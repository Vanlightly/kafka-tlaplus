--------------------------- MODULE kraft_kip_853_functions ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC,
        kraft_kip_853_types, network

ReceivableMessage(m, type, epoch_match) ==
    (* 
        The message is of the type, has a matching epoch
        and the destination server is not dead.
    *)
    /\ state[m.dest] # DeadNoState
    /\ m.type = type
    /\ \/ epoch_match = AnyEpoch
       \/ /\ epoch_match = EqualEpoch
          /\ m.epoch = current_epoch[m.dest]

VoterStates ==
    {Leader, Candidate, Follower, Unattached, Voted, Resigned}
    
ObserverStates ==
    (* Note:
       - a leader can be an observer when it has been removed 
         from the current configuration but has no yet committed
         the RemoveServerCommand.
       - an observer can be in the voted state as with
         reconfiguration, an observer may be in the configuration
         of another server and be required for any election to complete.
    *)  
    {Leader, Follower, Unattached, Voted}

EmptyMap == [x \in {} |-> Nil]

Quorum(ensemble) ==
    (* 
       The set of all quorums for a given ensemble of servers. 
       This just calculates simple majorities, but the only
       important property is that every quorum overlaps with every other.
    *)
    {i \in SUBSET(ensemble) : Cardinality(i) * 2 > Cardinality(ensemble)}

MajorityCount(ensemble) ==
    (Cardinality(ensemble) \div 2) + 1

LastEpoch(xlog) == 
    (*
        The epoch of the last entry in a log, or 0 if the log is empty.
    *)
    IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].epoch

FailPendingWrites(s) ==
    (* 
       When a node crashes, loses leadership etc, we reset the pending values to
       be acked and log those values as negatively acked (which includes client-s.de
       timeout in the case of a crash).
    *)
    /\ pending_ack' = [pending_ack EXCEPT ![s] = {}]
    /\ inv_neg_acked' = inv_neg_acked \union pending_ack[s]
    /\ UNCHANGED << inv_sent, inv_pos_acked >>

CompareEntries(offset1, epoch1, offset2, epoch2) ==
    (* 
        Compares two entries, with epoch taking precedence. 
        Offset only matters when both have the same epoch.
        - When entry1 > entry2 then 1
        - When entry1 = entry2 then 0
        - When entry1 < entry2 then 1
    *)
    CASE epoch1 > epoch2 -> 1
      [] epoch1 = epoch2 /\ offset1 > offset2 -> 1
      [] epoch1 = epoch2 /\ offset1 = offset2 -> 0
      [] OTHER -> -1

HighestCommonOffset(s, end_offset_for_epoch, epoch) ==
    (* 
        Finds the highest offset in the log which
        is <= to the supplied epoch and its end_offset_for_epoch
        (where the end_offset_for_epoch is inclusive here).
    *)
      \* CASE 1) the log is empty so no common offset
    CASE log[s] = <<>> -> 
            [offset |-> 0, epoch |-> 0]
      \* CASE 2) there is no lower entry in the log, so no common offset
      [] ~\E offset \in DOMAIN log[s] :
            CompareEntries(offset, log[s][offset].epoch, 
                           end_offset_for_epoch, epoch) <= 0 -> 
            [offset |-> 0, epoch |-> 0]
      \* CASE 3) there is a common entry, so choose the highest one 
      [] OTHER ->
            LET offset == CHOOSE offset \in DOMAIN log[s] :
                            /\ CompareEntries(offset, log[s][offset].epoch, 
                                              end_offset_for_epoch, epoch) <= 0
                            /\ ~\E offset2 \in DOMAIN log[s] :
                                /\ CompareEntries(offset2, log[s][offset2].epoch, 
                                                  end_offset_for_epoch, epoch) <= 0
                                /\ offset2 > offset
            IN [offset |-> offset, epoch |-> log[s][offset].epoch]  

TruncateLog(s, m) ==
    (* 
        Create a new log, truncated to the highest common entry
    *)
    LET highest_common_offset == HighestCommonOffset(
                                    s,
                                    m.diverging_end_offset - 1,
                                    m.diverging_epoch)
    IN IF highest_common_offset.offset = 0
       THEN <<>>
       ELSE [offset \in 1..highest_common_offset.offset |-> log[s][offset]]

EndOffsetForEpoch(s, last_fetched_epoch) ==
    (*
        The highest offset in the leader's log that has the same or lower epoch.
        Returns an inclusive offset.
    *)
      \* CASE 1) the log is empty so no end offset
    CASE log[s] = <<>> -> 
            [offset |-> 0, epoch |-> 0]
      \* CASE 2) there is no entry at or below the epoch in the log, so no end offset
      [] ~\E offset \in DOMAIN log[s] :
            log[s][offset].epoch <= last_fetched_epoch -> 
            [offset |-> 0, epoch |-> 0]
      \* CASE 3) there is an entry at or below the epoch in the log,
      \*         so return the highest one
      [] OTHER ->
            LET offset == CHOOSE offset \in DOMAIN log[s] :
                            /\ log[s][offset].epoch <= last_fetched_epoch
                            /\ ~\E offset2 \in DOMAIN log[s] :
                                /\ log[s][offset2].epoch <= last_fetched_epoch
                                /\ offset2 > offset
            IN [offset |-> offset, 
                epoch  |-> log[s][offset].epoch] 

ValidFetchPosition(s, m) ==
    (*
        TRUE if the fetch position of the follower is consistent
        with the log of the leader.
    *)
    \/ m.fetch_offset = 1
    \/ LET end == EndOffsetForEpoch(s, m.last_fetched_epoch)
       IN \* it's ok to ask for the next highest offset even if it doesn't yet exist
          /\ m.fetch_offset <= end.offset + 1
          /\ m.last_fetched_epoch = end.epoch

\* Transition helpers ------------------------------

HasConsistentLeader(s, leader_id, epoch) ==
    (*
        TRUE if server s and the peer have a consistent view on leadership,
        FALSE if not.
        TODO: 
            v3.2.0 Note: 3.2.0 has a bug which may not be possible
            in the implementation due to how connection are managed
            however it should be investigated: 
            A leader restarts and resigns on start-up but 
            immediately receives a vote response from before it was leader
            which results in this function returning TRUE as the response
            says this server is the leader but this leader does not
            think so. This has been modified to ignore this case when
            in the resigned state.

        Reconfiguration Note: a leader (s1) may have resigned after being 
        removed from the configuration and have sent a fetch request to
        a voter (s2) who still thinks that s1 is the leader. The fetch response
        would have leader_id=s1 and s1 would then (as of v3.2.0) enter 
        an illegal state (as it is inconsistent with its view that it is not leader).
        Therefore this formula has been modified for reconfiguration
        to ignore this case.
    *)
    IF leader_id = s
    THEN IF /\ current_epoch[s] = epoch 
            /\ \/ role[s] = Observer 
               \/ state[s] = Resigned
         THEN \* no conflict, the server has resigned after either restarting, 
              \* been removed as leader or become prospective of this same epoch.
              TRUE 
         ELSE \* if the peer thinks I am leader, and I am really leader
              \* then TRUE, else FALSE
              state[s] = Leader
    ELSE \* either the peer doesn't know there is a leader, or this
         \* node doesn't know a leader, or both agree on the same leader,
         \* or they have different epochs
         \/ epoch # current_epoch[s]
         \/ leader_id = Nil
         \/ leader[s] = Nil
         \/ leader[s] = leader_id

SetIllegalState ==
    (* This will be picked up by an invariant. *)
    [state        |-> IllegalState,
     epoch        |-> 0, 
     leader       |-> Nil,
     votes_recv   |-> {},
     voted_for    |-> Nil]

NoTransition(s) ==
    (* Creates a record with current values.*)
    [state        |-> state[s], 
     epoch        |-> current_epoch[s], 
     leader       |-> leader[s],
     votes_recv   |-> votes_recv[s],
     voted_for    |-> voted_for[s]]

TransitionToVoted(epoch, state0, vote_recipient) ==
    (* The server has voted for a peer in this epoch and transitioned
       to Voted. The if statement is not really necessary here, but 
       this check exists in the code. *)
    IF /\ state0.epoch = epoch
       /\ state0.state # Unattached
    THEN SetIllegalState
    ELSE [state        |-> Voted,
          epoch        |-> epoch,
          leader       |-> Nil,
          votes_recv   |-> {},
          voted_for    |-> vote_recipient]

TransitionToUnattached(s, epoch, curr_role) ==
    (* Either:
        - A voter has learned of a higher epoch but not
          yet learned who the new leader is. 
        - An observer has received a NotLeader fetch response .*)
    IF /\ curr_role = Voter
       /\ epoch <= current_epoch[s]
    THEN SetIllegalState
    ELSE [state        |-> Unattached, 
          epoch        |-> epoch, 
          leader       |-> Nil,
          votes_recv   |-> {},
          voted_for    |-> Nil]  \* forget prior vote
     
TransitionToFollower(s, leader_id, epoch) ==
    (* The follower has learned who the leader is in this epoch *)
    IF \/ leader_id = s
       \/ /\ current_epoch[s] = epoch
          /\ \/ state[s] = Follower
             \/ state[s] = Leader
       \/ epoch < current_epoch[s]
\*       \/ leader_id \notin config[s].members TODO later, check this works with reconfig
    THEN SetIllegalState
    ELSE [state        |-> Follower, 
          epoch        |-> epoch,
          leader       |-> leader_id,
          votes_recv   |-> {},
          \* only forget prior vote if epoch bumped
          voted_for    |-> IF epoch > current_epoch[s]
                           THEN Nil ELSE voted_for[s]]
          
TransitionToLeader(s) ==
    IF state[s] # Candidate
    THEN SetIllegalState
    ELSE [state        |-> Leader, 
          epoch        |-> current_epoch[s],
          leader       |-> s,
          votes_recv   |-> {},
          voted_for    |-> voted_for[s]] \* don't forget prior vote
     
TransitionToResigned(s) ==
    IF state[s] # Leader
    THEN SetIllegalState
    ELSE [state        |-> Resigned, 
          epoch        |-> current_epoch[s],
          leader       |-> Nil,
          votes_recv   |-> {},
          voted_for    |-> voted_for[s]]  \* don't forget prior vote
     
TransitionToCandidate(s) ==
    (* Transitioning to Candidate and sending vote requests occur
       in the same action, so (s) added to votes_recv *)
    [state        |-> Candidate, 
     epoch        |-> current_epoch[s] + 1,
     leader       |-> Nil,
     votes_recv   |-> {s}, \* votes for itself
     voted_for    |-> s]   \* votes for itself

MaybeTransition(s, leader_id, epoch) ==
    (*
        An event has occurred which may cause the server to
        transition to a new state. Returns a record with
        a new state, epoch and leader.  
    *)
    CASE ~HasConsistentLeader(s, leader_id, epoch) ->
            SetIllegalState
      [] epoch > current_epoch[s] ->
            \* the epoch of the server is stale, become a follower
            \* if the request contained the leader id, else become
            \* unattached
            IF leader_id = Nil
            THEN TransitionToUnattached(s, epoch, role[s])
            ELSE TransitionToFollower(s, leader_id, epoch)
      []  /\ leader_id # Nil  \* message contains a leader id 
          /\ leader[s] = Nil  \* this server doesn't know who the leader is
          /\ leader_id # s ->  \* leader id of the message is not this server
            \* the request contained a leader id and this server does not know
            \* of a leader, so become a follower of that leader
            TransitionToFollower(s, leader_id, epoch)  
      [] OTHER ->
            \* no changes
            NoTransition(s)

MaybeHandleCommonResponse(s, leader_id, epoch, errors) ==
    (*
        Common code between multiple response handlers:
        Note: 
        - The Handled field indicates whether action has already been
          taken. When TRUE, the parent action should do no more 
          processing of this response, only update the corresponding
          variables.
    *)
      \* CASE 1) stale epoch, do nothing ---------------
    CASE epoch < current_epoch[s] ->
                [state        |-> state[s],
                 epoch        |-> current_epoch[s],
                 leader       |-> leader[s],
                 votes_recv   |-> votes_recv[s],
                 voted_for    |-> voted_for[s],
                 handled      |-> TRUE,
                 error        |-> errors]
      \* CASE 2) higher epoch or an error ---------------
      [] \/ epoch > current_epoch[s] 
         \/ errors \in { FencedLeaderEpoch, NotLeader } ->
                MaybeTransition(s, leader_id, epoch) @@ 
                    [handled |-> TRUE, 
                     error   |-> errors]
      \* CASE 3) become a follower -----------------------
      [] /\ epoch = current_epoch[s]
         /\ leader_id # Nil
         /\ leader[s] = Nil 
         /\ leader_id # s ->
                TransitionToFollower(s, leader_id, epoch) @@
                     [handled |-> TRUE, 
                      error   |-> errors]
      \* CASE 4) no changes to state or leadership --------
      [] OTHER -> 
                [state        |-> state[s],
                 epoch        |-> current_epoch[s], 
                 leader       |-> leader[s],
                 votes_recv   |-> votes_recv[s],
                 voted_for    |-> voted_for[s],
                 handled      |-> FALSE,
                 error        |-> errors]

MaybeApplyChange(s, field, value) ==
    IF field[s] # value
    THEN field' = [field EXCEPT ![s] = value]
    ELSE UNCHANGED field 

ApplyState(s, new_state) ==
    /\ MaybeApplyChange(s, state, new_state.state)
    /\ MaybeApplyChange(s, leader, new_state.leader)
    /\ MaybeApplyChange(s, current_epoch, new_state.epoch)
    /\ MaybeApplyChange(s, votes_recv, new_state.votes_recv)
    /\ MaybeApplyChange(s, voted_for, new_state.voted_for)

UpdateFollowerEndOffsetMap(s, new_members) ==
    (* Updates the server's follower end offset map with the
       current set of members. Existing members keep their
       current values, new members get set to 0. *)
    flwr_end_offset' = [flwr_end_offset EXCEPT ![s] = 
                            [s1 \in new_members |->
                                IF s1 \in DOMAIN flwr_end_offset[s]
                                THEN flwr_end_offset[s][s1]
                                ELSE 0]]

ResetFollowerEndOffsetMap(s, members) ==
    (* Updates the server's follower end offset map with the
       current set of members, setting all values to 0. *)
    flwr_end_offset' = [flwr_end_offset EXCEPT ![s] = 
                            [s1 \in members |-> 0]]

IsConfigCommand(server_log, offset) ==
    (* The offset points to a reconfiguration command in the log. *)
    server_log[offset].command \in {InitClusterCommand,
                                    AddVoterCommand, 
                                    RemoveVoterCommand}

HasPendingConfigCommand(i) ==
    (* 
       A leader only allows one uncommitted reconfiguration
       command at a time.
    *)
    config[i].committed = FALSE

MostRecentReconfigEntry(server_log) ==
    (*
        Returns the most recent config command entry in the log.
    *)
    LET offset == CHOOSE offset \in DOMAIN server_log : 
                    /\ IsConfigCommand(server_log, offset)
                    /\ ~\E offset2 \in DOMAIN server_log : 
                        /\ IsConfigCommand(server_log, offset2)
                        /\ offset2 > offset
    IN [offset |-> offset, entry |-> server_log[offset]]

NoConfig == 
    [id        |-> 0,
     members   |-> {},
     committed |-> FALSE]
              
ConfigFor(offset, reconfig_entry, ci) ==
    (*
        Builds a configuration record from a 
        reconfiguration log entry.
    *)
    [id        |-> reconfig_entry.value.id,
     members   |-> reconfig_entry.value.members,
     committed |-> ci >= offset]

MaybeSwitchConfigurations(s, curr_config, new_state) ==
    (*
        If the last configuration in the log is not the same 
        as the current cached configuration then switch to the
        last configuration in the log. This may involve switching 
        to a new configuration or reverting to the prior 
        configuration (in the case of a log truncation).  
    *)
    /\ MaybeApplyChange(s, leader, new_state.leader)
    /\ MaybeApplyChange(s, current_epoch, new_state.epoch)
    /\ config' = [config EXCEPT ![s] = curr_config]
         \* CASE 1) The server (a voter )has been removed from
         \*         membership and become an observer.
    /\ CASE role[s] = Voter /\ s \notin curr_config.members ->
               /\ role'  = [role EXCEPT ![s] = Observer]
               /\ state' = [state EXCEPT ![s] = Follower]
               /\ MaybeApplyChange(s, votes_recv, {})
         \* CASE 2) The server (an observer) has been added 
         \*         to membership as a voter.
         [] role[s] = Observer /\ s \in curr_config.members ->
               /\ role'  = [role EXCEPT ![s] = Voter]
               /\ state' = [state EXCEPT ![s] = Follower]
               /\ MaybeApplyChange(s, votes_recv, {})
         \* CASE 3) The server role is unchanged.
         [] OTHER -> 
               /\ UNCHANGED role
               /\ MaybeApplyChange(s, state, new_state.state)
               /\ MaybeApplyChange(s, votes_recv, new_state.votes_recv)
    /\ UpdateFollowerEndOffsetMap(s, curr_config.members)

LeaderHasCommittedOffsetsInCurrentEpoch(s) ==
    (* 
        The server has log entries in its log of the
        current epoch, which are below the HWM (meaning
        they are committed). Must be TRUE for a leader to
        accept a reconfiguration command.
    *)
    \E offset \in DOMAIN log[s] :
        /\ log[s][offset].epoch = current_epoch[s]
        /\ hwm[s] >= offset

        
================================================