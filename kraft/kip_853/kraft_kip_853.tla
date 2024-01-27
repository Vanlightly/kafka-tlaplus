--------------------------------- MODULE kraft_kip_853 ---------------------------------
(*NOTES
Author: Jack Vanlightly

-----------------------------------------------
Kafka KRaft TLA+ specification with KIP-853
-----------------------------------------------

This specification description assumes you already understand Raft
and does not attempt to describe the basic mechanics of Raft. The
major difference between Raft and KRaft is that KRaft is a pull 
variant of Raft, whereas the original is push based.

This is a specification that is a mix of reverse engineering the
existing Kafka KRaft implementation (as of v3.2.0) plus the addition 
of reconfiguration and composite server identity which is included in
KIP-853.

Because this spec was based on reverse engineering the code in 3.2,
a review is needed to make sure this is still faithful to the 
implementation.

See the readme for more discussion.
*)

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC,
        kraft_kip_853_types, 
        kraft_kip_853_functions,
        kraft_kip_853_properties,
        network

\* ================================================
\* Actions
\* ================================================

\* Each action is split into two parts:
\* - enabling conditions that make the action enabled or not.
\* - state mutations - changes to the variables.

(* 
    ACTION: RestartWithState -------------------------------------
    Server (s) restarts from stable storage.
    KRaft durably stores: role, state, current_epoch, leader, 
    voted_for and log.
*)
RestartWithState(s) ==
    \* enabling conditions (including state space contraints)
    /\ aux_ctrs.restart_ctr < MaxRestarts
    /\ s \in StartedServers
    /\ state[s] # DeadNoState
    \* state mutations
    /\ state' = [state EXCEPT ![s] = 
                    CASE /\ state[s] = Leader 
                         /\ role[s] = Voter -> Resigned
                      [] /\ state[s] = Leader 
                         /\ role[s] = Observer -> Unattached
                      [] OTHER -> @]
    /\ leader' = [leader EXCEPT ![s] = IF state[s] = Leader
                                       THEN Nil ELSE @]                                         
    /\ votes_granted' = [votes_granted EXCEPT ![s] = {}]
    /\ flwr_end_offset' = [flwr_end_offset EXCEPT ![s] = 
                            [s1 \in DOMAIN flwr_end_offset[s] |-> 0]]
    /\ hwm' = [hwm EXCEPT ![s] = 0]
    /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
    /\ aux_ctrs' = [aux_ctrs EXCEPT !.restart_ctr = @ + 1]
    /\ FailPendingWrites(s)
    /\ UNCHANGED <<server_ids, NetworkVars, config, current_epoch, role, 
                   voted_for, log, aux_disk_id_gen>>

(* 
    ACTION: CrashLoseState -------------------------------------
    Server (s) is a member of the cluster and crashes with 
    all state lost.
    
    To avoid causing data loss due to a majority of servers
    crashing and losing data, this action is only enabled
    if losing this server does not cause the Raft cluster
    to become non-functional.
*)

ClusterStuck(crash_server) ==
    (* 
       Detects whether losing this server will result in a cluster
       unable to make further progress due to only a minority being
       functional.
    *)
    ~\E s \in StartedServers :
        /\ role[s] = Voter
        /\ s # crash_server
        /\ Quantify(config[s].members, LAMBDA peer :
            /\ peer # crash_server          \* not crash server
            /\ role[peer] = Voter           \* is a functioning voter
            /\ s \in config[peer].members   \* agrees that s is a member
            /\ Connected(s, peer))          \* the two are connected
                > Cardinality(config[s].members) \div 2

CrashLoseState(s) ==
    \* enabling conditions
    /\ aux_ctrs.crash_ctr < MaxCrashes
    /\ s \in StartedServers
    /\ role[s] = Voter
    /\ ~ClusterStuck(s)
    \* state mutations
    /\ state' = [state EXCEPT ![s] = DeadNoState]
    /\ config' = [config EXCEPT ![s] = NoConfig]
    /\ role' = [role EXCEPT ![s] = Nil]    
    /\ current_epoch' = [current_epoch EXCEPT ![s] = 0]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ voted_for' = [voted_for EXCEPT ![s] = Nil]
    /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil] 
    /\ votes_granted' = [votes_granted EXCEPT ![s] = {}]
    /\ flwr_end_offset' = [flwr_end_offset EXCEPT ![s] = EmptyMap]
    /\ log' = [log EXCEPT ![s] = <<>>]
    /\ hwm' = [hwm EXCEPT ![s] = 0]
    /\ FailPendingWrites(s)
    /\ aux_ctrs' = [aux_ctrs EXCEPT !.crash_ctr = @ + 1]
    /\ UNCHANGED <<NetworkVars, aux_disk_id_gen, server_ids, aux_disk_id_gen>>

(*
    ACTION: RequestVote -----------------------------------------------
    Server (s) is a voter and not the leader, and experiences
    an election times out. It sends a RequestVote request to 
    all peers in its configuration but not itself.
    
    This action combines an election timeout with a RequestVote
    broadcast. This means we allow the server to request a vote
    in the Voted state which is not strictly legal. However,
    this specification compresses the election timeout (which
    transitions a Voted server into a Candidate) and the new election
    into this single action).
*)
RequestVote(s) ==
    \* enabling conditions (including state space contraints)
    /\ aux_ctrs.election_ctr < MaxElections 
    /\ s \in StartedServers
    /\ role[s] = Voter
    /\ state[s] \in {Follower, Candidate, Unattached, Voted}
    /\ s \in config[s].members
    \* state mutations
    /\ state' = [state EXCEPT ![s] = Candidate]
    /\ current_epoch' = [current_epoch EXCEPT ![s] = current_epoch[s] + 1]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ voted_for' = [voted_for EXCEPT ![s] = s] \* votes for itself
    /\ votes_granted' = [votes_granted EXCEPT ![s] = {s}] \* votes for itself
    /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
    /\ aux_ctrs' = [aux_ctrs EXCEPT !.election_ctr = @ + 1]
    /\ SendAllOnce(
            {[type            |-> RequestVoteRequest,
              epoch           |-> current_epoch[s] + 1,
              last_log_epoch  |-> LastEpoch(log[s]),
              last_log_offset |-> Len(log[s]),
              source          |-> s,
              dest            |-> s1] : s1 \in config[s].members \ {s}})
    /\ UNCHANGED <<server_ids, config, role, pending_ack, leaderVars, logVars,
                   invVars, aux_disk_id_gen>>

(* 
    ACTION: HandleRequestVoteRequest ------------------------------
    Server (s0) receives a RequestVote message. 
    While this server may be an Observer and therefore believe 
    it is not a member of a configuration, it may in fact be 
    so (but be lagging) and may be required to process the message
    in order for an election to complete. In other words, if
    an observer ignores RequestVote messages it may cause a cluster
    to get stuck.

    Server (s) will vote for its peer if all the following are true:
    1) epoch of (peer) >= epoch of (s)
    2) the last entry of (s) is <= to the last entry of (peer)
    3) (s) has not already voted for a different server
*)
HandleRequestVoteRequest(s) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, RequestVoteRequest, AnyEpoch)
        /\ s = m.dest
        /\ LET peer     == m.source
               error    == IF m.epoch < current_epoch[s]
                           THEN FencedLeaderEpoch
                           ELSE Nil
               state0   == IF m.epoch > current_epoch[s]
                           THEN TransitionToUnattached(m.epoch)
                           ELSE NoTransition(s)
               log_ok == CompareEntries(m.last_log_offset,
                                        m.last_log_epoch,
                                        Len(log[s]),
                                        LastEpoch(log[s])) >= 0
               grant == /\ \/ state0.state = Unattached
                           \/ /\ state0.state = Voted
                              /\ voted_for[s] = peer
                        /\ log_ok
               final_state == IF grant /\ state0.state = Unattached
                              THEN TransitionToVoted(s, m.epoch, state0)
                              ELSE state0                         
            IN  \* state mutations
                /\ IF error = Nil
                  THEN
                       /\ state' = [state EXCEPT ![s] = final_state.state]
                       /\ current_epoch' = [current_epoch EXCEPT ![s] = final_state.epoch]
                       /\ leader' = [leader EXCEPT ![s] = final_state.leader]
                       /\ \/ /\ grant
                             /\ voted_for' = [voted_for EXCEPT ![s] = peer]
                          \/ /\ ~grant
                             /\ UNCHANGED voted_for
                       /\ IF state # state'
                          THEN /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
                               /\ FailPendingWrites(s)
                          ELSE UNCHANGED << pending_fetch, pending_ack, invVars >>
                       /\ Reply(m, [type         |-> RequestVoteResponse,
                                    epoch        |-> m.epoch,
                                    leader       |-> final_state.leader,
                                    vote_granted |-> grant,
                                    error        |-> Nil,
                                    source       |-> s,
                                    dest         |-> peer])
                  ELSE /\ Reply(m, [type         |-> RequestVoteResponse,
                                    epoch        |-> current_epoch[s],
                                    leader       |-> leader[s],
                                    vote_granted |-> FALSE,
                                    error        |-> error,
                                    source       |-> s,
                                    dest         |-> peer])
                       /\ UNCHANGED << current_epoch, state, leader, voted_for,
                                       pending_fetch, pending_ack, invVars>>
               /\ UNCHANGED <<server_ids, role, config, candidateVars, 
                              leaderVars, logVars, auxVars>>

(* 
    ACTION: HandleRequestVoteResponse --------------------------------
    Server (s) receives a RequestVote reponse.
    The server would normally be a candidate, but it could
    have already transitioned to a different state or epoch.
    If the response is stale it will be ignored.
*)
HandleRequestVoteResponse(s) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, RequestVoteResponse, AnyEpoch)
        /\ s = m.dest
        /\ role[s] = Voter \* new check because roles can change with reconfigurations
        \* state mutations
        /\ LET peer == m.source
               new_state == MaybeHandleCommonResponse(s, m.leader, m.epoch, m.error)
           IN
              /\ IF new_state.handled = TRUE
                 THEN /\ state' = [state EXCEPT ![s] = new_state.state]
                      /\ leader' = [leader EXCEPT ![s] = new_state.leader]
                      /\ current_epoch' = [current_epoch EXCEPT ![s] = new_state.epoch]
                      /\ UNCHANGED <<votes_granted>>
                 ELSE
                      /\ state[s] = Candidate
                      /\ \/ /\ m.vote_granted
                            /\ votes_granted' = [votes_granted EXCEPT ![s] =
                                                      votes_granted[s] \union {peer}]
                         \/ /\ ~m.vote_granted
                            /\ UNCHANGED <<votes_granted>>
                      /\ UNCHANGED <<state, leader, current_epoch>>
              /\ Discard(m)
              /\ UNCHANGED <<server_ids, config, role, voted_for, pending_fetch, 
                             pending_ack, leaderVars, logVars, invVars, auxVars>>               

(*
    ACTION: BecomeLeader -------------------------------------------
    Server (s) is a voter in the Candidate state. It has
    received enough votes to win the election and transitions
    to leader. It sends all peers in its current configuration
    a BeginQuorumRequest to notify them of its leadership.
*)
BecomeLeader(s) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ state[s] = Candidate
    /\ votes_granted[s] \in Quorum(config[s].members)
    \* state mutations
    /\ state' = [state EXCEPT ![s] = Leader]
    /\ leader' = [leader EXCEPT ![s] = s]
    /\ flwr_end_offset' = [flwr_end_offset EXCEPT ![s] = 
                            [peer \in config[s].members  |-> 0]]
    /\ SendAllOnce(
            {[type    |-> BeginQuorumRequest,
              epoch   |-> current_epoch[s],
              source  |-> s,
              dest    |-> peer] : peer \in config[s].members \ {s}})
    /\ UNCHANGED <<server_ids, config, role, current_epoch, voted_for,
                   pending_fetch, pending_ack, candidateVars, logVars,
                   invVars, auxVars>>

(* 
    ACTION: AcceptBeginQuorumRequest -------------------------------------------
    Server (s), which is a voter, receives a BeginQuorumRequest 
    and transitions to a follower unless the message is stale.
    
    Note that rejecting a BeginQuorumRequest is not modeled but
    it should happen in the following cases:
    - Observers must ignore or reject this request for safety reasons. 
      An observer can only transition to a voter via receiving a reconfig 
      command in its log.
*)
AcceptBeginQuorumRequest(s) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, BeginQuorumRequest, AnyEpoch)
        /\ s = m.dest
        /\ LET peer     == m.source
               error    == IF m.epoch < current_epoch[s]
                           THEN FencedLeaderEpoch
                           ELSE Nil
               new_state == MaybeTransition(s, m.source, m.epoch)
           IN /\ error = Nil
              /\ role[s] = Voter \* new check because roles can change with reconfigurations
              \* state mutations
              /\ state' = [state EXCEPT ![s] = new_state.state]
              /\ leader' = [leader EXCEPT ![s] = new_state.leader]
              /\ current_epoch' = [current_epoch EXCEPT ![s] = new_state.epoch]
              /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
              /\ FailPendingWrites(s)
              /\ Discard(m)
        /\ UNCHANGED <<server_ids, config, role, voted_for, 
                       logVars, candidateVars, leaderVars, auxVars>>

(* 
    ACTION: ClientRequest ----------------------------------
    A client sends a write request to server (s) which is
    a leader. 
    
    TODO: Discuss merits of allowing a leader that is an
          observer to accept writes. Doing so will be better
          for availability and still be safe. A leader can 
          be an observer during a reconfiguration.
*)
ClientRequest(s) ==
    \* enabling conditions
    \E v \in Value : 
        /\ s \in StartedServers
        /\ state[s] = Leader
        /\ v \notin inv_sent \* prevent submitting the same value repeatedly
        /\ aux_ctrs.value_ctr[current_epoch[s]] < MaxValuesPerEpoch
        \* state mutations
        /\ LET entry == [command |-> AppendCommand,
                         epoch   |-> current_epoch[s],
                         value   |-> v]
               new_log == Append(log[s], entry)
           IN  /\ log' = [log EXCEPT ![s] = new_log]
               /\ pending_ack' = [pending_ack EXCEPT ![s] = @ \union {v}]
               /\ inv_sent' = inv_sent \union {v}
               /\ aux_ctrs' = [aux_ctrs EXCEPT !.value_ctr = 
                                [@ EXCEPT ![current_epoch[s]] = @ + 1]]
        /\ UNCHANGED <<server_ids, config, current_epoch, role, state, voted_for, 
                       leader, pending_fetch, NetworkVars, candidateVars,
                       leaderVars, hwm, inv_pos_acked, inv_neg_acked, aux_disk_id_gen>>
                       
(* 
    ACTION: SendFetchRequest ----------------------------------------
    Server (s) is a Voter or Observer in the Follower state,
    and sends the server it believes is the leader a fetch request.
    
    Note that this server may have switched to a new configuration
    where the leader is no longer a member, but this follower
    will continue to send fetches to this leader in order for
    that the leader to be able to commit the reconfig command.
    Once the leader has committed the reconfig command it will resign
    and reject further fetch requests.
*)
SendFetchRequest(s) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ \E peer \in StartedServers : 
        /\ s # peer
        /\ \* either the follower (voter or observer) knows who the 
           \* leader is and can send a fetch request to the leader
           \/ /\ leader[s] = peer
              /\ state[s] = Follower
           \* or we're an observer follower that doesn't know who the
           \* leader is and picks a random voter to fetch from, knowing
           \* that if it isn't the leader, it will include the leader id
           \* in its response if it knows.
           \/ /\ role[s] = Observer
              /\ state[s] = Unattached
              /\ peer \in config[s].members 
        /\ pending_fetch[s] = Nil
        \* state mutations
        /\ LET last_log_offset == Len(log[s])
               last_log_epoch  == IF last_log_offset > 0 
                                  THEN log[s][last_log_offset].epoch
                                  ELSE 0
               fetch_msg    == [type               |-> FetchRequest,
                                epoch              |-> current_epoch[s],
                                fetch_offset       |-> last_log_offset + 1,
                                last_fetched_epoch |-> last_log_epoch,
                                observer           |-> role[s] = Observer,
                                source             |-> s,
                                dest               |-> peer]
           IN /\ pending_fetch' = [pending_fetch EXCEPT ![s] = fetch_msg]
              /\ Send(fetch_msg)
        /\ UNCHANGED <<server_ids, config, role, current_epoch, state, 
                       voted_for, leader, pending_ack, candidateVars, leaderVars, 
                       logVars, invVars, auxVars>>

(* NOTE: Fetch requests --------------------------------
    Note 1:
    The server that receives a fetch request
    can be the leader and an observer. This can happen
    when the leader has switched to being an observer
    because it is an acting leader that is continuing until
    it can commit a RemoveServerCommand which removes itself from the
    configuration.

    Note 2:
    We allow fetches from voters that are not in
    the current configuration because they may not have
    reached the reconfiguration command yet. Once they do
    they will switch to being an observer. Also this follower
    may be required in order to commit the command, so if
    the leader rejects fetches from this follower then it
    would block further progress completely - a stuck cluster.
*)

(*
    ACTION: RejectFetchRequest -------------------
    Server (s) receives a fetch request that is invalid.
    A server rejects a FetchRequest due to any of the
    following:
    (1) (s) is not a leader
    (2) the message epoch is lower than the server epoch
    (3) the message epoch is higher than the server epoch
*)
RejectFetchRequest(s, peer) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, FetchRequest, AnyEpoch)
        /\ s = m.dest
        /\ peer = m.source
        /\ LET error == CASE state[s] # Leader -> NotLeader
                          [] m.epoch < current_epoch[s] -> FencedLeaderEpoch
                          [] m.epoch > current_epoch[s] -> UnknownLeader
                          [] OTHER -> Nil
           IN  /\ error # Nil
               \* state mutations
               /\ Reply(m, [type        |-> FetchResponse,
                            result      |-> NotOk,
                            error       |-> error,
                            leader      |-> leader[s],
                            epoch       |-> current_epoch[s],
                            hwm         |-> hwm[s],
                            source      |-> s,
                            dest        |-> peer,
                            correlation |-> m])
               /\ UNCHANGED <<server_ids, candidateVars, leaderVars, serverVars, 
                              logVars, invVars, auxVars>>

(* 
    ACTION: DivergingFetchRequest -------------------
    Server (s) is a leader that receives a FetchRequest with
    a fetch offset and last fetched epoch that is inconsistent 
    with the server's log. It responds with the highest offset
    that matches the epoch of the follower fetch position so 
    the follower can truncate its log and start fetching from
    a consistent offset.
*)
DivergingFetchRequest(s, peer) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, FetchRequest, EqualEpoch)
        /\ s = m.dest
        /\ peer = m.source
        /\ LET valid_position     == ValidFetchPosition(s, m)
               valid_offset_epoch == EndOffsetForEpoch(s, m.last_fetched_epoch)
           IN  /\ state[s] = Leader
               /\ ~valid_position 
               \* state mutations
               /\ Reply(m, [type                 |-> FetchResponse,
                            epoch                |-> current_epoch[s],
                            result               |-> Diverging,
                            error                |-> Nil,
                            diverging_epoch      |-> valid_offset_epoch.epoch,
                            diverging_end_offset |-> valid_offset_epoch.offset,
                            leader               |-> leader[s],
                            hwm                  |-> hwm[s],
                            source               |-> s,
                            dest                 |-> peer,
                            correlation          |-> m])
               /\ UNCHANGED <<server_ids, candidateVars, leaderVars, serverVars, 
                              logVars, invVars, auxVars>>

(* 
    ACTION: AcceptFetchRequestFromVoter ------------------
    Server (s) is a leader that receives a FetchRequest from
    a Voter with a fetch offset and last fetched epoch and 
    responds with an entry if there is one or an empty 
    response if not.

    The leader updates the end offset of the fetching peer
    and advances the high watermark if it can.
    It can only advance the high watermark to an entry of the
    current epoch.
*)

IsRemovedFromCluster(i, new_hwm) ==
    (* 
        TRUE when this fetch request causes the HWM to advance
        such that a reconfiguration command gets committed and
        this leader is no longer a member in this new configuration.
    *)
    \E offset \in DOMAIN log[i] :
        /\ offset > hwm[i]
        /\ offset <= new_hwm
        /\ log[i][offset].command = RemoveServerCommand
        /\ i \notin log[i][offset].value.members

NewHighwaterMark(s, new_end_offset) ==
    (*
        Returns a HWM that may or may not have changed.
    *)
    LET \* The set of servers that agree up through the given offset.
        \* If the leader is not in the current member set due
        \* to an in-progress reconfiguration then it does not 
        \* include itself in the quorum
        Agree(offset, members) == 
            IF s \in members
            THEN {s} \union {k \in members : new_end_offset[k] >= offset }
            ELSE {k \in members : new_end_offset[k] >= offset }
        \* The maximum offsets for which a quorum agrees
        agree_offsets  == {offset \in 1..Len(log[s]) : 
                            Agree(offset, config[s].members) \in Quorum(config[s].members)}
    IN 
        IF /\ agree_offsets # {}
           /\ log[s][Max(agree_offsets)].epoch = current_epoch[s]
        THEN Max(agree_offsets)
        ELSE hwm[s]

AcceptFetchRequestFromVoter(s, peer) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, FetchRequest, EqualEpoch)
        /\ s = m.dest
        /\ peer = m.source
        /\ LET valid_position == ValidFetchPosition(s, m)
               entries        == IF m.fetch_offset > Len(log[s])
                                 THEN <<>>
                                 ELSE <<log[s][m.fetch_offset]>>
           IN 
              /\ state[s] = Leader
              /\ peer \in config[s].members
              /\ m.observer = FALSE
              /\ valid_position
              \* state mutations
              /\ LET new_end_offset == [flwr_end_offset[s] EXCEPT ![peer] = m.fetch_offset-1]
                     new_hwm        == NewHighwaterMark(s, new_end_offset)
                     leaves         == IsRemovedFromCluster(s, new_hwm)
                     config_entry   == MostRecentReconfigEntry(log[s])
                     committed_values == { log[s][ind].value : ind \in hwm[s]+1..new_hwm }
                     values_to_ack    == pending_ack[s] \intersect committed_values
                 IN
                    /\ IF new_hwm > hwm[s]
                       THEN /\ config' = [config EXCEPT ![s] = 
                                            \* may be update our cached config as committed
                                            ConfigFor(config_entry.offset, 
                                                      config_entry.entry, 
                                                      new_hwm)]
                            /\ inv_pos_acked' = inv_pos_acked \union values_to_ack
                            /\ pending_ack' = [pending_ack EXCEPT ![s] = @ \ values_to_ack]
                            /\ IF leaves
                               THEN \* the server resigns and becomes an unattached observer
                                    /\ role' = [role EXCEPT ![s] = Observer]
                                    /\ state' = [state EXCEPT ![s] = Unattached]
                                    /\ leader' = [leader EXCEPT ![s] = Nil]
                                    /\ votes_granted' = [votes_granted EXCEPT ![s] = {}]
                                    /\ flwr_end_offset' = [flwr_end_offset EXCEPT ![s] = EmptyMap]
                                    /\ hwm' = [hwm EXCEPT ![s] = 0]
                               ELSE /\ flwr_end_offset' = [flwr_end_offset EXCEPT ![s] = new_end_offset]
                                    /\ hwm' = [hwm EXCEPT ![s] = new_hwm]
                                    /\ UNCHANGED <<role, state, leader, votes_granted>>
                       ELSE /\ flwr_end_offset' = [flwr_end_offset EXCEPT ![s] = new_end_offset]
                            /\ UNCHANGED <<role, config, state, leader, votes_granted, 
                                           pending_ack, hwm, invVars>>
                    /\ Reply(m, [type        |-> FetchResponse,
                                 epoch       |-> current_epoch[s],
                                 leader      |-> IF leaves THEN Nil ELSE leader[s],
                                 result      |-> Ok,
                                 error       |-> Nil,
                                 entries     |-> entries,
                                 hwm         |-> Min({new_hwm, m.fetch_offset}),
                                 source      |-> s,
                                 dest        |-> peer,
                                 correlation |-> m])                    
                    /\ UNCHANGED <<server_ids, current_epoch, log, voted_for, pending_fetch, 
                                   inv_sent, inv_neg_acked, aux_ctrs, aux_disk_id_gen>>

(* 
    ACTION: AcceptFetchRequestFromObserver ------------------
    Server (s) is a leader that receives a FetchRequest from
    an Observer with a fetch offset and last fetched epoch that
    is consistent with its log.
    The serverupdates no local state but simply responds
    with entries if there are any to return.
*)
AcceptFetchRequestFromObserver(s, peer) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, FetchRequest, EqualEpoch)
        /\ s = m.dest
        /\ peer = m.source
        /\ LET valid_position == ValidFetchPosition(s, m)
               entries        == IF m.fetch_offset > Len(log[s])
                                 THEN <<>>
                                 ELSE <<log[s][m.fetch_offset]>>
           IN 
              /\ state[s] = Leader
              /\ m.observer = TRUE
              /\ valid_position
              \* state mutations
              /\ Reply(m, [type        |-> FetchResponse,
                           epoch       |-> current_epoch[s],
                           leader      |-> leader[s],
                           result      |-> Ok,
                           error       |-> Nil,
                           entries     |-> entries,
                           hwm         |-> Min({m.fetch_offset, hwm[s]}),
                           source      |-> s,
                           dest        |-> peer,
                           correlation |-> m])
              /\ UNCHANGED <<server_ids, serverVars, candidateVars, leaderVars,
                             logVars, invVars, auxVars>>
       
(* 
    ACTION: HandleSuccessFetchResponse ---------------------
    A server receives a successful FetchResponse, appends
    any entries to its log and updates its high watermark.

    The response may include a reconfiguration command
    and if so, the server immediately switches to the new
    configuration.
*)
HandleSuccessFetchResponse(s) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ s = m.dest
        /\ LET new_state    == MaybeHandleCommonResponse(s, m.leader, m.epoch, m.error)
               new_log      == IF Len(m.entries) > 0
                               THEN [log EXCEPT ![s] = Append(@, m.entries[1])]
                               ELSE log 
               config_entry == MostRecentReconfigEntry(new_log[s])
               curr_config  == ConfigFor(config_entry.offset,
                                         config_entry.entry,
                                         m.hwm)
           IN /\ m.result = Ok
              /\ new_state.handled = FALSE
              /\ pending_fetch[s] = m.correlation
              \* state mutations
              /\ MaybeSwitchConfigurations(s, curr_config, new_state)                    
              /\ hwm' = [hwm  EXCEPT ![s] = m.hwm]
              /\ log' = new_log
              /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
              /\ Discard(m)
              /\ UNCHANGED <<server_ids, current_epoch, voted_for, pending_ack,
                             candidateVars, invVars, auxVars>>

(*
    ACTION: HandleDivergingFetchResponse ------------------------
    Server (s) is a Follower that receives a Fetch response 
    that indicates that the fetch position is inconsistent. 
    The response includes the highest offset of the last common
    epoch the leader and follower share, so the follower truncates
    its log to the highest entry it has at or below that
    point which will be the highest common entry that the 
    leader and follower share.

    Log truncation could remove a reconfiguration command, so
    this may cause the server to switch to a prior configuration.

    After this it can send another FetchRequest to the leader
    from a valid fetch position.
*)
HandleDivergingFetchResponse(s) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ s = m.dest
        /\ LET new_state    == MaybeHandleCommonResponse(s, m.leader, m.epoch, m.error)
               new_log      == [log EXCEPT ![s] = TruncateLog(s, m)] 
               config_entry == MostRecentReconfigEntry(new_log[s])
               curr_config  == ConfigFor(config_entry.offset,
                                         config_entry.entry,
                                         m.hwm)
           IN 
              /\ m.result = Diverging
              /\ new_state.handled = FALSE
              /\ pending_fetch[s] = m.correlation
              \* state mutations
              \* The server could have truncated the reconfig command
              \* of the current configuration, causing the server
              \* to revert to the prior configuration.
              /\ MaybeSwitchConfigurations(s, curr_config, new_state)
              \* update log
              /\ log' = new_log
              /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil] 
              /\ Discard(m)
        /\ UNCHANGED <<server_ids, current_epoch, voted_for, pending_ack,
                       candidateVars, hwm, invVars, auxVars>>
                       
(* ACTION: HandleNonSuccessFetchResponse ------------------------
    Server (s) receives a FetchResponse from that satisfies one 
    of the following conditions:
    (1) It is an error response
    (2) (s) has entered an illegal state
    (3) (s) transitions to a new state where no further processing
        of this message should happen. Such as transitioning to 
        follower state in a new epoch.
    
    If this is an observer and the error was NotLeader and the id of
    the leader was included in the response, the observer can now send
    fetches to that leader.
*)
HandleNonSuccessFetchResponse(s) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ s = m.dest
        /\ LET new_state == MaybeHandleCommonResponse(s, m.leader, m.epoch, m.error)
           IN
              /\ new_state.handled = TRUE
              /\ pending_fetch[s] = m.correlation
              \* state mutations
              /\ state' = [state EXCEPT ![s] = new_state.state]
              /\ leader' = [leader EXCEPT ![s] = new_state.leader]
              \* if the response is UnknownMember then it possible
              \* the current configuration got truncated after a leader election
              \* and so this server should switch to being an Observer
              \* If it gets made a member again it will discover that in its log.
              /\ IF m.error = UnknownMember
                 THEN role' = [role EXCEPT ![s] = Observer]
                 ELSE UNCHANGED <<role>>
              /\ current_epoch' = [current_epoch EXCEPT ![s] = new_state.epoch]
              /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
              /\ Discard(m)
        /\ UNCHANGED <<server_ids, config, voted_for, pending_ack, candidateVars,
                       leaderVars, logVars, invVars, auxVars>>                       

\* ----------------------------------------------
\* RECONFIGURATION ------------------------------

(* 
    ACTION: StartNewServer ----------------------------
    A server starts with a blank disk and generates
    a composite identity based on host and a random id
    called disk_id and in the observer role.

    The server chooses another server in the cluster and
    sends a fetch request to it. The server could get 
    lucky (by happening to choose a server that is leader),
    or it might send its first fetch to a follower. In the
    latter case, it will receive an error reponse that
    includes the leader id so that subsequent fetches can
    be sent to the leader.

    Note this spec takes a shortcut by magically causing
    the new server to send its first FetchRequest to a
    server that identifies itself as a leader. This reduces
    the state space, but does not affect safety. 
*)
StartNewServer ==
    \* enabling conditions
    /\ Cardinality(StartedServers) < MaxSpawnedServers
    /\ \E host \in Hosts, anyLeader \in StartedServers :
        LET new_server == Max(StartedServers) + 1
            disk_id    == aux_disk_id_gen + 1
            identity   == [host |-> host, disk_id |-> disk_id]
        IN /\ state[anyLeader] = Leader \* this is a shortcut, but a safe one.
           \* state mutations
           /\ aux_disk_id_gen' = aux_disk_id_gen + 1
           /\ LET fetch_msg == [type               |-> FetchRequest,
                                epoch              |-> 0,
                                fetch_offset       |-> 0,
                                last_fetched_epoch |-> 0,
                                observer           |-> TRUE,
                                source             |-> new_server,
                                dest               |-> anyLeader]
              IN \* Add a new server to the variables
                 /\ server_ids' = server_ids @@ (new_server :> identity)
                 /\ config' = config @@ (new_server :> NoConfig)
                 /\ role' = role @@ (new_server :> Observer)    
                 /\ state' = state @@ (new_server :> Unattached)
                 /\ current_epoch' = current_epoch @@ (new_server :> 0)
                 /\ leader' = leader @@ (new_server :> Nil)
                 /\ voted_for' = voted_for @@ (new_server :> Nil)
                 /\ pending_fetch' = pending_fetch @@ (new_server :> fetch_msg) 
                 /\ pending_ack' = pending_ack @@ (new_server :> {})
                 /\ votes_granted' = votes_granted @@ (new_server :> {})
                 /\ flwr_end_offset' = flwr_end_offset @@ (new_server :> EmptyMap)
                 /\ log' = log @@ (new_server :> <<>>)
                 /\ hwm' = hwm @@ (new_server :> 0)
                 /\ Send(fetch_msg)
    /\ UNCHANGED << invVars, aux_ctrs >>

(*
    ACTION: SendJoinRequest -----------------------------
    Server (s) is an Observer in the Follower state. A Join
    request (the sender is not important) is sent to the
    leader, to add (s) to the cluster in a new configuration. 
    
    Ideally, the observer will be caught up to the leader
    when the Join request is sent, but this is not modelled
    in this spec.
*)
SendJoinRequest(s) ==
    \* enabling conditions
    /\ aux_ctrs.add_reconfig_ctr < MaxAddReconfigs
    /\ s \in StartedServers
    /\ \E peer \in StartedServers :
        /\ s # peer
        /\ role[s] = Observer
        /\ s \notin config[s].members
        /\ leader[s] = peer
        \* state mutations
        /\ Send([type      |-> JoinRequest,
                 epoch     |-> current_epoch[s],
                 dest      |-> peer,
                 source    |-> s])
        /\ aux_ctrs' = [aux_ctrs EXCEPT !.add_reconfig_ctr = @ + 1]
        /\ UNCHANGED <<server_ids, serverVars, candidateVars, leaderVars, 
                       logVars, invVars, aux_disk_id_gen>>
              
(*
    ACTION: AcceptJoinRequest ----------------------------------
    Server (s) is a Leader and a Voter (a leader observer by 
    definition already has a RemoveServerCommand in-progress).
    
    Leader (s) accepts a valid JoinRequest and appends an 
    AddServerCommand with the new server identity to its log 
    and assumes the new configuration immediately.

    To be valid a JoinRequest the following conditions are required:
    (1) The request is received by a leader.
    (2) The joining node cannot already be a member.
    (3) The leader has no in-progress reconfiguration.
    (4) The leader must have committed an offset in the current epoch.
*)
JoinCheck(s, m) ==
    (* Enforces the above rules. *)
    CASE state[s] # Leader -> NotLeader
      [] m.source \in config[s].members -> AlreadyMember
      [] HasPendingConfigCommand(s) -> ReconfigInProgress
      [] ~LeaderHasCommittedOffsetsInCurrentEpoch(s) -> LeaderNotReady
      [] OTHER -> Ok

AcceptJoinRequest(s) ==
    \* enabling conditions
    /\ \E m \in Messages :
        /\ ReceivableMessage(m, JoinRequest, AnyEpoch)
        /\ s = m.dest
        /\ LET peer  == m.source
               check == JoinCheck(s, m)
           IN
              /\ Cardinality(config[s].members) < MaxClusterSize
              /\ check = Ok
              \* state mutations
              /\ LET entry   == [command |-> AddServerCommand,
                                 epoch   |-> current_epoch[s],
                                 value   |-> [id      |-> config[s].id + 1,
                                              new     |-> peer,
                                              members |-> config[s].members \union {peer}]]
                     new_log == Append(log[s], entry)
                 IN  /\ log' = [log EXCEPT ![s] = new_log]
                     /\ config' = [config EXCEPT ![s] = 
                                        ConfigFor(Len(new_log),
                                                  entry, 
                                                  hwm[s])]
                     \* start tracking the end offset of this new member
                     /\ flwr_end_offset' = [flwr_end_offset EXCEPT ![s] = @ @@ (peer :> 0)]
                     /\ Reply(m, [type   |-> JoinResponse,
                                  epoch  |-> current_epoch[s],
                                  leader |-> leader[s],
                                  result |-> Ok,
                                  error  |-> Nil,
                                  dest   |-> peer,
                                  source |-> s])
              /\ UNCHANGED <<server_ids, candidateVars, role, current_epoch, state, 
                             leader, voted_for, pending_fetch, pending_ack,
                             hwm, invVars, auxVars>>

(*
    ACTION: RejectJoinRequest ----------------------------------
    Server (s) is a Leader and rejects an invalid JoinRequest.
    
    Model checking note:
    Note in this specification we only send a rejection
    for a check result that is NotLeader or AlreadyMember.
    For the check results ReconfigInProgress and LeaderNotReady
    we simply don't send a response at all until either
    the request can be accepted or rejected. This avoids
    the need for modeling retries which would increase the state
    space and make liveness hard to check due to infinite retries.
    The implementation would send rejections immediately.
*)
RejectJoinRequest(s) ==
    \* enabling conditions
    /\ \E m \in Messages :
        /\ ReceivableMessage(m, JoinRequest, AnyEpoch)
        /\ s = m.dest
        /\ LET peer == m.source
               check == JoinCheck(s, m)
           IN
              /\ check \in {NotLeader, AlreadyMember}
              \* state mutations
              /\ Reply(m, [type   |-> JoinResponse,
                           epoch  |-> current_epoch[s],
                           leader |-> leader[s],
                           result |-> NotOk,
                           error  |-> check,
                           dest   |-> peer,
                           source |-> s])
              /\ UNCHANGED <<server_ids, serverVars, candidateVars,
                             leaderVars, logVars, invVars, auxVars>>                                 


(* 
    ACTION: HandleJoinResponse ----------------------------------
    Server (s) is an Observer in Follower state that receives 
    a rejection JoinResponse.
    
    Next, it may:
    (1) Transition to unattached if the source doesn't know 
        who the leader is.
    (2) Send a new JoinRequest if the error wasn't AlreadyMember
        and the source knows who the leader is.
    
    We don't model a success response as the observer simply 
    carries on being an observer until it sees the AddServerCommand
    in its log.

    Note this does not use MaybeHandleCommonResponse as that
    function needed modifying which introduced other unexpected
    behaviour leading to invariant violations.

    Recommendation: I recommend removing that function entirely
    as it makes reasoning about the logic much harder. 
    Modifying it can easily break something in a non-obvious
    way. Best to put the conditions clearly inside each Handle*
    method so it is easy to reason about, even if it introduces
    more duplicate code.
*)
HandleRejectJoinResponse(s) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, JoinResponse, AnyEpoch)
        /\ s = m.dest
        /\ role[s] = Observer
        /\ m.result = NotOk
        \* state mutations
        /\ CASE /\ m.epoch >= current_epoch[s]
                /\ m.result \in { NotLeader, FencedLeaderEpoch }
                /\ m.leader # Nil ->
                      /\ leader' = [leader EXCEPT ![s] = m.leader]
                      /\ current_epoch' = [current_epoch EXCEPT ![s] = m.epoch]
                      /\ Reply(m, [type      |-> JoinRequest,
                                   epoch     |-> current_epoch[s],
                                   dest      |-> m.leader,
                                   source    |-> s])
                      /\ UNCHANGED << state >>
             [] /\ m.epoch >= current_epoch[s]
                /\ m.result \in { NotLeader, FencedLeaderEpoch }
                /\ m.leader = Nil ->
                      /\ leader' = [leader EXCEPT ![s] = Nil]
                      /\ state' = [state EXCEPT ![s] = Unattached]
                      /\ current_epoch' = [current_epoch EXCEPT ![s] = m.epoch]
                      /\ Discard(m)
             [] OTHER ->
                      /\ Discard(m)
                      /\ UNCHANGED << leader, state, current_epoch >>
        /\ UNCHANGED <<server_ids, role, config, voted_for, pending_fetch, pending_ack,
                       candidateVars, leaderVars, logVars, invVars, auxVars>>
                       
(* 
    ACTION: HandleRemoveRequest ----------------------------------
    Server (s) is a leader and a voter (a leader observer by
    definition already has a RemoveServerCommand in-progress). 
    
    Leader (s) accepts a valid RemoveRequest from an Administrator
    and appends a RemoveServerCommand (with the identity of the
    server to removed) to its log and switches to the new 
    configuration immediately.

    To be valid a RemoveRequest the following conditions are required:
    (1) The request is received by a leader
    (2) The leaving node must be a member of the current configuration.
    (3) The leader have no in-progress reconfiguration.
    (4) The leader must have committed an offset in the current epoch.
    
    Note that this server may be the one being removed. In that case
    it switches to being an observer but continues as leader. Once it 
    has committed the command it will resign.
*)
RemoveCheck(s, peer) ==
    (* Enforces the rules above *)
    CASE state[s] # Leader -> NotLeader
      [] peer \notin config[s].members -> UnknownMember
      [] HasPendingConfigCommand(s) -> ReconfigInProgress
      [] ~LeaderHasCommittedOffsetsInCurrentEpoch(s) -> LeaderNotReady
      [] OTHER -> Ok

HandleRemoveRequest(s) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ \E remove_server \in StartedServers :
        /\ aux_ctrs.remove_reconfig_ctr < MaxRemoveReconfigs
        /\ RemoveCheck(s, remove_server) = Ok
        /\ Cardinality(config[s].members) > MinClusterSize
        \* state mutations
        /\ LET entry      == [command |-> RemoveServerCommand,
                              epoch   |-> current_epoch[s],
                              value   |-> [id      |-> config[s].id + 1,
                                           old     |-> remove_server,
                                           members |-> config[s].members \ {remove_server}]]
               new_log    == Append(log[s], entry)
           IN  /\ log' = [log EXCEPT ![s] = new_log]
               /\ config' = [config EXCEPT ![s] = 
                                  ConfigFor(Len(new_log),
                                            entry, 
                                            hwm[s])]
               /\ IF s = remove_server
                  THEN role' = [role EXCEPT ![s] = Observer]
                  ELSE UNCHANGED role
               /\ aux_ctrs' = [aux_ctrs EXCEPT !.remove_reconfig_ctr = @ + 1]                                 
        /\ UNCHANGED <<server_ids, NetworkVars, candidateVars,  current_epoch, 
                       state, leader, voted_for, pending_fetch, pending_ack, leaderVars,
                       hwm, invVars, aux_disk_id_gen>>  

\* Network connectivity changes --------------------
\* -------------------------------------------------

(*
    ACTION: ChangeNetworkConnectivity --------------
    Non-deterministically chooses whether each server pair
    that exists, have network connectivity between them.

    This takes into account the dead servers to avoid the
    situation where connectivity prevents a server majority
    from being able to make progress. For example, if
    we limit the number of disconnected pairs to 1, then a
    3 server cluster will continue to make progress. However,
    if one of those servers is dead, and the linkbetween the
    remaining two servers is cut, any liveness checks
    will break.
*)
ChangeNetworkConnectivity ==
    LET dead_servers == { s \in StartedServers : state[s] = DeadNoState }
    IN /\ ChangeConnectivity(dead_servers)
       /\ UNCHANGED << server_ids, serverVars, candidateVars, 
                       leaderVars, logVars, invVars, auxVars >>

\*================================================
\* Init and Next
\*================================================

InitServerVars(init_leader, server_identities) ==
    LET servers == DOMAIN server_identities
    IN
        /\ server_ids    = server_identities
        /\ current_epoch = [s \in servers |-> 1]
        /\ role          = [s \in servers |-> Voter]
        /\ state         = [s \in servers |-> IF s = init_leader 
                                              THEN Leader
                                              ELSE Follower]
        /\ leader        = [s \in servers |-> init_leader]
        /\ voted_for     = [s \in servers |-> Nil]
        /\ pending_fetch = [s \in servers |-> Nil]
        /\ pending_ack   = [s \in servers |-> {}]
        /\ config        = [s \in servers |-> [id        |-> 1,
                                               members   |-> servers,
                                               committed |-> TRUE]]

InitCandidateVars(servers) == 
    votes_granted   = [s \in servers |-> {}]

InitLeaderVars(servers) == 
    flwr_end_offset  = [s \in servers |-> [s1 \in servers |-> 1]]

InitLogVars(servers, first_entry) == 
    /\ log = [s \in servers |-> << first_entry >>]
    /\ hwm = [s \in servers |-> 1]

InitInvVars ==
    /\ inv_sent = {}
    /\ inv_pos_acked = {}
    /\ inv_neg_acked = {}

InitAuxVars == 
    /\ aux_ctrs = [election_ctr        |-> 0,
                   value_ctr           |-> [v \in 1..MaxElections+1 |-> 0],
                   crash_ctr           |-> 0,
                   restart_ctr         |-> 0,
                   add_reconfig_ctr    |-> 0,
                   remove_reconfig_ctr |-> 0]
    /\ aux_disk_id_gen = 0

(* Initial state notes:
    - Seeds a cluster of size InitClusterSize with an established leader
      and followers without any observers.
    - The disk_id is the same for all servers of the initial cluster
      which wouldn't be the case in reality but is simpler here and does not
      violate the global identity uniqueness.
*)
Init == LET servers     == 1..InitClusterSize
            hosts       == SetToSeq(Hosts)
            srv_ids     == [s \in servers |-> 
                                [host    |-> hosts[s], 
                                 disk_id |-> 0]]                        
            init_leader == CHOOSE i \in servers : TRUE
            first_entry == [command |-> InitClusterCommand,
                            epoch   |-> 1,
                            value   |-> [id      |-> 1,
                                         members |-> servers]]
        IN
            /\ NetworkInit(AllServers)
            /\ InitServerVars(init_leader, srv_ids)
            /\ InitCandidateVars(servers)
            /\ InitLeaderVars(servers)
            /\ InitLogVars(servers, first_entry)
            /\ InitInvVars
            /\ InitAuxVars       

Next == 
    \* server starts/restarts/crashes--------------
    \/ StartNewServer
    \/ \E s \in AllServers :
        \/ RestartWithState(s)
        \/ CrashLoseState(s)
        \* reconfiguration actions ----------------
        \/ SendJoinRequest(s)
        \/ AcceptJoinRequest(s)
        \/ RejectJoinRequest(s)
        \/ HandleRejectJoinResponse(s)
        \/ HandleRemoveRequest(s)
        \* elections ------------------------------
        \/ RequestVote(s)
        \/ HandleRequestVoteRequest(s)
        \/ HandleRequestVoteResponse(s)
        \/ BecomeLeader(s)
        \* follower actions -----------------------
        \/ AcceptBeginQuorumRequest(s)
        \/ SendFetchRequest(s)
        \/ HandleSuccessFetchResponse(s)
        \/ HandleDivergingFetchResponse(s)
        \/ HandleNonSuccessFetchResponse(s)
        \* leader actions -------------------------
        \/ ClientRequest(s)
    \/ \E s, peer \in AllServers :        
        \/ RejectFetchRequest(s, peer)
        \/ DivergingFetchRequest(s, peer)
        \/ AcceptFetchRequestFromVoter(s, peer)
        \/ AcceptFetchRequestFromObserver(s, peer)
    \* network connectivity -----------------------
    \/ ChangeNetworkConnectivity

(*
    FAIRNESS notes.
    Liveness checks will break unless we force the model
    checker to allow all servers to make progress. Without
    weak fairness across all servers, then actions such
    as fetch requests can cause cycles where only a subset
    of servers ever send fetch requests, leaving the 
    cluster unable to make progress.
*)    
Fairness ==
    \A s \in AllServers :
        /\ WF_vars(RequestVote(s))
        /\ WF_vars(HandleRequestVoteRequest(s))
        /\ WF_vars(HandleRequestVoteResponse(s))
        /\ WF_vars(BecomeLeader(s))
        /\ WF_vars(AcceptBeginQuorumRequest(s))
        /\ WF_vars(SendFetchRequest(s))
        /\ WF_vars(HandleSuccessFetchResponse(s))
        /\ WF_vars(HandleDivergingFetchResponse(s))
        /\ WF_vars(HandleNonSuccessFetchResponse(s))
        /\ WF_vars(AcceptJoinRequest(s))
        /\ WF_vars(RejectJoinRequest(s))
        /\ WF_vars(HandleRejectJoinResponse(s))
        /\ WF_vars(HandleRemoveRequest(s))
        /\ \A peer \in AllServers :
            /\ WF_vars(RejectFetchRequest(s, peer))
            /\ WF_vars(DivergingFetchRequest(s, peer))
            /\ WF_vars(AcceptFetchRequestFromVoter(s, peer))
            /\ WF_vars(AcceptFetchRequestFromObserver(s, peer))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

===================================================