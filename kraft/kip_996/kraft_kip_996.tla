--------------------------------- MODULE kraft_kip_996 ---------------------------------
(*NOTES
Author: Jack Vanlightly

-----------------------------------------------
Kafka KRaft TLA+ specification with KIP-996 Pre-Vote + KIP-853 reconfiguration
-----------------------------------------------

This specification is based on KIP-853 (reconfiguration) + KIP-996 (pre-vote).
Find the KIP here:
- https://cwiki.apache.org/confluence/display/KAFKA/KIP-853%3A+KRaft+Controller+Membership+Changes
- https://cwiki.apache.org/confluence/display/KAFKA/KIP-996%3A+Pre-Vote
*)

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC,
        kraft_kip_996_types, 
        kraft_kip_996_functions,
        kraft_kip_996_properties,
        kraft_kip_996_liveness,
        network

\* ================================================================
\* ACTIONS
\* ================================================================

\* Each action is split into two parts:
\* - enabling conditions that make the action enabled or not.
\*      - some conditions constrain behavior based on the required behavior as per the KIP
\*      - some conditions constrain the state space
\* - state mutations - changes to the variables in the next state.

(*
    ACTION: ChangeNetworkConnectivity --------------
    Non-deterministically chooses whether each server pair
    that exists, have network connectivity between them.

    It ensures that there are enough connections for at least
    one server to carry out a successful election. 
*)

\* ACTION
ChangeNetworkConnectivity ==
    /\ CanChangeConnectivity 
    /\ \E connected \in NewConnectedPairs :
        \* No dead servers are counted in the connected server pairs
        /\ ~\E s \in StartedServers :
            \E pair \in connected :
                /\ s \in pair
                /\ state[s] = DeadNoState
        \* Connections allow for elections to progress.
        /\ LIVENESS_ElectionsCanProgress(connected)
        \* Change the connectivity to this new connected set of servers
        /\ ChangeConnectivity(connected)
        /\ UNCHANGED << server_ids, serverVars, candidateVars, 
                        leaderVars, logVars, invVars, auxVars >>

\* Server actions ----------------------------------
\* -------------------------------------------------

(* 
    ACTION: RestartWithState -------------------------------------
    
    Server (s) restarts from stable storage.
    
    KRaft durably stores: state, current_epoch, leader, 
    voted_for and log.
*)

\* ACTION
RestartWithState(s) ==
    \* enabling conditions
    /\ aux_ctrs.restart_ctr < MaxRestarts
    /\ s \in StartedServers
    /\ state[s] # DeadNoState
    \* state mutations
    /\ LET new_state == CASE /\ state[s] = Leader 
                             /\ IsVoter(s) ->
                                    TransitionToResigned(s)
                          [] /\ state[s] = Leader 
                             /\ IsObserver(s) ->
                                    BootTimeUnattached(s)
                          [] /\ state[s] = Prospective -> 
                                    BootTimeUnattached(s)
                          [] OTHER ->
                                    NoTransition(s)
      IN
         /\ ApplyState(s, new_state)
         /\ hwm' = [hwm EXCEPT ![s] = 0]
         /\ ResetFetchStateIfFollower(s)
         /\ ResetFollowerFetchStateIfLeader(s, DOMAIN flwr_end_offset[s])
         /\ FailAnyPendingWritesIfLeader(s)
         /\ aux_ctrs' = [aux_ctrs EXCEPT !.restart_ctr = @ + 1]
         /\ UNCHANGED <<server_ids, NetworkVars, config, log, aux_disk_id_gen>>

(* 
    ACTION: CrashLoseState -------------------------------------
    
    Server (s) is a member of the cluster and crashes with 
    all state lost.
    
    To avoid causing data loss due to a majority of servers
    crashing and losing data, this action is only enabled
    if losing this server does not cause the Raft cluster
    to become non-functional. Exploring such destructive cases
    is not actually helpful, so we avoid it.
*)

CrashAllowed(s) ==
    (*
        If testing liveness, then make sure that permanently crashing this
        server does not prevent the cluster from making future progress
    *)
    IF TestLiveness
    THEN LET connected_pairs == ConnectedPairsWithoutServer(s)
         IN LIVENESS_ElectionsCanProgress(connected_pairs)
    ELSE TRUE

\* ACTION
CrashLoseState(s) ==
    \* enabling conditions
    /\ aux_ctrs.crash_ctr < MaxPermCrashes
    /\ s \in StartedServers
    /\ IsVoter(s)
    /\ CrashAllowed(s)
    \* state mutations
    /\ DisconnectServer(s)
    /\ state' = [state EXCEPT ![s] = DeadNoState]
    /\ config' = [config EXCEPT ![s] = NoConfig]
    /\ current_epoch' = [current_epoch EXCEPT ![s] = 0]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ voted_for' = [voted_for EXCEPT ![s] = Nil]
    /\ votes_recv' = [votes_recv EXCEPT ![s] = {}]
    /\ ResetFetchStateIfFollower(s)
    /\ ResetFollowerFetchStateIfLeader(s, {})
    /\ FailAnyPendingWritesIfLeader(s)
    /\ log' = [log EXCEPT ![s] = <<>>]
    /\ hwm' = [hwm EXCEPT ![s] = 0]
    /\ aux_ctrs' = [aux_ctrs EXCEPT !.crash_ctr = @ + 1]
    /\ UNCHANGED <<aux_disk_id_gen, server_ids, aux_disk_id_gen>>

(* 
    ACTION: CheckQuorumResign -------------------------------------
    
    Server (s) is a leader but resigns because it cannot receive 
    fetch requests from enough followers to consitute a functional
    majority. This happens either due to enough followers being
    disconnected or no longer believing this server is the leader.
    
    Note that the spec allows for the leader to resign due to losing
    functional majority, or just randomly if we're under the
    disruption limit (required for limiting state space).

    Note that min_connected is a minority as we do not count server
    (s), when (s) is included, it would reach a majority. 
*)

ShouldResign(s) ==
    LET connected_peers == Quantify(config[s].members, LAMBDA peer :
                                        /\ s # peer
                                        /\ Connected(s, peer)
                                        /\ \/ /\ IsVoter(peer)
                                              /\ current_epoch[s] >= current_epoch[peer]
                                           \/ IsObserver(peer))
        min_connected   == IF s \in config[s].members
                           THEN Cardinality(config[s].members) \div 2
                           ELSE Cardinality(config[s].members) \div 2 + 1
    IN connected_peers < min_connected

\* ACTION
CheckQuorumResign(s) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ state[s] = Leader
    /\ LET should_resign == ShouldResign(s)
           new_state == TransitionToResigned(s)
       IN /\ \/ should_resign
             \/ AUX_UnderDisruptionLimit
          \* state mutations
          /\ ApplyState(s, new_state)
          /\ FailAnyPendingWritesIfLeader(s)
          /\ ResetFollowerFetchStateIfLeader(s, config[s].members)
          /\ IF should_resign
             THEN UNCHANGED aux_ctrs
             ELSE AUX_IncrementDisruptions
    /\ UNCHANGED <<NetworkVars, server_ids, config, current_epoch,
                   fetch_state, logVars, aux_disk_id_gen>>

(*
    ACTION: VoterFetchTimeout and VoterElectionTimeout ------------------
    
    Server (s) is a voter and not the leader, and experiences either:
    1. A fetch time out as a Follower.
    2. An election timeout as a Candidate or Unattached server. 
    
    The server sends a pre-vote RequestVote request to all peers in
    its configuration but not itself. It adds itself to its received
    votes set.
    
    Note this excludes Resigned servers, see ResignedElectionTimeout.
*)

NotEnoughVotes(s, pre_vote) ==
    /\ ~HasInflightVoteReq(s, RequestVoteRequest, pre_vote)
    /\ ~HasInflightVoteRes(s, RequestVoteResponse, pre_vote)
    /\ Cardinality(votes_recv[s]) < MajorityCount(config[s].members)
    /\ state[s] # Leader

SendPreVoteRequests(s) ==
    SendAll({[type            |-> RequestVoteRequest,
              replica_epoch   |-> current_epoch[s],
              last_log_epoch  |-> LastEpoch(log[s]),
              last_log_offset |-> Len(log[s]),
              pre_vote        |-> TRUE,
              source          |-> s,
              dest            |-> s1] : s1 \in config[s].members \ {s}})

\* ACTION
VoterFetchTimeout(s) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ IsVoter(s)
    /\ s \in config[s].members
    /\ state[s] = Follower
    /\ \/ FetchCanTimeout(s)
       \/ AUX_UnderDisruptionLimit
    \* state mutations
    /\ ApplyState(s, TransitionToProspective(s, current_epoch[s]))
    /\ ResetFetchStateIfFollower(s)
    /\ SendPreVoteRequests(s)
    /\ AUX_IncTimeoutCtrs(~FetchCanTimeout(s))
    /\ UNCHANGED <<server_ids, config, flwr_end_offset,
                   invVars, pending_ack, logVars, aux_disk_id_gen>>

CausalElectionTimeout(s) ==
    \* CASE 1) The server is a candidate and has not received 
    \*         enough votes to win the election.
    \/ /\ state[s] = Candidate
       /\ NotEnoughVotes(s, FALSE)
    \* CASE 2) The server is unattached
    \/ state[s] = Unattached

EventualElectionTimeout(s) ==
    (* TRUE when a timeout would eventually occur.*)
    CASE 
      \* CASE 1: It happens for a reason and may be needed to make progress
         CausalElectionTimeout(s) -> TRUE 
      \* CASE 2: It just happens, even if everything is stable, so we limit
      \*         the number of times it can happen to limit the state space.
      [] /\ aux_ctrs.disruptive_ctr < MaxDisruptiveElectionTriggers
         /\ state[s] \in { Candidate, Unattached } -> TRUE
      [] OTHER -> FALSE

VoterElectionTimeout(s) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ IsVoter(s)
    /\ s \in config[s].members
    /\ EventualElectionTimeout(s)
    \* state mutations
    /\ ApplyState(s, TransitionToProspective(s, current_epoch[s]))
    /\ ResetFetchStateIfFollower(s)
    /\ SendPreVoteRequests(s)
    /\ AUX_IncTimeoutCtrs(~CausalElectionTimeout(s)) 
    /\ UNCHANGED <<server_ids, config, flwr_end_offset, 
                   pending_ack, invVars, logVars, aux_disk_id_gen>>

(*
    ACTION: ResignedElectionTimeout ---------------------------------
    
    A Resigned server experiences an election timeout and transitions
    to Unattached with a bumped epoch. 
*)

ResignedElectionTimeout(s) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ state[s] = Resigned
    \* state mutations
    /\ ApplyState(s, TransitionToUnattached(s, current_epoch[s] + 1, Nil))
    /\ UNCHANGED <<server_ids, config, flwr_end_offset, fetch_state,
                   invVars, pending_ack, logVars, auxVars, NetworkVars>>

(* 
    ACTION: HandleVoteRequest ------------------------------
    
    Server (s) receives a RequestVote message which could be a pre-vote
    or a standard vote.
     
    While this server may be an Observer and therefore believe 
    it is not a member of a configuration, it may in fact be 
    so (but be lagging) and may be required to process the message
    in order for an election to complete. In other words, if
    an observer ignores pre-vote or standard vote RequestVote messages 
    it may cause a cluster to get stuck.

    When a pre-vote, the server (s) will vote for its peer if all the 
    following are true:
    1) It is not a leader.
    2) It is either Unattached, Prospective, Candidate, Resigned
       or it is a Follower that has never successfully fetched from its current leader.
    3) The log last entry of (s) is <= to the last log entry of (peer)
    
    When a standard vote, the server (s) will vote for its peer if all the 
    following are true:
    1) It is Unattached and either:
        a) has not previously voted in this epoch
        b) has previously voted in this epoch and voted for the peer.
    2) the last log entry of (s) is <= to the last log entry of (peer).
    
    Note that if the vote request has a higher epoch than (s) then (s)
    transitions to Unattached and is therefore not a Follower under the
    above conditions.
*)

GrantPreVote(s, state0, log_ok) ==
    CASE /\ state0.state \in {Unattached, Prospective, Candidate, Resigned}
         /\ log_ok -> TRUE
      [] /\ state0.state = Follower
         /\ fetch_state[s].has_fetch_success = FALSE \* never been able to fetch from leader in current epoch
         /\ log_ok -> TRUE
      [] OTHER     -> FALSE

GrantVote(s, peer, state0, log_ok) ==
    IF state0.state \in { Unattached, Prospective }
    THEN CASE state0.voted_for # Nil ->
                 state0.voted_for = peer \* can grant the same vote again
           [] state0.leader # Nil ->
                 FALSE
           [] OTHER -> log_ok
    ELSE FALSE

FinalState(s, peer, m, state0, grant_vote, pre_vote) ==
    CASE pre_vote ->
            state0
      [] grant_vote /\ state0.state = Unattached ->
            TransitionToUnattachedAddVote(s, m.replica_epoch, state0, peer)
      [] grant_vote /\ state0.state = Prospective ->
            TransitionToProspectiveAddVote(s, m.replica_epoch, state0, peer)
      [] OTHER -> state0 
    
HandleVoteRequest(s, peer) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, RequestVoteRequest, AnyEpoch)
        /\ s = m.dest
        /\ peer = m.source
        /\ LET error == CASE m.last_log_epoch > m.replica_epoch -> InvalidRequest
                          [] m.replica_epoch < current_epoch[s] -> FencedLeaderEpoch
                          [] OTHER -> Nil
               state0   == IF m.replica_epoch > current_epoch[s]
                           THEN TransitionToUnattached(s, m.replica_epoch, Nil)
                           ELSE NoTransition(s)
               log_ok == CompareEntries(m.last_log_offset,
                                        m.last_log_epoch,
                                        Len(log[s]),
                                        LastEpoch(log[s])) >= 0
               grant_vote == IF m.pre_vote = TRUE
                             THEN GrantPreVote(s, state0, log_ok)
                             ELSE GrantVote(s, peer, state0, log_ok) 
               final_state == FinalState(s, peer, m, state0, grant_vote, m.pre_vote)
           IN \* state mutations
              IF error = Nil
              THEN \* If the server changed state then may be reset fetch state or fail pending writes
                   /\ IF state[s] # final_state.state
                      THEN /\ ResetFetchStateIfFollower(s)
                           /\ FailAnyPendingWritesIfLeader(s)
                      ELSE UNCHANGED << fetch_state, pending_ack, invVars >>
                   \* Apply the state change
                   /\ ApplyState(s, final_state)
                   /\ Reply(m, [type          |-> RequestVoteResponse,
                                replica_epoch |-> m.replica_epoch,
                                leader        |-> final_state.leader,
                                vote_granted  |-> grant_vote,
                                pre_vote      |-> m.pre_vote,
                                error         |-> Nil,
                                source        |-> s,
                                dest          |-> peer])
              ELSE /\ Reply(m, [type          |-> RequestVoteResponse,
                                replica_epoch |-> current_epoch[s],
                                leader        |-> leader[s],
                                vote_granted  |-> FALSE,
                                pre_vote      |-> m.pre_vote,
                                error         |-> error,
                                source        |-> s,
                                dest          |-> peer])
                   /\ ApplyNoStateChange(s)
                   /\ UNCHANGED << fetch_state, pending_ack, invVars >>
        /\ UNCHANGED <<server_ids, config, leaderVars, logVars, auxVars>>

(* 
    ACTION: HandleVoteResponse --------------------------------
    
    Server (s) receives a RequestVote response.
    
    The server would normally be a prospective in the case of a
    pre-vote or candidate in the case of a standard vote, but it could
    have already transitioned to a different state or epoch.
    The logic of MaybeHandleCommonResponse (named after a method in the
    actual code), handles these situations.

    First, the MaybeHandleCommonResponse may do the following:
    1. Cause the server to transition to follower if the response
       has an epoch >= the server's epoch and a non-null leader id.
    2. Cause the server to transition to unattached if the response
       has a higher epoch and no leader id.
    
    Else if the server has been granted a vote and the server is 
    still a Prospective for a pre-vote, or a candidate for a standard
    vote, then it adds the vote to its received votes.
    
    Concluding the election phase happens in different actions (ConcludePreVote
    or BecomeLeader). Remember that an election may terminate in this action
    due to MaybeHandleCommonResponse.
*)

MaybeLoseLeadership(s, state1) ==
    (*
        The server may be a leader that must resign, and therefore
        fail pending writes and reset follower fetch state.
        This can happen because it's possible to continue receiving 
        vote responses of the election that this server just won, 
        that causes this server to have to relinquish it's new found
        leadership because the vote response has a higher epoch.
    *)
    IF state[s] = Leader /\ state1.state # Leader
    THEN /\ FailAnyPendingWritesIfLeader(s)
         /\ ResetFollowerFetchStateIfLeader(s, config[s].members)
    ELSE UNCHANGED << flwr_end_offset, pending_ack, invVars >>

HandleVoteResponse(s, peer) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, RequestVoteResponse, AnyEpoch)
        /\ s = m.dest
        /\ peer = m.source
        /\ IsVoter(s) \* new check because roles can change with reconfigurations
        \* state mutations
        /\ LET state0 == MaybeHandleCommonResponse(s, m.leader, m.replica_epoch, m.error)
               state1 == IF /\ state0.handled = FALSE
                            /\ \/ /\ state0.state = Prospective
                                  /\ m.pre_vote = TRUE
                               \/ /\ state0.state = Candidate
                                  /\ m.pre_vote = FALSE
                            /\ m.vote_granted
                         THEN [state0 EXCEPT !.votes_recv = @ \union {peer}]
                         ELSE state0
           IN /\ ApplyState(s, state1)
              /\ MaybeLoseLeadership(s, state1)
              /\ Discard(m)
        /\ UNCHANGED <<server_ids, config, fetch_state, logVars, auxVars>>

(*
    ACTION: ConcludePreVote -----------------------------------------------
    
    Server (s) is a voter and prospective. 
    
    The prospective has either been granted a pre-vote from a majority
    or it did not receive enough votes. This action does not include 
    transitioning to a Follower or Unattached due to a specific prevote 
    RequestVoteResponse (that is handled in HandleVoteResponse).
    
    If the server received a majority prevote then it initiates an
    election by:
    1. Incrementing its epoch.
    2. Sending a RequestVote request to all peers in the current
       configuration.
       
    If the server did not receive enough votes, but also did not
    transition to follower/unattached due to a RequestVoteResponse, then it
    transitions to Unattached.
*)

WithinEpochLimit(s) ==
    IF TestLiveness
    THEN TRUE \* an election make may be required for a cluster to become functional
    ELSE current_epoch[s] < MaxEpoch

NoMorePreVotesToCount(s) ==
    \* There are no more relevant inflight messages (either they were processed or lost or network partition) 
    /\ ~HasInflightVoteReq(s, RequestVoteRequest, TRUE)
    /\ ~HasInflightVoteRes(s, RequestVoteResponse, TRUE)

ConcludePreVote(s) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ IsVoter(s)
    /\ state[s] = Prospective
    /\ WithinEpochLimit(s)
    /\ s \in config[s].members
    /\ \/ NoMorePreVotesToCount(s)
       \/ votes_recv[s] \in Quorum(config[s].members)
    \* state mutations
    /\ CASE 
         \* CASE 1 - It received enough votes  
            votes_recv[s] \in Quorum(config[s].members) ->
                LET new_state == TransitionToCandidate(s)
                IN /\ ApplyState(s, new_state)
                   /\ SendAll({[type            |-> RequestVoteRequest,
                                replica_epoch   |-> new_state.epoch,
                                last_log_epoch  |-> LastEpoch(log[s]),
                                last_log_offset |-> Len(log[s]),
                                pre_vote        |-> FALSE,  
                                source          |-> s,
                                dest            |-> s1] : s1 \in config[s].members \ {s}})
         \* CASE 2 - It did not receive enough votes but has a last known leader id
         [] leader[s] # Nil ->
                LET new_state == TransitionToFollower(s, leader[s], current_epoch[s])
                IN /\ ApplyState(s, new_state)
                   /\ UNCHANGED NetworkVars
         \* CASE 3 - Not enough votes, no leader id
         [] OTHER ->
                LET new_state == TransitionToUnattached(s, current_epoch[s], leader[s])
                IN /\ ApplyState(s, new_state)
                   /\ UNCHANGED NetworkVars
    /\ UNCHANGED <<server_ids, config, pending_ack, leaderVars, logVars,
                   fetch_state, invVars, auxVars>>

(*
    ACTION: BecomeLeader -------------------------------------------
    
    Server (s) is a voter in the Candidate state. It has
    received enough votes to win the election and transitions
    to leader. It sends all peers in its current configuration
    a BeginQuorumEpochRequest to notify them of its leadership.
*)
BecomeLeader(s) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ state[s] = Candidate
    /\ votes_recv[s] \in Quorum(config[s].members)
    \* state mutations
    /\ LET new_state == TransitionToLeader(s)
           \* insert a new entry for this leader epoch
           entry == [command |-> LeaderChangeRecord,
                     epoch   |-> current_epoch[s],
                     value   |-> Nil]
           new_log == Append(log[s], entry)
       IN /\ ApplyState(s, new_state)
          /\ log' = [log EXCEPT ![s] = new_log]
          /\ IF Cardinality(config[s].members) = 1
             THEN hwm' = [hwm EXCEPT ![s] = Len(new_log)]
             ELSE UNCHANGED hwm
          /\ ResetFollowerFetchStateIfLeader(s, config[s].members)
          /\ ResetFetchStateIfFollower(s)
          /\ SendAllOnce(
                  {[type          |-> BeginQuorumEpochRequest,
                    replica_epoch |-> current_epoch[s],
                    resend        |-> FALSE,
                    source        |-> s,
                    dest          |-> peer] : peer \in config[s].members \ {s}})
          /\ UNCHANGED <<server_ids, config, pending_ack, hwm, invVars, auxVars>>

(*
    ACTION: ResendBeginQuorumEpochRequest -------------------------------------------
    
    Server (s) is a voter in the Leader state. It needs to resend
    a follower the BeginQuorumEpochRequest because the follower
    did not receive it the first time.
    
    This is required when testing liveness.
*)
                      
BeginQuorumEpochRequestTimeout(s, peer) ==
    (* Given that timeouts based on time passed can't be modeled,
       this formula figures out if the original request has not
       been processed and never will. *)
    \* The 1st epoch was set up by initial state, so ignore that case.
    /\ current_epoch[s] > 1 
    \* The BeginQuorumEpochRequest got dropped
    /\ ~NotLostReqWithReplicaEpoch(s, peer, BeginQuorumEpochRequest, current_epoch[s])
    \* There is a connection, so a new message would arrive
    /\ Connected(s, peer)
    \* The peer has a stale epoch or is not a follower yet, so needs this message
    /\ \/ current_epoch[s] > current_epoch[peer]
       \/ /\ current_epoch[s] = current_epoch[peer]
          /\ state[peer] # Follower

ResendBeginQuorumEpochRequest(s, peer) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ state[s] = Leader
    /\ s # peer
    /\ peer \in config[s].members
    /\ BeginQuorumEpochRequestTimeout(s, peer)
    \* state mutations
    /\ Send([type          |-> BeginQuorumEpochRequest,
             replica_epoch |-> current_epoch[s],
             resend        |-> TRUE,
             source        |-> s,
             dest          |-> peer])
    /\ UNCHANGED <<logVars, serverVars, leaderVars, candidateVars,
                   invVars, auxVars, server_ids>>  

(* 
    ACTION: AcceptBeginQuorumRequest -------------------------------------------
    
    Server (s), which is a voter, receives a BeginQuorumEpochRequest 
    and transitions to a follower unless the message is stale.
    
    Note that rejecting a BeginQuorumEpochRequest is not modeled as
    it is a best effort mechanism only.
*)
AcceptBeginQuorumRequest(s, peer) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, BeginQuorumEpochRequest, AnyEpoch)
        /\ s = m.dest
        /\ peer = m.source
        /\ LET error    == IF m.replica_epoch < current_epoch[s]
                           THEN FencedLeaderEpoch
                           ELSE Nil
               new_state == MaybeTransition(s, peer, m.replica_epoch)
           IN /\ error = Nil
              \* state mutations
              /\ ApplyState(s, new_state)
              /\ ResetFetchStateIfFollower(s)
              /\ FailAnyPendingWritesIfLeader(s)
              /\ Discard(m)
        /\ UNCHANGED <<server_ids, config, logVars, leaderVars, auxVars>>

(* 
    ACTION: HandleClientRequest ----------------------------------
    
    A client sends a write request to server (s) which is
    a leader. 
    
    TODO: Discuss merits of allowing a leader that is an
          observer to accept writes. Doing so will be better
          for availability and still be safe. A leader can 
          be an observer during a reconfiguration. However,
          it is likely that some of the produce requests written
          to the log after the RemoveVoter command will get
          negatively acknowledged when the leader resigns.
*)

WithinValuesPerEpochLimit(s) ==
    (* State space limit trick*)
    Quantify(DOMAIN log[s], LAMBDA offset : 
                        /\ log[s][offset].epoch = current_epoch[s]
                        /\ log[s][offset].command = AppendCommand)
        < MaxValuesPerEpoch

HandleClientRequest(s) ==
    \* enabling conditions
    \E v \in Value : 
        /\ s \in StartedServers
        /\ state[s] = Leader
        /\ v \notin inv_sent \* prevent submitting the same value repeatedly
        /\ WithinValuesPerEpochLimit(s)
        \* state mutations
        /\ LET entry == [command |-> AppendCommand,
                         epoch   |-> current_epoch[s],
                         value   |-> v]
               new_log == Append(log[s], entry)
           IN  /\ log' = [log EXCEPT ![s] = new_log]
               /\ IF Cardinality(config[s].members) = 1
                  THEN hwm' = [hwm EXCEPT ![s] = Len(new_log)]
                  ELSE UNCHANGED hwm
               /\ pending_ack' = [pending_ack EXCEPT ![s] = @ \union {v}]
               /\ inv_sent' = inv_sent \union {v}
        /\ UNCHANGED <<server_ids, config, current_epoch, state, voted_for, 
                       leader, fetch_state, NetworkVars, candidateVars,
                       leaderVars, inv_pos_acked, inv_neg_acked, auxVars>>
                       
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

ShouldSendFetch(s, peer) ==
    \* CASE 1) It is a follower and knows who the leader is 
    \* and can send a fetch request to the leader...
    \/ /\ fetch_state[s].pending_fetch = Nil
       /\ leader[s] = peer
       /\ state[s] = Follower
       /\ LIVENESS_HelpsMakeProgress(s, peer, Len(log[s])+1)
       /\ ~LIVENESS_InPrevoteCycle(s, peer)
    \* CASE 2) It is a voter and is unattached and doesn't know who 
    \* the leader is and picks a random voter to fetch from, knowing 
    \* that if it isn't the leader, it will include the leader id in
    \* its response if it knows.
    \/ /\ fetch_state[s].pending_fetch = Nil
       /\ IsVoter(s)
       /\ state[s] = Unattached
       /\ LIVENESS_ValidPeer(s, peer)
    \* Case 3) It is an Observer follower that experienced a fetch timeout,
    \* an Observer does not change state, instead, it just chooses a random
    \* peer to fetch from.
    \/ /\ IsObserver(s)
       /\ state[s] = Follower
       /\ FetchCanTimeout(s)
       /\ LIVENESS_MaybeNotSamePeerAgain(s, peer)

SendFetchRequest(s, peer) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ peer \in StartedServers 
    /\ s # peer
    /\ ShouldSendFetch(s, peer)
    \* state mutations
    /\ LET last_log_offset == Len(log[s])
           last_log_epoch  == IF last_log_offset > 0 
                              THEN log[s][last_log_offset].epoch
                              ELSE 0
           fetch_msg    == [type               |-> FetchRequest,
                            replica_epoch      |-> current_epoch[s],
                            fetch_offset       |-> last_log_offset + 1,
                            last_fetched_epoch |-> last_log_epoch,
                            source             |-> s,
                            dest               |-> peer]
       IN /\ UpdateFetchStateWithFetchReq(s, fetch_msg)
          /\ Send(fetch_msg)
    /\ UNCHANGED <<server_ids, config, current_epoch, state, 
                   voted_for, leader, pending_ack, candidateVars,
                   leaderVars, logVars, invVars, auxVars>>

(* -------------------------------------------------------------
   NOTE: Handling fetch requests -------------------------------
    Note 1:
    The server that receives a fetch request can be the leader
    and an observer. This can happen when the leader has switched
    to being an observer because it is an acting leader that is 
    continuing until it can commit a RemoveServerCommand which 
    removes itself from the configuration.

    Note 2:
    We allow fetches from voters that are not in the current 
    configuration because they may not have reached the reconfiguration
    command yet. Once they do they will switch to being an observer.
    Also this follower may be required in order to commit the command,
    so if the leader rejects fetches from this follower then it
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
                          [] m.replica_epoch < current_epoch[s] -> FencedLeaderEpoch
                          [] m.replica_epoch > current_epoch[s] -> UnknownLeader
                          [] OTHER -> Nil
           IN  /\ error # Nil
               \* state mutations
               /\ Reply(m, [type          |-> FetchResponse,
                            result        |-> NotOk,
                            error         |-> error,
                            leader        |-> leader[s],
                            replica_epoch |-> current_epoch[s],
                            hwm           |-> hwm[s],
                            source        |-> s,
                            dest          |-> peer,
                            correlation   |-> m])
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
        /\ state[s] = Leader
        /\ LET valid_position     == ValidFetchPosition(s, m)
               valid_offset_epoch == EndOffsetForEpoch(s, m.last_fetched_epoch)
               diverging_offset   == valid_offset_epoch.offset + 1
           IN  /\ ~valid_position 
               \* state mutations
               /\ Reply(m, [type                 |-> FetchResponse,
                            replica_epoch        |-> current_epoch[s],
                            result               |-> Diverging,
                            error                |-> Nil,
                            diverging_epoch      |-> valid_offset_epoch.epoch,
                            diverging_end_offset |-> diverging_offset,
                            leader               |-> leader[s],
                            hwm                  |-> hwm[s],
                            source               |-> s,
                            dest                 |-> peer,
                            correlation          |-> m])
               /\ UNCHANGED <<server_ids, candidateVars, leaderVars, serverVars, 
                              logVars, invVars, auxVars>>

(* 
    ACTION: AcceptFetchRequest ------------------------------
    
    Server (s) is a leader that receives a FetchRequest from
    either a Voter or an Observer with a fetch offset and last 
    fetched epoch and responds with an entry if there is one 
    or an empty response if not.

    If the request is from a voter, the leader updates the end
    offset of the fetching peer and advances the high watermark
    if it can. It can only advance the high watermark to an entry
    of the current epoch.
    
    Note this is a quite complex action as advancing the 
    high watermark can cause the leader to leave the cluster
    if it commits a RemoveVoterCommand that pertains to itself.
*)

EntryRemovesServerFromCluster(i, new_hwm) ==
    (* 
        TRUE when this fetch request causes the HWM to advance
        such that a reconfiguration command gets committed and
        this leader is no longer a member in this new configuration.
    *)
    \E offset \in DOMAIN log[i] :
        /\ offset > hwm[i]
        /\ offset <= new_hwm
        /\ log[i][offset].command = RemoveVoterCommand
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

AdvanceHwmAndResign(s, leave_state, values_to_ack) ==
    /\ ApplyState(s, leave_state)
    /\ ResetFollowerFetchStateIfLeader(s, {})
    /\ pending_ack' = [pending_ack EXCEPT ![s] = {}] \* clear pending acks
    /\ inv_neg_acked' = inv_neg_acked \union (pending_ack[s] \ values_to_ack) \* neg ack remaining log entries
    /\ hwm' = [hwm EXCEPT ![s] = 0]
    /\ UNCHANGED inv_sent
    
AdvanceHwm(s, new_config, new_end_offset, new_hwm, values_to_ack) ==
    (* 
        The end offset of the peer is updated, but we may also have switched
        to a new configuration which may include a new member to track
    *)
    /\ pending_ack' = [pending_ack EXCEPT ![s] = @ \ values_to_ack]
    /\ flwr_end_offset' = [flwr_end_offset EXCEPT ![s] = 
                                \* a new map of this configuration, maintain values
                                \* of existing members, set 0 for new members
                                [s1 \in new_config.members |->
                                    IF s1 \in DOMAIN new_end_offset
                                    THEN new_end_offset[s1]
                                    ELSE 0]]
    /\ hwm' = [hwm EXCEPT ![s] = new_hwm]
    /\ UNCHANGED <<state, leader, current_epoch, votes_recv, 
                   voted_for, inv_neg_acked, inv_sent>>    

OnlyUpdateFollowerMap(s, new_end_offset) ==
    /\ flwr_end_offset' = [flwr_end_offset EXCEPT ![s] = new_end_offset]
    /\ UNCHANGED <<config, state, leader, current_epoch, votes_recv, 
                   voted_for, pending_ack, hwm, invVars>>

HandleVoterFetch(s, peer, m, entries) ==
    (*
        A fetch request from a voter may cause the HWM to advance and may
        even cause the leader to resign if it commits its own RemoveVoter
        command.
    *)
    LET new_end_offset == [flwr_end_offset[s] EXCEPT ![peer] = m.fetch_offset-1]
        new_hwm        == NewHighwaterMark(s, new_end_offset)
        leaves         == EntryRemovesServerFromCluster(s, new_hwm)
        config_entry   == MostRecentReconfigEntry(log[s])
        committed_values == { log[s][ind].value : ind \in hwm[s]+1..new_hwm }
        values_to_ack  == pending_ack[s] \intersect committed_values
        new_config     == ConfigFor(config_entry.offset, 
                                    config_entry.entry, 
                                    new_hwm)
        leave_state    == TransitionToResigned(s)
    IN
       /\ IF new_hwm > hwm[s]
          THEN /\ config' = [config EXCEPT ![s] = new_config]
               /\ inv_pos_acked' = inv_pos_acked \union values_to_ack
               /\ IF leaves
                  THEN AdvanceHwmAndResign(s, leave_state, values_to_ack)
                  ELSE AdvanceHwm(s, new_config, new_end_offset, new_hwm, values_to_ack)
          ELSE OnlyUpdateFollowerMap(s, new_end_offset)
       /\ Reply(m, [type          |-> FetchResponse,
                    replica_epoch |-> current_epoch[s],
                    leader        |-> IF leaves THEN Nil ELSE leader[s],
                    result        |-> Ok,
                    error         |-> Nil,
                    entries       |-> entries,
                    hwm           |-> Min({new_hwm, m.fetch_offset}),
                    source        |-> s,
                    dest          |-> peer,
                    correlation   |-> m])

HandleObserverFetch(s, peer, m, entries) ==
    (* 
        The server updates no local state but simply responds
        with entries if there are any to return.
    *)
    /\ Reply(m, [type          |-> FetchResponse,
                replica_epoch |-> current_epoch[s],
                leader        |-> leader[s],
                result        |-> Ok,
                error         |-> Nil,
                entries       |-> entries,
                hwm           |-> Min({m.fetch_offset, hwm[s]}),
                source        |-> s,
                dest          |-> peer,
                correlation   |-> m])
    /\ UNCHANGED << config, current_epoch, state, 
                    voted_for, leader, pending_ack, candidateVars, 
                    leaderVars, logVars, invVars>>

\* ACTION
AcceptFetchRequest(s, peer) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, FetchRequest, EqualEpoch)
        /\ s = m.dest
        /\ peer = m.source
        /\ state[s] = Leader
        /\ peer \in config[s].members
        /\ LET valid_position == ValidFetchPosition(s, m)
               entries        == IF m.fetch_offset > Len(log[s])
                                 THEN <<>>
                                 ELSE <<log[s][m.fetch_offset]>>
           IN 
              /\ valid_position
              \* state mutations
              /\ IF IsPeerVoter(s, peer)
                 THEN HandleVoterFetch(s, peer, m, entries)
                 ELSE HandleObserverFetch(s, peer, m, entries)             
              /\ UNCHANGED <<server_ids, log, fetch_state, auxVars>>

(* ACTION: HandleFetchResponse ------------------------
   
   A server receives a FetchResponse, and the response
   may indicate success, failure or a diverging epoch.
   
   In the case of a successful response, the server appends
   the records to its log. The new entries may include a 
   reconfiguration command and if so, the server immediately 
   switches to the new configuration.
   
   In the case that it is a diverging epoch response, the 
   follower truncates its log to the highest entry it has 
   below the indicated divergent position. Log truncation 
   could remove a reconfiguration command, so this may cause
   the server to switch to a prior configuration.
   
   Other cases are handled by the MaybeHandleCommonResponse
   logic which can involve transitioning to Unattached or
   Follower. For example, if this is an observer and the 
   error was NotLeader and the id of the leader was included
   in the response, the observer can now send fetches to that
   leader. See MaybeHandleCommonResponse for logic flow.
*)

\* ACTION
HandleFetchResponse(s, peer) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ s = m.dest
        /\ peer = m.source
        /\ LET new_state    == MaybeHandleCommonResponse(s, m.leader, m.replica_epoch, m.error)
               new_log      == CASE m.result = Ok ->
                                   IF Len(m.entries) > 0
                                   THEN [log EXCEPT ![s] = Append(@, m.entries[1])]
                                   ELSE log
                                [] m.result = Diverging ->
                                   [log EXCEPT ![s] = TruncateLog(s, m)]
                                [] OTHER -> log
               config_entry == MostRecentReconfigEntry(new_log[s])
               curr_config  == ConfigFor(config_entry.offset,
                                         config_entry.entry,
                                         m.hwm)
           IN /\ fetch_state[s].pending_fetch = m.correlation
              /\ IF new_state.handled = TRUE
                 THEN /\ ApplyState(s, new_state)
                      /\ UNCHANGED << log, hwm, config, flwr_end_offset >>
                 ELSE /\ MaybeSwitchConfigurations(s, curr_config, new_state)
                      /\ log' = new_log
                      /\ IF m.result = Ok
                         THEN hwm' = [hwm  EXCEPT ![s] = m.hwm]
                         ELSE UNCHANGED hwm
                      /\ UNCHANGED voted_for
              /\ UpdateFetchStateWithFetchRes(s, m)
              /\ Discard(m)
              /\ UNCHANGED <<server_ids, pending_ack, invVars, auxVars>>

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
    latter case, it will receive an error response that
    includes the leader id so that subsequent fetches can
    be sent to the leader.

    Note this spec takes a shortcut by magically causing
    the new server to send its first FetchRequest to a
    server that identifies itself as a leader. This reduces
    the state space, but does not affect safety. 
*)

\* ACTION
StartNewServer ==
    \* enabling conditions
    /\ Cardinality(StartedServers) < MaxSpawnedServers
    /\ \E host \in Hosts, anyLeader \in StartedServers :
        LET new_server  == Max(StartedServers) + 1
            disk_id     == aux_disk_id_gen + 1
            identity    == [host |-> host, disk_id |-> disk_id]
            init_config == config[anyLeader] \* start the server with the current config
        IN /\ state[anyLeader] = Leader \* this is a shortcut, but a safe one.
           \* state mutations
           /\ aux_disk_id_gen' = aux_disk_id_gen + 1
           /\ LET fetch_msg == [type               |-> FetchRequest,
                                replica_epoch      |-> 0,
                                fetch_offset       |-> 0,
                                last_fetched_epoch |-> 0,
                                observer           |-> TRUE,
                                source             |-> new_server,
                                dest               |-> anyLeader]
              IN \* Add a new server to the variables
                 /\ server_ids' = server_ids @@ (new_server :> identity)
                 /\ config' = config @@ (new_server :> init_config)
                 /\ state' = state @@ (new_server :> Unattached)
                 /\ current_epoch' = current_epoch @@ (new_server :> 0)
                 /\ leader' = leader @@ (new_server :> Nil)
                 /\ voted_for' = voted_for @@ (new_server :> Nil)
                 /\ fetch_state' = fetch_state @@ (new_server :> BlankFetchState)
                 /\ pending_ack' = pending_ack @@ (new_server :> {})
                 /\ votes_recv' = votes_recv @@ (new_server :> {})
                 /\ flwr_end_offset' = flwr_end_offset @@ (new_server :> EmptyMap)
                 /\ log' = log @@ (new_server :> <<>>)
                 /\ hwm' = hwm @@ (new_server :> 0)
                 /\ Send(fetch_msg)
    /\ UNCHANGED << invVars, aux_ctrs >>

(*
    ACTION: AcceptAddVoterRequest--------------------------------
    Server (s) is a Leader and a Voter (a leader observer by 
    definition already has a RemoveServerCommand in-progress).
    
    Leader (s) accepts a valid AddVoterRequest and:
    - appends an AddServerCommand with the new server identity to
      its log and assumes the new configuration immediately.
    - sends a BeginQuorumRequest to the new member.
    
    KIP-853 states that the leader will wait for the new server
    to catch up before adding the AddVoterCommand to the log. This spec
    does not do that as this measure is an optimization and the
    spec tries to keep things simpler.

    To be valid a AddVoterRequest the following conditions are required:
    (1) The request is received by a leader.
    (2) The joining node cannot already be a member.
    (3) The leader has no in-progress reconfiguration.
    (4) The leader must have committed an offset in the current epoch.
*)

AddVoterCheck(s, add_server) ==
    (* Enforces the above rules. *)
    CASE state[s] # Leader -> NotLeader
      [] add_server \in config[s].members -> AlreadyMember
      [] HasPendingConfigCommand(s) -> ReconfigInProgress
      [] ~LeaderHasCommittedOffsetsInCurrentEpoch(s) -> LeaderNotReady
      [] OTHER -> Ok
      
\* ACTION
AcceptAddVoterRequest(s) ==
    \* enabling conditions
    /\ aux_ctrs.add_reconfig_ctr < MaxAddReconfigs
    /\ s \in StartedServers
    /\ \E add_server \in StartedServers :
        /\ AddVoterCheck(s, add_server) = Ok
        /\ LIVENESS_AddVoterLivenessCondition(s, add_server)
        /\ Cardinality(config[s].members) < MaxClusterSize
        \* state mutations
        /\ LET entry   == [command |-> AddVoterCommand,
                           epoch   |-> current_epoch[s],
                           value   |-> [id      |-> config[s].id + 1,
                                        new     |-> add_server,
                                        members |-> config[s].members 
                                                        \union {add_server}]]
               new_log == Append(log[s], entry)
               new_config == ConfigFor(Len(new_log), entry, hwm[s])
           IN  /\ log' = [log EXCEPT ![s] = new_log]
               /\ config' = [config EXCEPT ![s] = new_config]
               /\ UpdateFollowerEndOffsetMap(s, new_config.members)
               /\ Send([type          |-> BeginQuorumEpochRequest,
                        replica_epoch |-> current_epoch[s],
                        source        |-> s,
                        dest          |-> add_server])
        /\ aux_ctrs' = [aux_ctrs EXCEPT !.add_reconfig_ctr = @ + 1]
        /\ UNCHANGED <<server_ids, candidateVars, current_epoch, state, 
                       leader, voted_for, fetch_state, pending_ack,
                       hwm, invVars, aux_disk_id_gen>>

(* 
    ACTION: HandleRemoveVoterRequest ----------------------------------
    
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

RemoveVoterCheck(s, peer) ==
    (* Enforces the rules above *)
    CASE state[s] # Leader -> NotLeader
      [] peer \notin config[s].members -> UnknownMember
      [] HasPendingConfigCommand(s) -> ReconfigInProgress
      [] ~LeaderHasCommittedOffsetsInCurrentEpoch(s) -> LeaderNotReady
      [] OTHER -> Ok
      
\* ACTION
AcceptRemoveVoterRequest(s) ==
    \* enabling conditions
    /\ aux_ctrs.remove_reconfig_ctr < MaxRemoveReconfigs
    /\ s \in StartedServers 
    /\ \E remove_server \in StartedServers :
        /\ RemoveVoterCheck(s, remove_server) = Ok
        /\ LIVENESS_RemoveVoterLivenessCondition(s, remove_server)
        /\ Cardinality(config[s].members) > MinClusterSize
        \* state mutations
        /\ LET entry      == [command |-> RemoveVoterCommand,
                              epoch   |-> current_epoch[s],
                              value   |-> [id      |-> config[s].id + 1,
                                           old     |-> remove_server,
                                           members |-> config[s].members \ {remove_server}]]
               new_log    == Append(log[s], entry)
               new_config == ConfigFor(Len(new_log), entry, hwm[s])
           IN  /\ log' = [log EXCEPT ![s] = new_log]
               /\ config' = [config EXCEPT ![s] = new_config]
               /\ UpdateFollowerEndOffsetMap(s, new_config.members)
               /\ aux_ctrs' = [aux_ctrs EXCEPT !.remove_reconfig_ctr = @ + 1]                                 
        /\ UNCHANGED <<server_ids, NetworkVars, candidateVars,  current_epoch, 
                       state, leader, voted_for, fetch_state, 
                       pending_ack, hwm, invVars, aux_disk_id_gen>>  

\*================================================
\* Init and Next
\*================================================

InitServerVars(init_leader, server_identities) ==
    LET servers == DOMAIN server_identities
    IN
        /\ server_ids    = server_identities
        /\ current_epoch = [s \in servers |-> 1]
        /\ state         = [s \in servers |-> IF s = init_leader 
                                              THEN Leader
                                              ELSE Follower]
        /\ leader        = [s \in servers |-> init_leader]
        /\ voted_for     = [s \in servers |-> Nil]
        /\ fetch_state = [s \in servers |-> [pending_fetch     |-> Nil,
                                             last_fetch_res    |-> Nil,
                                             has_fetch_success |-> TRUE]]
        /\ pending_ack   = [s \in servers |-> {}]
        /\ config        = [s \in servers |-> [id        |-> 1,
                                               members   |-> servers,
                                               committed |-> TRUE]]

InitCandidateVars(servers) == 
    votes_recv   = [s \in servers |-> {}]

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
    /\ aux_ctrs = [prevote_ctr         |-> 0,
                   election_ctr        |-> 0,
                   disruptive_ctr      |-> 0,
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
    \/ StartNewServer
    \/ ChangeNetworkConnectivity
    \* Single server actions ---------------------
    \/ \E s \in AllServers :
        \/ RestartWithState(s)
        \/ CrashLoseState(s)
        \* reconfiguration actions ----------------
        \/ AcceptAddVoterRequest(s)
        \/ AcceptRemoveVoterRequest(s)
        \* elections ------------------------------
        \/ VoterFetchTimeout(s)
        \/ VoterElectionTimeout(s)
        \/ ResignedElectionTimeout(s)
        \/ ConcludePreVote(s)
        \/ BecomeLeader(s)
        \* leader actions -------------------------
        \/ HandleClientRequest(s)
        \/ CheckQuorumResign(s)
    \* Message sending/receiving actions
    \/ \E s, peer \in AllServers :    
        \* elections
        \/ HandleVoteRequest(s, peer)
        \/ HandleVoteResponse(s, peer)
        \* follower actions -----------------------
        \/ AcceptBeginQuorumRequest(s, peer)
        \/ SendFetchRequest(s, peer)
        \/ HandleFetchResponse(s, peer)
        \* leader message send/receive ------------     
        \/ ResendBeginQuorumEpochRequest(s, peer)
        \/ RejectFetchRequest(s, peer)
        \/ DivergingFetchRequest(s, peer)
        \/ AcceptFetchRequest(s, peer)

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
        /\ WF_vars(CheckQuorumResign(s))
        /\ WF_vars(VoterFetchTimeout(s))
        /\ WF_vars(VoterElectionTimeout(s))
        /\ WF_vars(ResignedElectionTimeout(s))
        /\ WF_vars(ConcludePreVote(s))
        /\ WF_vars(BecomeLeader(s))
        /\ \A peer \in AllServers :
            /\ WF_vars(HandleVoteRequest(s, peer))
            /\ WF_vars(HandleVoteResponse(s, peer))
            /\ WF_vars(RejectFetchRequest(s, peer))
            /\ WF_vars(DivergingFetchRequest(s, peer))
            /\ WF_vars(AcceptFetchRequest(s, peer))
            /\ WF_vars(ResendBeginQuorumEpochRequest(s, peer))
            /\ WF_vars(AcceptBeginQuorumRequest(s, peer))
            /\ WF_vars(SendFetchRequest(s, peer))
            /\ WF_vars(HandleFetchResponse(s, peer))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

===================================================8