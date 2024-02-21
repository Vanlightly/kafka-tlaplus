--------------------------------- MODULE kraft_kip_996 ---------------------------------
(*NOTES
Author: Jack Vanlightly

-----------------------------------------------
Kafka KRaft TLA+ specification with KIP-996 Pre-Vote
-----------------------------------------------

This specification is based on the KIP-853 (reconfiguration) specification.
See the readme for the KIP-853 spec, as well as the readme for this spec
for more discussion of the design and the specification itself.
*)

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC,
        kraft_kip_996_types, 
        kraft_kip_996_functions,
        kraft_kip_996_properties,
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
    /\ LET new_state == CASE /\ state[s] = Leader 
                             /\ role[s] = Voter -> 
                                    TransitionToResigned(s)
                          [] /\ state[s] = Leader 
                             /\ role[s] = Observer -> 
                                    TransitionToUnattached(s,
                                        current_epoch[s],
                                        role[s])
                          [] OTHER ->
                                    NoTransition(s)
      IN
         /\ ApplyState(s, new_state)
         /\ hwm' = [hwm EXCEPT ![s] = 0]
         /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
         /\ ResetFollowerEndOffsetMap(s, DOMAIN flwr_end_offset[s])
         /\ FailPendingWrites(s)
         /\ aux_ctrs' = [aux_ctrs EXCEPT !.restart_ctr = @ + 1]
         /\ UNCHANGED <<server_ids, NetworkVars, config, role, 
                        log, aux_disk_id_gen>>

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

CrashLoseState(s) ==
    \* enabling conditions
    /\ aux_ctrs.crash_ctr < MaxCrashes
    /\ s \in StartedServers
    /\ role[s] = Voter
    \* state mutations
    /\ DisconnectDeadServer(s)
    /\ state' = [state EXCEPT ![s] = DeadNoState]
    /\ config' = [config EXCEPT ![s] = NoConfig]
    /\ role' = [role EXCEPT ![s] = Nil]    
    /\ current_epoch' = [current_epoch EXCEPT ![s] = 0]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ voted_for' = [voted_for EXCEPT ![s] = Nil]
    /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil] 
    /\ votes_recv' = [votes_recv EXCEPT ![s] = {}]
    /\ ResetFollowerEndOffsetMap(s, {})
    /\ log' = [log EXCEPT ![s] = <<>>]
    /\ hwm' = [hwm EXCEPT ![s] = 0]
    /\ FailPendingWrites(s)
    /\ aux_ctrs' = [aux_ctrs EXCEPT !.crash_ctr = @ + 1]
    /\ UNCHANGED <<aux_disk_id_gen, server_ids, aux_disk_id_gen>>

(* 
    ACTION: CheckQuorumResign -------------------------------------
    Server (s) is a leader but resigns because it cannot receive 
    fetch requests from enough followers to consitute a functional
    majority. This happens either due to enough followers being
    disconnected or no longer believing this server is the leader.
    
    This is only enabled when checking liveness.
*)
CheckQuorumResign(s) ==
    /\ s \in StartedServers
    /\ state[s] = Leader
    /\ LET connected_peers == Quantify(config[s].members, LAMBDA peer :
                                        /\ s # peer
                                        /\ Connected(s, peer)
                                        /\ \/ /\ role[peer] = Voter
                                              /\ current_epoch[s] >= current_epoch[peer]
                                           \/ role[peer] = Observer)
           min_connected == Cardinality(config[s].members) \div 2
           new_state     == IF role[s] = Voter
                            THEN TransitionToResigned(s)
                            ELSE TransitionToUnattached(s, current_epoch[s], Observer)
       IN /\ \/ /\ TestLiveness = TRUE
                /\ connected_peers < min_connected
             \/ TestLiveness = FALSE
          /\ ApplyState(s, new_state)
    /\ UNCHANGED <<NetworkVars, server_ids, role, config, current_epoch,
                   pending_fetch, pending_ack, invVars, leaderVars,
                   logVars, auxVars>>

(*
    ACTION: VoterElectionTimeout -----------------------------------------------
    Server (s) is a voter and not the leader, and experiences
    an fetch time out or directly an election timeout. This action
    is used for both cases.
    
    The server sends a pre-vote RequestVote request to all peers in
    its configuration but not itself. It adds itself to its received
    votes set.

    When checking liveness, the election timeout can only happen
    for a reason, such as being a follower that is disconnected
    from the leader, a prospective/candidate that couldn't get
    enough votes, or being unattached.
        
    When only checking safety, an election timeout can happen at
    any time.
*)
NotEnoughVotes(s, pre_vote) ==
    /\ ~HasInflightVoteReq(s, RequestVoteRequest, pre_vote)
    /\ ~HasInflightVoteRes(s, RequestVoteResponse, pre_vote)
    /\ Cardinality(votes_recv[s]) < MajorityCount(config[s].members)
    /\ state[s] # Leader
    
ValidTimeout(s) ==
    IF TestLiveness
    THEN /\ \* 1) The server is a follower which it either cut-off from
            \* the leader or the leader has perished.
            \/ /\ state[s] = Follower
               /\ \/ ~Connected(s, leader[s])
                  \/ state[leader[s]] # Leader
            \* 2) The server is a candidate and has lost connectivity such that
            \*    it cannot form a majority.
            \/ /\ state[s] = Candidate
               /\ NotEnoughVotes(s, FALSE)
            \* 3) The server has voted and the voted for server has lost connectivity
            \*    such that it cannot form a majority.
            \/ /\ state[s] = Voted
               /\ NotEnoughVotes(voted_for[s], FALSE)
            \* 4) The server is a prospective, hasn't reached a majority and no more
            \*    replies are coming in.
            \/ /\ state[s] = Prospective
               /\ NotEnoughVotes(s, TRUE)
            \* 5) The server is unattached or resigned.
            \/ state[s] \in {Unattached, Resigned}
    ELSE state[s] \in {Follower, Candidate, Unattached, 
                       Voted, Prospective, Resigned}

VoterElectionTimeout(s) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ role[s] = Voter
    /\ s \in config[s].members
    /\ ValidTimeout(s)
    \* state mutations
    /\ ApplyState(s, TransitionToProspective(s))
    /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
    /\ SendAll(
            {[type            |-> RequestVoteRequest,
              epoch           |-> current_epoch[s],
              last_log_epoch  |-> LastEpoch(log[s]),
              last_log_offset |-> Len(log[s]),
              pre_vote        |-> TRUE,
              source          |-> s,
              dest            |-> s1] : s1 \in config[s].members \ {s}})
    /\ UNCHANGED <<server_ids, config, role, pending_ack, 
                   flwr_end_offset, logVars, invVars, auxVars>>
                   

(*
    ACTION: ObserverFetchTimeout -----------------------------------------------
    Server (s) is an observer, and experiences a fetch time out.

    When checking liveness, the fetch timeout can only happen
    for a reason, such as being disconnected from the leader
    or the leader failing/losing leadership.
        
    When only checking safety, a fetch timeout can happen at
    any time.
*)

ValidObserverTimeout(s) ==
    IF TestLiveness
    THEN LET peer == pending_fetch[s].dest
         IN ~Connected(s, peer)
    ELSE TRUE

ObserverFetchTimeout(s) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ role[s] = Observer
    /\ pending_fetch[s] # Nil
    /\ ValidObserverTimeout(s)
    \* state mutations
    /\ ApplyState(s, TransitionToUnattached(s, current_epoch[s], role[s]))
    /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
    /\ UNCHANGED <<server_ids, config, role, pending_ack, flwr_end_offset, 
                   logVars, invVars, auxVars, NetworkVars>>                   

(* 
    ACTION: HandleRequestPreVoteRequest ------------------------------
    Server (s0) receives a pre-vote RequestVote message. 
    While this server may be an Observer and therefore believe 
    it is not a member of a configuration, it may in fact be 
    so (but be lagging) and may be required to process the message
    in order for an election to complete. In other words, if
    an observer ignores pre-vote RequestVote messages it may cause a cluster
    to get stuck. CHECK THIS IS STILL TRUE.

    Server (s) will vote for its peer if all the following are true:
    1) epoch of (peer) >= epoch of (s)
    2) the last entry of (s) is <= to the last entry of (peer)
*)

ExpiredFetchResponseTime(s) ==
    IF TestLiveness
    THEN CASE leader[s] = Nil -> TRUE
           [] \/ ~Connected(s, leader[s])
              \/ state[leader[s]] # Leader -> TRUE
           [] OTHER -> FALSE
    ELSE FALSE

HandlePreVoteRequest(s) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, RequestVoteRequest, AnyEpoch)
        /\ m.pre_vote = TRUE
        /\ s = m.dest
        /\ LET peer     == m.source
               error    == IF m.epoch < current_epoch[s]
                           THEN FencedLeaderEpoch
                           ELSE Nil
               state0   == IF m.epoch > current_epoch[s]
                           THEN TransitionToUnattached(s, m.epoch, role[s])
                           ELSE NoTransition(s)
               log_ok == CompareEntries(m.last_log_offset,
                                        m.last_log_epoch,
                                        Len(log[s]),
                                        LastEpoch(log[s])) >= 0
               grant == \* /\ state0.state # Follower TODO!!
                        /\ ExpiredFetchResponseTime(s)
                        /\ log_ok
            IN \* state mutations
               /\ ApplyState(s, state0)
               /\ IF error = Nil
                  THEN Reply(m, [type         |-> RequestVoteResponse,
                                 epoch        |-> m.epoch,
                                 leader       |-> IF grant THEN Nil \* KIP-996 TODO!!
                                                  ELSE state0.leader,
                                 vote_granted |-> grant,
                                 pre_vote     |-> TRUE,
                                 error        |-> Nil,
                                 source       |-> s,
                                 dest         |-> peer])
                  ELSE Reply(m, [type         |-> RequestVoteResponse,
                                 epoch        |-> current_epoch[s],
                                 leader       |-> state0.leader,
                                 vote_granted |-> FALSE,
                                 pre_vote     |-> TRUE,
                                 error        |-> error,
                                 source       |-> s,
                                 dest         |-> peer])
        /\ UNCHANGED <<server_ids, role, config, pending_fetch, pending_ack,
                       invVars, leaderVars, logVars, auxVars>>

(* 
    ACTION: HandleRequestPreVoteResponse --------------------------------
    Server (s) receives a pre-vote RequestVote reponse.
    The server would normally be a prospective, but it could
    have already transitioned to a different state or epoch.
    If the response is stale it will be ignored.
*)
HandlePreVoteResponse(s) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, RequestVoteResponse, AnyEpoch)
        /\ m.pre_vote = TRUE
        /\ s = m.dest
        /\ role[s] = Voter \* new check because roles can change with reconfigurations
        \* state mutations
        /\ LET peer == m.source
               state0 == MaybeHandleCommonResponse(s, m.leader, m.epoch, m.error)
               state1 == IF /\ state0.handled = FALSE
                            /\ state[s] = Prospective
                            /\ m.vote_granted
                         THEN [state0 EXCEPT !.votes_recv = @ \union {peer}]
                         ELSE state0
           IN /\ ApplyState(s, state1)
              /\ Discard(m)
              /\ UNCHANGED <<server_ids, config, role, pending_fetch, 
                             pending_ack, leaderVars, logVars, invVars, auxVars>> 

(*
    ACTION: RequestVote -----------------------------------------------
    Server (s) is a voter and prospective. It has received a
    pre-vote from a majority and initiates an election.

    When testing safety only, there is an artificial limit on the
    epoch in order to prevent an infinite state space.

    When testing liveness, this limit is not used else liveness
    checking will be impacted. An election may be required for
    a cluster to make progress and thus limiting the number of
    elections can cause liveness properties to be violated. This
    results in an infinite state space and therefore liveness
    check should be carried out using simulation, not brute-force.
*)

WithinEpochLimit(s) ==
    IF TestLiveness
    THEN TRUE
    ELSE current_epoch[s] < MaxEpoch

RequestVote(s) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ role[s] = Voter
    /\ state[s] = Prospective
    /\ WithinEpochLimit(s)
    /\ s \in config[s].members
    /\ votes_recv[s] \in Quorum(config[s].members)
    \* state mutations
    /\ LET new_state == TransitionToCandidate(s)
       IN /\ ApplyState(s, new_state)
          /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
          /\ SendAll(
                  {[type            |-> RequestVoteRequest,
                    epoch           |-> new_state.epoch,
                    last_log_epoch  |-> LastEpoch(log[s]),
                    last_log_offset |-> Len(log[s]),
                    pre_vote        |-> FALSE,  
                    source          |-> s,
                    dest            |-> s1] : s1 \in config[s].members \ {s}})
    /\ UNCHANGED <<server_ids, config, role, pending_ack, leaderVars, logVars,
                   invVars, auxVars>>

(* 
    ACTION: HandleRequestVoteRequest ------------------------------
    Server (s0) receives a standard RequestVote message. 
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
HandleStandardVoteRequest(s) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, RequestVoteRequest, AnyEpoch)
        /\ m.pre_vote = FALSE
        /\ s = m.dest
        /\ LET peer     == m.source
               error    == IF m.epoch < current_epoch[s]
                           THEN FencedLeaderEpoch
                           ELSE Nil
               state0   == IF m.epoch > current_epoch[s]
                           THEN TransitionToUnattached(s, m.epoch, role[s])
                           ELSE NoTransition(s)
               log_ok == CompareEntries(m.last_log_offset,
                                        m.last_log_epoch,
                                        Len(log[s]),
                                        LastEpoch(log[s])) >= 0
               grant_vote == /\ \/ state0.state = Unattached
                                \/ /\ state0.state = Voted
                                   /\ voted_for[s] = peer
                             /\ log_ok
               final_state == IF grant_vote /\ state0.state = Unattached
                              THEN TransitionToVoted(m.epoch, state0, peer)
                              ELSE state0                         
            IN \* state mutations
               /\ ApplyState(s, final_state)
               /\ IF error = Nil
                  THEN
                       \* if a follower changed state then clear pending_fetch
                       \* if a leader changed state, then fail any pending writes
                       /\ IF state # state'
                          THEN /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
                               /\ FailPendingWrites(s)
                          ELSE UNCHANGED << pending_fetch, pending_ack, invVars >>
                       /\ Reply(m, [type         |-> RequestVoteResponse,
                                    epoch        |-> m.epoch,
                                    leader       |-> final_state.leader,
                                    vote_granted |-> grant_vote,
                                    pre_vote     |-> FALSE,
                                    error        |-> Nil,
                                    source       |-> s,
                                    dest         |-> peer])
                  ELSE /\ Reply(m, [type         |-> RequestVoteResponse,
                                    epoch        |-> current_epoch[s],
                                    leader       |-> final_state.leader,
                                    vote_granted |-> FALSE,
                                    pre_vote     |-> FALSE,
                                    error        |-> error,
                                    source       |-> s,
                                    dest         |-> peer])
                       /\ UNCHANGED << pending_fetch, pending_ack, invVars>>
               /\ UNCHANGED <<server_ids, role, config, leaderVars, logVars, auxVars>>

(* 
    ACTION: HandleRequestVoteResponse --------------------------------
    Server (s) receives a RequestVote reponse.
    The server would normally be a candidate, but it could
    have already transitioned to a different state or epoch.
    If the response is stale it will be ignored. It is stale if
    - the server is not a Candidate anymore
    - the request epoch is lower than the server epoch.
*)
HandleStandardVoteResponse(s) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, RequestVoteResponse, AnyEpoch)
        /\ m.pre_vote = FALSE
        /\ s = m.dest
        /\ role[s] = Voter \* new check because roles can change with reconfigurations
        \* state mutations
        /\ LET peer == m.source
               state0 == MaybeHandleCommonResponse(s, m.leader, m.epoch, m.error)
               state1 == IF /\ state0.handled = FALSE
                            /\ state[s] = Candidate
                            /\ m.vote_granted
                         THEN [state0 EXCEPT !.votes_recv = @ \union {peer}]
                         ELSE state0
           IN /\ ApplyState(s, state1)
              /\ Discard(m)
              /\ UNCHANGED <<server_ids, config, role, pending_fetch, 
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
          /\ ResetFollowerEndOffsetMap(s, config[s].members)
          /\ SendAllOnce(
                  {[type    |-> BeginQuorumRequest,
                    epoch   |-> current_epoch[s],
                    source  |-> s,
                    dest    |-> peer] : peer \in config[s].members \ {s}})
          /\ UNCHANGED <<server_ids, config, role, pending_fetch, pending_ack, 
                         hwm, invVars, auxVars>>

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
               new_state == MaybeTransition(s, peer, m.epoch)
           IN /\ error = Nil
              \* state mutations
              /\ ApplyState(s, new_state)
              /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
              /\ FailPendingWrites(s)
              /\ Discard(m)
        /\ UNCHANGED <<server_ids, config, role, logVars, leaderVars, auxVars>>

(* 
    ACTION: ClientRequest ----------------------------------
    A client sends a write request to server (s) which is
    a leader. 
    
    TODO: Discuss merits of allowing a leader that is an
          observer to accept writes. Doing so will be better
          for availability and still be safe. A leader can 
          be an observer during a reconfiguration.
*)

WithinValuesPerEpochLimit(s, v) ==
    (* State space limit trick*)
    Quantify(DOMAIN log[s], LAMBDA offset : 
                        log[s][offset].epoch = current_epoch[s])
        < MaxValuesPerEpoch

ClientRequest(s) ==
    \* enabling conditions
    \E v \in Value : 
        /\ s \in StartedServers
        /\ state[s] = Leader
        /\ v \notin inv_sent \* prevent submitting the same value repeatedly
        /\ WithinValuesPerEpochLimit(s, v)
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
        /\ UNCHANGED <<server_ids, config, current_epoch, role, state, voted_for, 
                       leader, pending_fetch, NetworkVars, candidateVars,
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
SendFetchRequest(s) ==
    \* enabling conditions
    /\ s \in StartedServers
    /\ \E peer \in StartedServers : 
        /\ s # peer
        /\ pending_fetch[s] = Nil
        /\ \* either the follower (voter or observer) knows who the 
           \* leader is and can send a fetch request to the leader
           \/ /\ leader[s] = peer
              /\ state[s] = Follower
           \* or we're an observer that doesn't know who the leader 
           \* is (either unattached or voted) and picks a random voter to
           \* fetch from, knowing that if it isn't the leader, it will
           \* include the leader id in its response if it knows.
           \/ /\ role[s] = Observer
              /\ state[s] \in {Unattached, Voted}
              /\ Connected(s, peer)
              \* CHEATING, to prevent a cycle of always sending it to a 
              \* server that is not the leader and doesn't know who the
              \* leader is, choose a voter that does know. 
              \* In reality, who this server sends a fetch request
              \* to is governed by a voter set in configuration. This spec
              \* assumes that the server is given the set of voters it can
              \* send its first fetch to.
              /\ role[peer] = Voter
              /\ leader[peer] # Nil
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
               diverging_offset   == valid_offset_epoch.offset + 1
           IN  /\ state[s] = Leader
               /\ ~valid_position 
               \* state mutations
               /\ Reply(m, [type                 |-> FetchResponse,
                            epoch                |-> current_epoch[s],
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
                     values_to_ack  == pending_ack[s] \intersect committed_values
                     new_config     == ConfigFor(config_entry.offset, 
                                                 config_entry.entry, 
                                                 new_hwm)
                     leave_state    == TransitionToUnattached(s, current_epoch[s], Observer)
                 IN
                    /\ IF new_hwm > hwm[s]
                       THEN /\ config' = [config EXCEPT ![s] = new_config]
                            /\ inv_pos_acked' = inv_pos_acked \union values_to_ack
                            /\ pending_ack' = [pending_ack EXCEPT ![s] = @ \ values_to_ack]
                            /\ IF leaves
                               THEN \* the server resigns and becomes an unattached observer
                                    /\ role' = [role EXCEPT ![s] = Observer]
                                    /\ ApplyState(s, leave_state)
                                    /\ ResetFollowerEndOffsetMap(s, {})
                                    /\ hwm' = [hwm EXCEPT ![s] = 0]
                               ELSE \* the end offset of the peer is updated, but we may also have switched
                                    \* to a new configuration which may include a new member to track
                                    /\ flwr_end_offset' = [flwr_end_offset EXCEPT ![s] = 
                                                                \* a new map of this configuration, maintain values
                                                                \* of existing members, set 0 for new members
                                                                [s1 \in new_config.members |->
                                                                    IF s1 \in DOMAIN new_end_offset
                                                                    THEN new_end_offset[s1]
                                                                    ELSE 0]]
                                    /\ hwm' = [hwm EXCEPT ![s] = new_hwm]
                                    /\ UNCHANGED <<role, state, leader, current_epoch, votes_recv, voted_for>>
                       ELSE /\ flwr_end_offset' = [flwr_end_offset EXCEPT ![s] = new_end_offset]
                            /\ UNCHANGED <<role, config, state, leader, current_epoch, votes_recv, 
                                           voted_for, pending_ack, hwm, invVars>>
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
                    /\ UNCHANGED <<server_ids, log, pending_fetch, inv_sent, 
                                   inv_neg_acked, aux_ctrs, aux_disk_id_gen>>

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
       
(* ACTION: HandleFetchResponse ------------------------
   
   A server receives a FetchResponse, and the response
   may indicate success, failure or a diverging epoch.
   
   In the case of a successful response, the server appends
   an records to its log. The new entries may include a 
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

HandleFetchResponse(s) ==
    \* enabling conditions
    \E m \in Messages :
        /\ ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ s = m.dest
        /\ LET new_state    == MaybeHandleCommonResponse(s, m.leader, m.epoch, m.error)
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
           IN /\ pending_fetch[s] = m.correlation
              /\ IF \/ new_state.handled = TRUE
                    \/ state[s] # Follower
                 THEN /\ ApplyState(s, new_state)
                      /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
                      /\ UNCHANGED << role, log, hwm, config, flwr_end_offset >>
                 ELSE /\ MaybeSwitchConfigurations(s, curr_config, new_state)
                      /\ pending_fetch' = [pending_fetch EXCEPT ![s] = Nil]
                      /\ log' = new_log
                      /\ IF m.result = Ok
                         THEN hwm' = [hwm  EXCEPT ![s] = m.hwm]
                         ELSE UNCHANGED hwm
                      /\ UNCHANGED voted_for
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
        LET new_server  == Max(StartedServers) + 1
            disk_id     == aux_disk_id_gen + 1
            identity    == [host |-> host, disk_id |-> disk_id]
            init_config == config[anyLeader] \* start the server with the current config
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
                 /\ config' = config @@ (new_server :> init_config)
                 /\ role' = role @@ (new_server :> Observer)    
                 /\ state' = state @@ (new_server :> Unattached)
                 /\ current_epoch' = current_epoch @@ (new_server :> 0)
                 /\ leader' = leader @@ (new_server :> Nil)
                 /\ voted_for' = voted_for @@ (new_server :> Nil)
                 /\ pending_fetch' = pending_fetch @@ (new_server :> fetch_msg) 
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
      
AddVoterLivenessCondition(s, add_server) ==
    (* When testing liveness, don't add a server such that it causes
       the leader to lose a functioning majority. For example, the add
       server already crashed, and with only 2 live members out of 4,
       and this server having the largest log, only it can get elected
       but also it doesn't have a majority, so the cluster gets stuck. *)
    IF TestLiveness = TRUE
    THEN LET new_member_count == Cardinality(config[s].members) + 1
             connected_members == ConnectedServers(s, config[s].members)
             add_connected     == IF Connected(s, add_server)
                                  THEN 1 ELSE 0
         IN (connected_members + add_connected)
                > (new_member_count \div 2)
    ELSE TRUE  

AcceptAddVoterRequest(s) ==
    \* enabling conditions
    /\ aux_ctrs.add_reconfig_ctr < MaxAddReconfigs
    /\ s \in StartedServers
    /\ \E add_server \in StartedServers :
        /\ AddVoterCheck(s, add_server) = Ok
        /\ AddVoterLivenessCondition(s, add_server)
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
               /\ Send([type    |-> BeginQuorumRequest,
                        epoch   |-> current_epoch[s],
                        source  |-> s,
                        dest    |-> add_server])
        /\ aux_ctrs' = [aux_ctrs EXCEPT !.add_reconfig_ctr = @ + 1]
        /\ UNCHANGED <<server_ids, candidateVars, role, current_epoch, state, 
                       leader, voted_for, pending_fetch, pending_ack,
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
      
RemoveVoterLivenessCondition(s, remove_server) ==
    (* When testing liveness, don't remove a voter if that would
       result in the leader losing a majority and getting stuck. *)
    IF TestLiveness = TRUE
    THEN Quantify(config[s].members, LAMBDA peer :
            /\ peer # remove_server         \* not remove_server
            /\ role[peer] = Voter           \* is a functioning voter
            /\ Connected(s, peer))          \* the two are connected
                > Cardinality(config[s].members) \div 2
    ELSE TRUE      

AcceptRemoveVoterRequest(s) ==
    \* enabling conditions
    /\ aux_ctrs.remove_reconfig_ctr < MaxRemoveReconfigs
    /\ s \in StartedServers 
    /\ \E remove_server \in StartedServers :
        /\ RemoveVoterCheck(s, remove_server) = Ok
        /\ RemoveVoterLivenessCondition(s, remove_server)
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
               /\ IF s = remove_server
                  THEN role' = [role EXCEPT ![s] = Observer]
                  ELSE UNCHANGED role
               /\ aux_ctrs' = [aux_ctrs EXCEPT !.remove_reconfig_ctr = @ + 1]                                 
        /\ UNCHANGED <<server_ids, NetworkVars, candidateVars,  current_epoch, 
                       state, leader, voted_for, pending_fetch, pending_ack,
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
    /\ aux_ctrs = [election_ctr        |-> 0,
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
        \/ AcceptAddVoterRequest(s)
        \/ AcceptRemoveVoterRequest(s)
        \* elections ------------------------------
        \/ VoterElectionTimeout(s)
        \/ HandlePreVoteRequest(s)
        \/ HandlePreVoteResponse(s)
        \/ RequestVote(s)
        \/ HandleStandardVoteRequest(s)
        \/ HandleStandardVoteResponse(s)
        \/ BecomeLeader(s)
        \* follower actions -----------------------
        \/ AcceptBeginQuorumRequest(s)
        \/ SendFetchRequest(s)
        \/ HandleFetchResponse(s)
        \/ ObserverFetchTimeout(s)
        \* leader actions -------------------------
        \/ ClientRequest(s)
        \/ CheckQuorumResign(s)
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
        /\ WF_vars(CheckQuorumResign(s))
        /\ WF_vars(VoterElectionTimeout(s))
        /\ WF_vars(ObserverFetchTimeout(s))
        /\ WF_vars(HandlePreVoteRequest(s))
        /\ WF_vars(HandlePreVoteResponse(s))
        /\ WF_vars(RequestVote(s))
        /\ WF_vars(HandleStandardVoteRequest(s))
        /\ WF_vars(HandleStandardVoteResponse(s))
        /\ WF_vars(BecomeLeader(s))
        /\ WF_vars(AcceptBeginQuorumRequest(s))
        /\ WF_vars(SendFetchRequest(s))
        /\ WF_vars(HandleFetchResponse(s))
        /\ \A peer \in AllServers :
            /\ WF_vars(RejectFetchRequest(s, peer))
            /\ WF_vars(DivergingFetchRequest(s, peer))
            /\ WF_vars(AcceptFetchRequestFromVoter(s, peer))
            /\ WF_vars(AcceptFetchRequestFromObserver(s, peer))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

===================================================