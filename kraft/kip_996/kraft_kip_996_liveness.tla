----------------------- MODULE kraft_kip_996_liveness -----------------------

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC,
        kraft_kip_996_types, 
        kraft_kip_996_functions,
        network

(*
    NOTE! This file does not model the KRaft protocol (most people can ignore this).
    
    This file contains a set of functions used for constraining the
    spec to avoid cycles and to avoid actions that would prevent
    the cluster from making progress (such as all servers losing
    connectivity to each other). Only relevant when testing liveness.
*)

HasMajorityConnectionToMembers(s, connected) ==
    Quantify(config[s].members, LAMBDA m :
                /\ s # m
                /\ current_epoch[s] >= current_epoch[m]
                /\ state[m] # DeadNoState
                /\ \E pair \in connected :
                    /\ s \in pair
                    /\ m \in pair) >= (Cardinality(config[s].members) \div 2)

LIVENESS_ElectionsCanProgress(connected) ==
    IF TestLiveness
    THEN
         \E s \in StartedServers :
            /\ state[s] # DeadNoState
            /\ IsVoter(s)
            /\ HasMajorityConnectionToMembers(s, connected)
    ELSE TRUE

\* Constrain the spec to choose a broker that knows who the leader
\* is to avoid cycle where only brokers who don't know who the leader
\* is are chosen.
LIVENESS_ValidPeer(s, peer) ==
    IF TestLiveness
    THEN
            /\ IsVoter(peer)
            /\ leader[peer] # Nil
            /\ Connected(s, peer)
    ELSE TRUE
    
\* Constrain the spec to not send fetches that do not help make progress
\* (state space reduction). 
LIVENESS_HelpsMakeProgress(s, peer, fetch_offset) ==
    IF TestLiveness
    THEN
            \* The log of the follower does not match the leader
            \/ log[s] # log[peer] 
            \* The HWM of the follower does not match the leader
            \/ hwm[s] # hwm[peer] 
            \* The leader has no knowledge of or has a stale fetch offset for this follower
            \/ /\ state[peer] = Leader
               /\ IF s \in DOMAIN flwr_end_offset[peer]
                  THEN flwr_end_offset[peer][s] < fetch_offset \* stale fetch offset
                  ELSE TRUE \* the leader doesn't know of this observer yet 
            \* The supposed leader is on a different epoch
            \/ current_epoch[s] # current_epoch[peer] 
            \* The supposed leader isn't even a leader
            \/ state[peer] # Leader
    ELSE TRUE

\* Detects if we're in a cycle of FetchTimeout->PreVote->Follower->FetchTimeout
\* caused by losing connectivity to the leader where peers still have connectivity to it.
LIVENESS_InPrevoteCycle(s, ldr) ==
    IF TestLiveness
    THEN
            /\ IsVoter(s)
            /\ ~Connected(s, ldr)
            /\ \E m \in net_messages_processed :
                /\ m.type = RequestVoteResponse
                /\ m.pre_vote = TRUE
                /\ m.vote_granted = FALSE
                /\ m.leader = ldr
                /\ m.replica_epoch = current_epoch[s]
                /\ m.dest = s
                /\ Connected(m.source, ldr)
    ELSE FALSE
    
LIVENESS_MaybeNotSamePeerAgain(s, peer) ==
    IF TestLiveness
    THEN
            IF /\ fetch_state[s].last_fetch_res # Nil
               /\ fetch_state[s].last_fetch_res.error = NotLeader
            THEN fetch_state[s].last_fetch_res.peer # peer
            ELSE TRUE
    ELSE TRUE
    
    
LIVENESS_AddVoterLivenessCondition(s, add_server) ==
    (* When testing liveness, don't add a server such that it causes
       the leader to lose a functioning majority. For example, the add
       server already crashed, and with only 2 live members out of 4,
       and this server having the largest log, only it can get elected
       but also it doesn't have a majority, so the cluster gets stuck. *)
    IF TestLiveness = TRUE
    THEN LET new_member_count == Cardinality(config[s].members) + 1
             connected_members == NumConnections(s, config[s].members) + 1
             add_connected     == IF Connected(s, add_server)
                                  THEN 1 ELSE 0
         IN (connected_members + add_connected)
                > (new_member_count \div 2)
    ELSE TRUE
    
LIVENESS_RemoveVoterLivenessCondition(s, remove_server) ==
    (* When testing liveness, don't remove a voter if that would
       result in the leader losing a majority and getting stuck. *)
    IF TestLiveness = TRUE
    THEN Quantify(config[s].members, LAMBDA peer :
            /\ peer # remove_server         \* not remove_server
            /\ IsVoter(peer)
            /\ Connected(s, peer))          \* the two are connected
                > Cardinality(config[s].members) \div 2
    ELSE TRUE       

=============================================================================
