--------------------------- MODULE kraft_kip_996_properties ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC,
        kraft_kip_996_types,
        kraft_kip_996_functions,
        network

(*
    This file contains all the safety and liveness properties.
*)

\*================================================
\* Invariants (safety properties)
\*================================================

ValueInServerLog(s, v) ==
    \E offset \in DOMAIN log[s] :
        log[s][offset].value = v
        
ValueInServerLogAndCommitted(s, v) ==
    \E offset \in DOMAIN log[s] :
        /\ log[s][offset].value = v
        /\ hwm[s] >= offset

\* INV: NoIllegalState ---------------------------------------------
\* If a server enters an illegal state then something went wrong.
\* An IllegalState should not be possible.
NoIllegalState ==
    ~\E i \in StartedServers :
        state[i] = IllegalState

\* INV: LogMatching ------------------------------------------------
\* Each log offset is consistent across all servers (on those
\* servers whose high watermark is equal or higher than the offset).
MinHighWatermark(s1, s2) ==
    IF hwm[s1] < hwm[s2]
    THEN hwm[s1]
    ELSE hwm[s2]

LogMatching ==
    \A s1, s2 \in StartedServers :
        IF s1 = s2
        THEN TRUE
        ELSE
            LET lowest_common_hwm == MinHighWatermark(s1, s2)
            IN IF lowest_common_hwm > 0
               THEN \A offset \in 1..lowest_common_hwm : log[s1][offset] = log[s2][offset]
               ELSE TRUE

\* INV: ElectionSafety ----------------------------------------
\* We cannot have two servers having a conflicting
\* view on who the leader is in the same epoch.

ElectionSafety ==    
    ~\E s1, s2 \in StartedServers :
        /\ s1 # s2
        /\ leader[s1] # Nil
        /\ leader[s2] # Nil
        /\ leader[s1] # leader[s2]
        /\ current_epoch[s1] = current_epoch[s2]

\* INV: LeaderCompleteness -----------------------------------------------
\* A non-stale leader cannot be missing a committed value

IsCurrentLeader(s) ==
    /\ state[s] = Leader
    \* and which is the newest leader (aka not stale)
    /\ ~\E s1 \in StartedServers : 
        /\ s1 # s
        /\ current_epoch[s1] > current_epoch[s]

LeaderCompleteness ==
    \* for every acknowledged value (committed in a prior or current epoch)
    \A v \in inv_pos_acked :
        \* there does not exist a server that
        ~\E s \in StartedServers :
            \* is the non-stale current leader
            /\ IsCurrentLeader(s)
            \* and that is missing the value
            /\ ~ValueInServerLog(s, v)

\* INV: Durability -------------------------------------------------
\* An acknowledged value must exist on at least one 
\* live functioning voter server.
Durability ==
    \A v \in inv_pos_acked :
        \E s \in StartedServers :
            /\ IsVoter(s)
            /\ ValueInServerLog(s, v)
            
\* INV: ValidRolesAndStates -----------------------------------------
\* Ensures that the combination of state and role remains consistent.
ValidRolesAndStates ==    
    \A s \in StartedServers :
        /\ IsObserver(s) => state[s] \in ObserverStates
        /\ state[s] = Unattached => leader[s] = Nil
        /\ state[s] # Leader => pending_ack[s] = {}
        /\ Cardinality(votes_recv[s]) > 0 => state[s] \in {Prospective, Candidate}

\* INV: Used in debugging
TestInv ==
    TRUE

\*================================================
\* Liveness properties
\*================================================

\* LIVENESS: ValuesEventuallyAcked -----------------
\* A client value will eventually get positively or negatively
\* acknowledged. Detects a value that gets stuck.

ValuesEventuallyAcked ==
    \A v \in Value :
        (v \in inv_sent) ~> (\/ /\ v \in inv_neg_acked
                                /\ v \notin inv_pos_acked
                             \/ /\ v \in inv_pos_acked
                                /\ v \notin inv_neg_acked)

\* LIVENESS: ReconfigurationNotStuck -----------
\* A reconfiguration command will either get committed and be
\* fully replicated or it will be truncated and not be found on
\* any (connected/alive) server log. Detects a reconfiguration
\* that gets stuck.

ConfigNotInServerLog(s, config_id) ==
    ~\E offset \in DOMAIN log[s] :
        /\ IsConfigCommand(log[s], offset)
        /\ log[s][offset].value.id = config_id

ConfigInServerLogAndCommitted(s, config_id) ==
    \E offset \in DOMAIN log[s] :
        /\ IsConfigCommand(log[s], offset)
        /\ log[s][offset].value.id = config_id
        /\ hwm[s] >= offset

ConfigAllOrNothing(config_id) ==
    \E s \in StartedServers : 
        /\ IsCurrentLeader(s)
        /\ \/ \A s1 \in config[s].members : 
                \/ ConfigInServerLogAndCommitted(s, config_id)
                \/ ~Connected(s, s1)
                \/ state[s1] = DeadNoState
           \/ \A s1 \in config[s].members : 
                \/ ConfigNotInServerLog(s, config_id)
                \/ ~Connected(s, s1)
                \/ state[s1] = DeadNoState

ReconfigurationNotStuck ==
    \A config_id \in 1..(MaxAddReconfigs + MaxRemoveReconfigs) :
        []<>ConfigAllOrNothing(config_id)

\* LIVENESS: EventuallyLeaderElected -----------
\* If a state is reached where there is no functional leader,
\* then this state will lead to a state where a functional
\* leader does exist. Detects a cluster that gets stuck
\* due to being unable to elect a leader.
    
FunctionalLeaderExists ==
    \E s \in StartedServers : 
        /\ state[s] = Leader
        /\ Quantify(StartedServers, LAMBDA s1 : /\ IsVoter(s1)
                                                /\ leader[s1] = s
                                                /\ s \in config[s1].members) 
              >= MajorityCount(config[s].members)
   
        
EventuallyLeaderElected ==
      ~FunctionalLeaderExists ~> FunctionalLeaderExists
      
\* LIVENESS: NotStuckInProspective
\* A server will not remain in prospective forever, unless
\* it is completely cut-off from all non-prospective servers.
\* Prospectives will be unable to inform the server of the
\* leader and so a server that is disconnected from the leader
\* and all other non-prospectives will be stuck in Prospective
\* state.

IsProspective(s) ==
    /\ s \in DOMAIN state
    /\ state[s] = Prospective

NotStuckInProspective ==
    \A s \in AllServers :
        IsProspective(s) ~> (\/ ~IsProspective(s)
                             \/ ~\E s1 \in config[s].members :
                                 /\ s # s1
                                 /\ state[s1] # Prospective
                                 /\ Connected(s, s1))
        
================================================