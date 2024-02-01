--------------------------- MODULE kraft_kip_996_properties ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC,
        kraft_kip_996_types,
        kraft_kip_996_functions,
        network

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

\* INV: NoIllegalState
\* If a server enters an illegal state then something went wrong.
\* An IllegalState should not be possible.
NoIllegalState ==
    ~\E i \in StartedServers :
        state[i] = IllegalState

\* INV: NoLogDivergence
\* Each log offset is consistent across all servers (on those
\* servers whose high watermark is equal or higher than the offset).
MinHighWatermark(s1, s2) ==
    IF hwm[s1] < hwm[s2]
    THEN hwm[s1]
    ELSE hwm[s2]

NoLogDivergence ==
    \A s1, s2 \in StartedServers :
        IF s1 = s2
        THEN TRUE
        ELSE
            LET lowest_common_hwm == MinHighWatermark(s1, s2)
            IN IF lowest_common_hwm > 0
               THEN \A offset \in 1..lowest_common_hwm : log[s1][offset] = log[s2][offset]
               ELSE TRUE

\* INV: StatesMatchRoles
\* Ensures that the combination of state and role remains consistent.
StatesMatchRoles ==    
    \A s \in StartedServers :
        /\ role[s] = Observer => state[s] \in ObserverStates
        /\ state[s] = Unattached => leader[s] = Nil

\* INV: NeverTwoLeadersInSameEpoch
\* We cannot have two servers having a conflicting
\* view on who the leader is in the same epoch.

NeverTwoLeadersInSameEpoch ==    
    ~\E s1, s2 \in StartedServers :
        /\ s1 # s2
        /\ leader[s1] # Nil
        /\ leader[s2] # Nil
        /\ leader[s1] # leader[s2]
        /\ current_epoch[s1] = current_epoch[s2]

\* INV: LeaderHasAllAckedValues
\* A non-stale leader cannot be missing an acknowledged value

IsCurrentLeader(s) ==
    /\ state[s] = Leader
    \* and which is the newest leader (aka not stale)
    /\ ~\E s1 \in StartedServers : 
        /\ s1 # s
        /\ current_epoch[s1] > current_epoch[s]

LeaderHasAllAckedValues ==
    \* for every acknowledged value
    \A v \in inv_pos_acked :
        \* there does not exist a server that
        ~\E s \in StartedServers :
            \* is the non-stale current leader
            /\ IsCurrentLeader(s)
            \* and that is missing the value
            /\ ~ValueInServerLog(s, v)

\* INV: AckedValueNotLost
\* An acknowledged value must exist on at least one 
\* live functioning voter server.

AckedValueNotLost ==
    \A v \in inv_pos_acked :
        \E s \in StartedServers :
            /\ role[s] = Voter
            /\ ValueInServerLog(s, v)

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

\* LIVENESS: ReconfigurationCompletes -----------
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
        /\ Quantify(StartedServers, LAMBDA s1 : /\ role[s1] = Voter
                                                /\ leader[s1] = s
                                                /\ s \in config[s1].members) 
              >= MajorityCount(config[s].members)
   
        
EventuallyLeaderElected ==
      ~FunctionalLeaderExists ~> FunctionalLeaderExists      
        
================================================