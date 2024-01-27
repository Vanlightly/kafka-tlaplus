--------------------------- MODULE kraft_kip_853_properties ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC,
        kraft_kip_853_types,
        kraft_kip_853_functions,
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
\* Ensures that the combination of state and role remains consistent
StatesMatchRoles ==    
    \A s \in StartedServers :
        /\ role[s] = Observer => state[s] \in ObserverStates
        /\ state[s] = Unattached => leader[s] = Nil

\* INV: NeverTwoLeadersInSameEpoch
\* We cannot have two servers having a conflicting
\* view on who the leader is in the same epoch    
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
\* An acknowledged value must exist on at least one server

AckedValueNotLost ==
    \A v \in inv_pos_acked :
        \E s \in StartedServers :
            /\ role[s] = Voter
            /\ ValueInServerLog(s, v)

\* INV: Used in debugging
TestInv ==
    TRUE
\*    Quantify(DOMAIN net_connectivity, LAMBDA p : net_connectivity[p] = TRUE)
\*        >= 2
                

\*================================================
\* Liveness properties
\*================================================

\* Note that due to the number of elections being limited,
\* the last possible election could fail to elect a leader 
\* which will prevent progress, so these liveness formulas 
\* only apply in cases where the behaviour does not end 
\* with all elections used up and no elected leader in 
\* the current configuration. There doesn't seem to be any
\* way to avoid this.

NoProgressPossible ==
    \* no more elections will occur
    /\ aux_ctrs.election_ctr = MaxElections
    \* and, the current epoch cannot make further progress
    /\ ~\E s \in StartedServers : 
        /\ state[s] = Leader
        /\ \E peer \in StartedServers : 
            /\ state[peer] = Voter
            /\ s \in config[peer].members


\* LIVENESS: ValuesEventuallyAcked -----------------
\* A client value will eventually get positively or negatively
\* acknowledged, or the election limit is reached without a leader.

ValuesEventuallyAcked ==
    \A v \in Value :
        (v \in inv_sent) ~> (\/ NoProgressPossible
                             \/ v \in inv_neg_acked
                             \/ v \in inv_pos_acked)

\* LIVENESS: ReconfigurationCompletes -----------
\* A reconfiguration command will either get committed and be
\* fully replicated or it will be truncated and
\* not be found on any server log.
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
    IF NoProgressPossible
    THEN TRUE
    ELSE \E s \in StartedServers : 
            /\ IsCurrentLeader(s)
            /\ \/ \A s1 \in config[s].members : ConfigInServerLogAndCommitted(s, config_id)
               \/ \A s1 \in config[s].members : ConfigNotInServerLog(s, config_id)

ReconfigurationNotStuck ==
    \A config_id \in 1..(MaxAddReconfigs + MaxRemoveReconfigs) :
        []<>ConfigAllOrNothing(config_id)
        
================================================