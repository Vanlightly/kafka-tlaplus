--------------------------- MODULE v3_5_properties ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC,
        message_passing,
        v3_5_types,
        v3_5_functions

\* ===============================================================
\* INVARIANTS
\* ===============================================================

\* INV: TypeOK
\* Basic type checking
TypeOK ==
    /\ con_unfenced \in SUBSET Brokers
    /\ con_broker_reg \in [Brokers -> ControllerSideBrokerState]
    /\ con_partition_metadata \in ControllerPartitionMetadata
    /\ broker_state \in [Brokers -> BrokerSideState]
    /\ broker_fetchers \in [Brokers -> [Brokers -> BrokerFetcher]]
    /\ partition_metadata \in [Brokers -> ReplicaPartitionMetadata]
    /\ partition_replica_state \in [Brokers -> [Brokers -> PeerReplicaState]]
    /\ aux_ctrs \in StateSpaceLimitCtrs
    /\ partition_status \in [Brokers -> {Leader, Follower, Nil}]
    /\ inv_sent \in SUBSET Values
    /\ inv_pos_acked \in SUBSET Values
    /\ inv_neg_acked \in SUBSET Values

\* INV: ValidBrokerState
\* For catching spec bugs, ensure broker state is legal.
ValidBrokerState ==
    \A b \in Brokers :
        \/ broker_state[b].status # RUNNING
        \/ /\ broker_state[b].status = RUNNING
           /\ broker_state[b].registered = TRUE

\* INV: ValidReplicaState
\* For catching spec bugs, ensure replica state is legal.
ValidReplicaState ==           
    \A b \in Brokers :
        /\ IF partition_status[b] = Leader
           THEN partition_metadata[b].leader = b
           ELSE TRUE
        /\ partition_data[b].leo = Len(partition_data[b].log) + 1
        /\ \A offset \in 1..partition_data[b].leo-1 :
                partition_data[b].log[offset].offset = offset

\* INV: ValidFetcherState
\* For catching spec bugs, ensure fetcher state is legal.
ValidFetcherState ==
    \A b \in Brokers :
        \* the broker doesn't have two fetchers with the partition
        \* added at the same time.
        /\ ~\E b1, b2 \in Brokers :
            /\ b # b1
            /\ b1 # b2
            /\ broker_fetchers[b][b1].partition # Nil
            /\ broker_fetchers[b][b2].partition # Nil
        \* leaders do not have fetchers with the partition added
        \* and followers do have a fetcher with the partition added.
        /\ CASE partition_status[b] = Leader ->
                    ~\E b1 \in Brokers :
                        /\ b # b1
                        /\ broker_fetchers[b][b1].partition # Nil
             [] partition_status[b] = Follower ->
                    \E b1 \in Brokers :
                       /\ b # b1
                       /\ broker_fetchers[b][b1].partition # Nil
             [] OTHER -> TRUE

\* INV: ValidControllerState
\* For catching spec bugs, ensure controller state is legal.
ValidControllerState ==
    \* there is no broker such that its fenced status is
    \* inconsistent with its membership to the unfenced set.
    /\ ~\E b \in Brokers :
        \/ /\ con_broker_reg[b].status = FENCED
           /\ b \in con_unfenced              
        \/ /\ con_broker_reg[b].status = UNFENCED
           /\ b \notin con_unfenced
    \* A fenced broker cannot be in an ISR of size > 1
    /\ IF Cardinality(con_partition_metadata.isr) > 1
       THEN ~\E b \in con_partition_metadata.replicas :
               /\ con_broker_reg[b].status = FENCED
               /\ b \in con_partition_metadata.isr
       ELSE TRUE
    \* The ISR cannot be empty
    /\ con_partition_metadata.isr # {} 
    
\* INV: ReplicationQuorumSupersetProperty
\* The maximal ISR is critical for safety. The invariant here is that
\* the maximal ISR on the (non-stale) leader must be a superset of
\* the controller ISR. Else we can lose data. 
IsNonStaleLeader(b) ==
    /\ partition_status[b] = Leader
    /\ partition_metadata[b].leader_epoch = con_partition_metadata.leader_epoch

ReplicationQuorumSupersetProperty ==
    \A b \in Brokers :
        \* if the leader is a non-stale leader
        IF IsNonStaleLeader(b)
        THEN 
              \* if it doesn't have a pending AP Req then: maximal ISR = ISR
              /\ IF ~PendingAlterPartitionResponse(b)
                 THEN partition_metadata[b].maximal_isr = partition_metadata[b].isr
                 ELSE TRUE
              \* the leader maximal ISR must be a superset of the controller ISR 
              /\ \A b1 \in con_partition_metadata.isr :
                    b1 \in partition_metadata[b].maximal_isr
        ELSE TRUE

\* INV: LeaderCandidateCompletenessProperty
\* The true HWM is tracked by the spec (not the brokers)
\* and if any replica in the ISR has an LEO < the True
\* HWM, then that violates this property. Note that
\* this only applies for ISR members that are running. If a replica
\* just experienced a lossy unclean shutdown then it might not
\* host all committed data - but the Unclean Exclusion property
\* guarantees that once it is running again, it cannot be in the ISR
\* until it has proven itself by catching up to the new leader.
LeaderCandidateCompletenessProperty ==
    \* if something got committed then do the check
    IF inv_true_hwm > 1
    THEN 
         \* If there is a running leader then it should host the committed data
        ~\E b \in con_partition_metadata.isr :
            /\ partition_data[b].leo < inv_true_hwm
            /\ broker_state[b].status = RUNNING
    ELSE TRUE

\* INV: LeaderCompletenessProperty
\* The replica selected as leader by the controller must have
\* the entire committed log else this is data loss. Again,
\* this only applies if the leader is RUNNING (for the same
\* reason as LeaderCandidateCompleteness).
LeaderCompletenessProperty ==
    \* if something got committed then do the check
    IF inv_true_hwm > 1
    THEN 
         \* If there is a running leader then it should host the committed data
        LET leader == con_partition_metadata.leader
        IN  
            IF \/ leader = NoLeader
            \/ /\ leader # NoLeader
                /\ broker_state[leader].status # RUNNING
            THEN TRUE \* If there is no leader or the leader isn't running then
                    \* this property cannot be verified.
            ELSE \* The leader LEO is not lower than the True HWM.
                /\ partition_data[leader].leo >= inv_true_hwm
                \* also check positively acknowledged writes exist in the leader log.
                /\ \A v \in inv_pos_acked :  
                    \E offset \in DOMAIN partition_data[leader].log :
                        partition_data[leader].log[offset].value = v
    ELSE TRUE

\* INV: LogMatchingProperty
\* The stable prefix of the partition on each replica must be 
\* consistent with every other. For each replica pair, this 
\* checks up to the min of (b1 HWM, b2 HWM).
LogMatchingProperty == 
    \A offset \in 1..Cardinality(Values) :
        ~\E b1, b2 \in Brokers :
            /\ partition_data[b1].leo > offset
            /\ partition_data[b2].leo > offset
            /\ partition_data[b1].hwm > offset
            /\ partition_data[b2].hwm > offset
            /\ partition_data[b1].log[offset].value # partition_data[b2].log[offset].value

\* INV: MetadataLogMatchingProperty
\* The metadata log on the controller must be consistent with
\* every broker (up to the last offset per broker).
MetadataLogMatchingProperty == 
    \A offset \in 1..Len(con_metadata_log) :
        ~\E b \in Brokers :
            /\ Len(broker_metadata_log[b]) >= offset
            /\ broker_metadata_log[b][offset] # con_metadata_log[offset]

\*INV: NoCommittedRecordLostGlobally
\* This is useful as the LeaderCompleteness property only checks
\* leaders, not situations where data is lost and there is no
\* viable leader to elect. This will trigger if you set the number
\* of unclean shutdowns to match the MinISR. So if you want to check
\* LeaderCompleteness even under high unclean shutdown counts, do not
\* enable this invariant.
NoCommittedRecordLostGlobally ==
    \A v \in inv_pos_acked :
        \E b \in Brokers :
            \E offset \in LogOffsets(b) :
                partition_data[b].log[offset].value = v

\* INV: ConsistentReadProperty
\* Ensures consistency between records read in the past
\* and the current leader log. 
\* Consumers can consume up to the HWM. If a consumer consumes
\* a record at a given offset, then later the record at that
\* same offset does not exist or has changed, this invariant is violated.
\* This isn't quite enough for checking linearizability, that will
\* require checking producer acknowledgements - future work.
ConsistentReadProperty ==
    \* consistent (repeatable reads)
    /\ \A b \in Brokers :
        IF IsNonStaleLeader(b)
        THEN \A offset \in DOMAIN inv_consumed :
                /\ offset \in LogOffsets(b)
                /\ partition_data[b].log[offset] = inv_consumed[offset]
        ELSE TRUE
        
TestInv ==
    TRUE
    
\* ========================================================
\* LIVENESS
\*
\* Note that liveness checks are predicated on the fact that
\* actions which help the cluster make progress or heal the
\* cluster are eventually allowed to occur. This means the
\* specification explores all histories where eventually the
\* cluster can return to normal.
\* ========================================================

\* LIVENESS: EventuallyRuns
\* Eventually, a broker that has STARTING status, reaches RUNNING.
EventuallyRuns ==
    \A b \in Brokers :
        broker_state[b].status = STARTING ~>
            /\ broker_state[b].status = RUNNING
            /\ con_broker_reg[b].status = UNFENCED

\* LIVENESS: EventuallyUnfenced
\* Eventually, a broker that is fenced becomes unfenced.
EventuallyUnfenced ==
    \A b \in Brokers :
        con_broker_reg[b].status = FENCED ~>
            con_broker_reg[b].status = UNFENCED

\* LIVENESS: AlterPartitionEpochEventuallyReachedOrZero
\* Eventually, a replica that has sent an AlterPartition request
\* reaches the expected partition epoch, or the request is rejected.
AlterPartitionEpochEventuallyReachedOrZero ==
    []<>(\A b \in Brokers :
        partition_pending_ap[b].epoch > 0 ~> 
            \/ partition_pending_ap[b].epoch = partition_metadata[b].partition_epoch
            \/ partition_pending_ap[b].epoch = 0)

\* LIVENESS: EventuallyMetadataConverges
\* Eventually, each broker converges on the same metadata as the controller.
EventuallyMetadataConverges ==
    []<>(\A b \in Brokers : 
            \* either the metadata has converged
            \/ /\ partition_metadata[b].isr = con_partition_metadata.isr
               /\ partition_metadata[b].leader = con_partition_metadata.leader
               /\ partition_metadata[b].leader_epoch = con_partition_metadata.leader_epoch
               /\ partition_metadata[b].partition_epoch = con_partition_metadata.partition_epoch
            \* or this is a follower and there are no further relevant records
            \* (this spec reduces state space by pausing metadata replication when no relevant unreplicated records exist)
            \/ /\ partition_status[b] = Follower
               /\ ~\E md_offset \in UnreplicatedOffsets(b) :
                    PartitionNeedsAction(b, md_offset))
                    

\* LIVENESS: EventuallyWriteIsAcceptedOrRejected
\* A produce request will eventually be positively or negatively acknowledged
EventuallyWriteIsAcceptedOrRejected ==
    \A v \in Values :
        v \in inv_sent ~> \/ v \in inv_pos_acked
                          \/ v \in inv_neg_acked

\* LIVENESS: EventuallyAcknowledgedValueFullyReplicated
\* A record that gets positively acknowledged eventually becomes
\* fully replicated.
EventuallyAcknowledgedValueFullyReplicated ==
    \A v \in Values :
        v \in inv_pos_acked ~>
                \A b \in con_partition_metadata.replicas : 
                    \E offset \in LogOffsets(b) :
                        partition_data[b].log[offset].value = v


\* LIVENESS: EventuallyReassignmentCompletes
\* A reassignment should eventually complete.
EventuallyReassignmentCompletes ==
    \/ con_partition_metadata.adding # {}
    \/ con_partition_metadata.removing # {} ~>
            /\ con_partition_metadata.adding = {}
            /\ con_partition_metadata.removing = {}

      
=============================================================================    