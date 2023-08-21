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
       THEN ~\E b \in Brokers :
               /\ con_broker_reg[b].status = FENCED
               /\ b \in con_partition_metadata.isr
       ELSE TRUE
    \* The ISR cannot be empty
    /\ con_partition_metadata.isr # {} 
    
\* INV: ValidLeaderMaximalISR
\* The maximal ISR is critical for safety. The invariant here is that
\* the maximal ISR on the (non-stale) leader must be a superset of
\* the controller ISR. Else we can lose data.
\* (Triggers soon than invariant LeaderHasCompleteCommittedLog). 
IsNonStaleLeader(b) ==
    /\ partition_status[b] = Leader
    /\ partition_metadata[b].leader_epoch = con_partition_metadata.leader_epoch

ValidLeaderMaximalISR ==
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

\* INV: ControllerIsrHasUpToTrueHWM
\* The true HWM is tracked by the spec (not the brokers)
\* and if any replica in the ISR has an LEO < the true
\* HWM, then that is an illegal state which can lead
\* to data loss. 
\* (Triggers soon than invariant LeaderHasCompleteCommittedLog).
ControllerIsrHasUpToTrueHWM ==
    \* No member of the ISR is missing committed records
    \* and is RUNNING 
    /\ ~\E b \in con_partition_metadata.isr :
        /\ partition_data[b].leo < inv_true_hwm
        /\ broker_state[b].status = RUNNING

\* INV: LeaderHasCompleteCommittedLog
\* The replica selected as leader by the controller must have
\* the entire acknowledged log else this is data loss.
LeaderHasCompleteCommittedLog ==
    \/ con_partition_metadata.leader = NoLeader
    \/ /\ con_partition_metadata.leader # NoLeader
       /\ \A v \in inv_pos_acked :
            \E offset \in DOMAIN partition_data[con_partition_metadata.leader].log :
                partition_data[con_partition_metadata.leader].log[offset].value = v

\* INV: NoPartitionLogDivergence
\* The partition log on the leader must be consistent with
\* every follower (up to the HWM per replica).
NoPartitionLogDivergence == 
    \A offset \in 1..Cardinality(Values) :
        ~\E b1, b2 \in Brokers :
            /\ partition_data[b1].leo > offset
            /\ partition_data[b2].leo > offset
            /\ partition_data[b1].hwm > offset
            /\ partition_data[b2].hwm > offset
            /\ partition_data[b1].log[offset].value # partition_data[b2].log[offset].value

\* INV: NoMetadataLogDivergence
\* The metadata log on the controller must be consistent with
\* every broker (up to the last offset per broker).
NoMetadataLogDivergence == 
    \A offset \in 1..Len(con_metadata_log) :
        ~\E b \in Brokers :
            /\ Len(broker_metadata_log[b]) >= offset
            /\ broker_metadata_log[b][offset] # con_metadata_log[offset]

\*INV: NoCommittedRecordLostGlobally
\* LeaderHasCompleteCommittedLog prefered as it triggers earlier.
\* Losing an acknowledged record on the leader ultimately
\* results in global data loss for that record.
NoCommittedRecordLostGlobally ==
    \A v \in inv_pos_acked :
        \E b \in Brokers :
            \E offset \in LogOffsets(b) :
                partition_data[b].log[offset].value = v

\* INV: ConsumedRecordsMatchLeaderLog
\* Ensures consistency between records read in the past
\* and the current leader log. 
\* Consumers can consume up to the HWM. If a consumer consumes
\* a record at a given offset, then later the record at that
\* same offset does not exist or has changed, this invariant is violated. 
ConsumedRecordsMatchLeaderLog ==
    \A b \in Brokers :
        IF IsNonStaleLeader(b)
        THEN \A offset \in DOMAIN inv_consumed :
                /\ offset \in LogOffsets(b)
                /\ partition_data[b].log[offset] = inv_consumed[offset]
        ELSE TRUE

TestInv == 
    TRUE

\* ========================================================
\* LIVENESS
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
            /\ partition_metadata[b].isr = con_partition_metadata.isr
            /\ partition_metadata[b].leader = con_partition_metadata.leader
            /\ partition_metadata[b].leader_epoch = con_partition_metadata.leader_epoch
            /\ partition_metadata[b].partition_epoch = con_partition_metadata.partition_epoch)

\* LIVENESS: EventuallyHighwaterMarkAdvances
\* Once a value is written to the log
\*EventuallyHighwaterMarkAdvances ==
\*    \A v \in Values :
\*        (ValueWritten(v)) ~>
\*             (\/ ValueNegAcked(v)
\*              \/ \E b \in Brokers :
\*                  /\ IsNonStaleLeader(b)
\*                  /\ \E offset \in LogOffsets(b) :
\*                     /\ partition_data[b].log[offset].value = v
\*                     /\ partition_data[b].hwm >= offset)

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
                \A b \in Brokers : 
                    \E offset \in LogOffsets(b) :
                        partition_data[b].log[offset].value = v
      
=============================================================================    