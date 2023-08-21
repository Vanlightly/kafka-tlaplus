--------------------------- MODULE v3_5_functions ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC,
        v3_5_types

\* ======================================================================
\* ------------ Helpers -------------------------------------------------

LogOffsets(b) ==
    DOMAIN partition_data[b].log

LogOf(b) ==
    partition_data[b].log
    
LogEntry(b, offset) ==
    partition_data[b].log[offset]
    
LogEntryEpoch(b, offset) ==
    partition_data[b].log[offset].epoch
    
LeoOf(b) ==
    partition_data[b].leo
    
HwmOf(b) ==
    partition_data[b].hwm

PartitionMetadata(b) ==
    partition_metadata[b]

PartitionData(b) ==
    partition_data[b]

ReplicaState(b1, b2) ==
    partition_replica_state[b1][b2]    

Fetcher(b1, b2) ==
    broker_fetchers[b1][b2]

BlankFetchState ==
    [partition        |-> Nil,
     pending_response |-> FALSE]
     
IsPartitionAdded(b1, b2) ==
    broker_fetchers[b1][b2].partition # Nil

BlankReplicaState ==
    [leo              |-> Nil,
     broker_epoch     |-> 0]

\* A replica resets its peer replica state when it changes role.
\* If it has become a leader then it sets its own replica state as this
\* spec uses that when computing the HWM advancement.    
ResetReplicaState(b) ==
    partition_replica_state' = [partition_replica_state EXCEPT ![b] = 
                                    [b1 \in Brokers |-> BlankReplicaState]]

\* partition_pending_ap is used by the spec to know when it is pending 
\* an AP request. If the epoch is higher than the current partition epoch
\* then it is pending a response.
ResetPendingAlterPartition(b) ==
    partition_pending_ap' = [partition_pending_ap EXCEPT ![b] = 
                                [epoch   |-> 0,
                                 request |-> Nil]]

\* TRUE if we are expecting a response with a higher partition epoch
PendingAlterPartitionResponse(b) ==
    partition_pending_ap[b].epoch > PartitionMetadata(b).partition_epoch

\* ==========================================================================
\* -- Anti-cycle checks (for liveness properties and state space limiting) --
\*
\* To avoid cycles such as infinite fetch request/responses, the spec limits
\* fetch requests to when they are required to make progress.
\* Generally speaking, you can ignore this.


\* This magic formula is able to see the state on both the local replica
\* and the leader (which the replica can't actually do) and figure out
\* if sending a fetch helps progress - else it will only enable a cycle. 
\* This requires **great care** to avoid hiding legal behaviors that could
\* result in invariant or liveness violations.
__SendFetchMakesProgress(b) ==
    LET leader == PartitionMetadata(b).leader
        matching_epoch == PartitionMetadata(b).leader_epoch = PartitionMetadata(leader).leader_epoch
    IN \* Limit when fetch requests can be sent according to the leader epoch on leader and follower
       /\ CASE 
            \* --- CASE Delayed partition but leader epoch doesn't match ------------------------
               /\ broker_fetchers[b][leader].partition.delayed = TRUE
               /\ matching_epoch = FALSE -> FALSE
            \* --- CASE Model limits fetch requests to matching epoch but epochs don't match ----
            [] /\ LimitFetchesOnLeaderEpoch = TRUE
               /\ matching_epoch = FALSE -> FALSE
            \* --- CASE else we can send the fetch
            [] OTHER -> TRUE
       \* one of the following is true:
       /\ \* leader has records to get
          \/ LeoOf(b) < LeoOf(leader)
          \* leader has hwm to get                  
          \/ HwmOf(b) < HwmOf(leader)        
          \* leader hasn't received any fetch request from this follower
          \/ ReplicaState(leader, b).leo = Nil
          \* leader doesn't know current leo of this follower   
          \/ /\ ReplicaState(leader, b).leo # Nil   
             /\ ReplicaState(leader, b).leo < LeoOf(b)

\* This prevents a replica from processing a fetch request with a larger leader
\* epoch than its own. It shouldn't cause liveness issues as eventually the
\* replica will learn of the new leader epoch.
__ReceiveFetchMakesProgress(m) ==
    IF /\ LimitFetchesOnLeaderEpoch = TRUE
       /\ m.partition.leader_epoch > PartitionMetadata(m.dest).leader_epoch
    THEN FALSE
    ELSE TRUE



\* ======================================================================
\* ------------ Key functions -------------------------------------------
\* These functions may be used in multiple places.

\*----------------------------------------------------
\* FUNCTION: CommitOffsetOnFetch, CommitOffsetOnUpdate, CommitOffsetOnWrite
\*
\* Find the highest (contiguous) offset that has been replicated
\* to the leader's maximal ISR - nominally called the commit offset here.

IsCommitted(b, maximal_isr, replica_state, offset) ==
    \A b1 \in maximal_isr :
        \/ b = b1 \* we auto-count the leader itself
        \/ /\ replica_state[b1].leo # Nil
           /\ replica_state[b1].leo > offset

GetCommitOffset(b, maximal_isr, leo, replica_state) ==
    CASE LeoOf(b) = 1 ->
            0
      [] \E offset \in 1..leo-1:
            IsCommitted(b, maximal_isr, replica_state, offset) ->
                \* This is a TLA+ way of saying choose the highest offset which is committed.
                \* Basically, choose an offset such that it is committed and no other offset
                \* exists that is also committed and is higher.
                CHOOSE offset \in 1..leo-1 :
                    /\ IsCommitted(b, maximal_isr, replica_state, offset)
                    /\ ~\E offset1 \in 1..leo-1 :
                        /\ IsCommitted(b, maximal_isr, replica_state, offset1)
                        /\ offset1 > offset
      [] OTHER -> 0

\* Only the replica state of one follower may have changed from current state
CommitOffsetOnFetch(b, replica_state) ==
    GetCommitOffset(b, PartitionMetadata(b).maximal_isr, 
                    LeoOf(b), replica_state)

\* Only the maximal ISR may have changed from current state
CommitOffsetOnUpdate(b, maximal_isr) ==
    GetCommitOffset(b, maximal_isr, LeoOf(b), 
                    partition_replica_state[b])

\* Only the leader's log may have changed from current state    
CommitOffsetOnWrite(b, new_leo) ==
    GetCommitOffset(b, partition_metadata[b].maximal_isr,
                    new_leo, partition_replica_state[b])

\*-------------------------------------------------------------
\* FUNCTION: MaybeAdvanceHighWatermark
\*
\* If the potential new HWM is higher then, advance the HWM and
\* record it in related invariant variables.  

NoHighWatermarkChange ==
    UNCHANGED << partition_data, inv_vars >>

\* rebuild the map setting the ack type for the specified range
\* leaving the rest unchanged.
SendAcksFor(b, lower, higher, ack_type) ==
    LET values == { v \in inv_sent : /\ v \notin inv_pos_acked
                                     /\ v \notin inv_neg_acked
                                     /\ \E offset \in lower..higher :
                                          LogEntry(b, offset).value = v }
    IN 
       IF ack_type = TRUE 
       THEN /\ inv_pos_acked' = inv_pos_acked \union values
            /\ UNCHANGED << inv_neg_acked >>
       ELSE /\ inv_neg_acked' = inv_neg_acked \union values
            /\ UNCHANGED << inv_pos_acked >> 

UpdateHwmInvariantVars(b, old_hwm, new_hwm, ack_type) ==
    /\ IF ack_type = TRUE  \* positive ack
       THEN SendAcksFor(b, old_hwm, new_hwm-1, ack_type) \* pos ack up to new HWM
       ELSE SendAcksFor(b, old_hwm, LeoOf(b)-1, ack_type) \* neg ack from old HWM and above
    \* update the true high watermark
    /\ inv_true_hwm' = IF new_hwm > inv_true_hwm
                       THEN new_hwm ELSE inv_true_hwm
    \* If the "real" HWM has advanced, record which records
    \* got consumed by consumers.
    /\ inv_consumed' = IF new_hwm > inv_true_hwm
                       THEN inv_consumed \o SubSeq(LogOf(b), inv_true_hwm, new_hwm-1)
                       ELSE inv_consumed
                    
MaybeAdvanceHighWatermark(b, old_hwm, new_hwm, ack_type) ==
    IF new_hwm > old_hwm
    THEN /\ partition_data' = [partition_data EXCEPT ![b].hwm = new_hwm]
         /\ UpdateHwmInvariantVars(b, old_hwm, new_hwm, ack_type)
         /\ UNCHANGED inv_sent
    ELSE NoHighWatermarkChange

\*-----------------------------------------------------------
\* FUNCTION: MaybeFailPendingWrites
\*
\* If the ISR is now below MinISR or the replica lost leadership
\* then negatively acknowledge all unacknowledged records above
\* the high watermark.

FailPendingWrites(b) ==
    SendAcksFor(b, HwmOf(b), LeoOf(b)-1, FALSE)

MaybeFailPendingWrites(b, part_state) ==
    IF /\ HwmOf(b) < LeoOf(b)
       /\ \/ Cardinality(part_state.isr) < MinISR
          \/ b # part_state.leader
    THEN FailPendingWrites(b)
    ELSE UNCHANGED << inv_sent, inv_pos_acked, inv_neg_acked >>

\*----------------------------------------------------------------
\* FUNCTION: MaybeUpdateHwmOnPartitionChange
\*
\* On learning of a partition change, whether due to an 
\* AlterPartition response or from a metadata update, the leader
\* must check whether:
\*  1. It can now advance the high watermark or not.
\*  2. It should positively or negatively acknowledge any
\*     unacknowledged records.
\*
\* The high watermark is advanced if there are uncommitted records
\* that have been replicated to all members in the maximal ISR (in the
\* case of shrinkage). If the maximal ISR is now below MinISR then any 
\* unacknowledged records above the current high watermark should be
\* negatively acknowledged (NotEnoughReplicasAfterAppend).
\*
\* Note that the calculated new high watermark may be lower than 
\* the old high watermark as after a leader change, the leader may 
\* still not have enough information on its followers to know to 
\* compute the new high watermark.

MaybeUpdateHwmOnPartitionChange(b, part_state, is_new_leader) ==
    LET old_hwm == HwmOf(b)
        new_hwm == CommitOffsetOnUpdate(b, part_state.maximal_isr) + 1
        ack_type == IF Cardinality(part_state.maximal_isr) >= MinISR
                    THEN TRUE ELSE FALSE
    IN MaybeAdvanceHighWatermark(b, old_hwm, new_hwm, ack_type)

\*--------------------------------------------------------------
\* FUNCTIONS: ApplyPartitionChange, NoPartitionChange
\*
\* - ApplyPartitionChange: When a partition state change is required,
\*   the controller does two things: update the in-memory state and
\*   append a PartitionChangeRecord to the metadata log.

NoPartitionChange ==
    UNCHANGED << con_partition_metadata, con_metadata_log >>

ApplyPartitionChange(new_leader, new_isr, leader_epoch, 
                     part_epoch) ==
    /\ con_partition_metadata' = 
               [isr             |-> new_isr,
                leader          |-> new_leader, 
                leader_epoch    |-> leader_epoch,
                partition_epoch |-> part_epoch]
    /\ con_metadata_log' = 
          Append(con_metadata_log,
                [type            |-> PartitionChangeRecord,
                 leader          |-> new_leader,
                 isr             |-> new_isr,
                 leader_epoch    |-> leader_epoch,
                 partition_epoch |-> part_epoch])

\*--------------------------------------------------------------
\* FUNCTION: MaybeUpdatePartitionMetadata, MaybeRemoveBrokerFromISR

\* The ISR cannot drop below 1
MaybeRemoveBrokerFromISR(isr, b) ==
    IF Cardinality(isr) = 1
    THEN isr
    ELSE isr \ {b}    
    
\* TRUE iff no leader change is required    
NoLeaderChange(new_isr, new_unfenced) ==
    \* either there is no leader and there is no leader candidate either
    \/ /\ con_partition_metadata.leader = NoLeader
       /\ ~\E candidate \in new_isr : candidate \in new_unfenced
    \* or the leader is in the ISR and is unfenced (so no need to change it)
    \/ /\ con_partition_metadata.leader \in new_isr
       /\ con_partition_metadata.leader \in new_unfenced

\* Based on the new ISR and unfenced broker set, decide
\* whether a partition state change is required or not.
MaybeUpdatePartitionMetadata(new_isr, new_unfenced) ==
    LET md == con_partition_metadata
    IN
        CASE /\ NoLeaderChange(new_isr, new_unfenced)
             /\ new_isr = md.isr ->
                \* no-op
                NoPartitionChange
          [] /\ NoLeaderChange(new_isr, new_unfenced)
             /\ new_isr # md.isr ->
                \* basically, ISR change but no leader change. 
                \* Update partition state and append partition change record.
                ApplyPartitionChange(md.leader, new_isr, 
                                     md.leader_epoch,
                                     md.partition_epoch + 1)
          [] \E candidate \in new_isr : candidate \in new_unfenced ->
                \* basically, at the very least, there is a leader change.
                \* Non-deterministically choose a valid candidate for leader.
                \* Update partition state and append partition change record.
                \E candidate \in new_isr :
                    /\ candidate \in new_unfenced
                    /\ ApplyPartitionChange(candidate, new_isr, 
                                            md.leader_epoch + 1,
                                            md.partition_epoch + 1)
          [] ~\E candidate \in new_isr : candidate \in new_unfenced ->
                \* The ISR remains the same, but there is no leader.
                \* This is the case where the ISR was 1 and the leader got fenced.
                \* Update partition state and append partition change record.
                ApplyPartitionChange(NoLeader, new_isr, 
                                     md.leader_epoch + 1,
                                     md.partition_epoch + 1)
          [] OTHER -> \* no-op 
                NoPartitionChange

\*--------------------------------------------------------------
\* FUNCTIONS: HandleBrokerFenced, HandleBrokerUnfenced

HandleBrokerFenced(b) ==
    LET new_isr      == MaybeRemoveBrokerFromISR(con_partition_metadata.isr, b)
        new_unfenced == con_unfenced \ {b}
    IN /\ MaybeUpdatePartitionMetadata(new_isr, new_unfenced)
       /\ con_unfenced' = new_unfenced

HandleBrokerUnfenced(b) ==
    LET new_isr      == con_partition_metadata.isr \* unfencing doesn't change the ISR
        new_unfenced == con_unfenced \union {b}
    IN \* if there is no leader the controller can choose one from the ISR.
       /\ IF con_partition_metadata.leader = NoLeader 
          THEN MaybeUpdatePartitionMetadata(new_isr, new_unfenced)
          ELSE NoPartitionChange
       /\ con_unfenced' = new_unfenced

\*--------------------------------------------------------------
\* FUNCTION: LastOffsetForEpoch

\* Find the highest epoch in the log, or use the required epoch if
\* none is lower or equal, and the start offset of the next highest
\* epoch. The offset is exclusive.

NoEpochAndOffset == 
    [epoch |-> 0, offset |-> 0]

LastOffsetForEpoch(b, req_epoch, is_leader) ==
    IF \/ LogOf(b) = <<>> 
       \/ /\ LogOf(b) # <<>>
          /\ req_epoch = Last(LogOf(b)).epoch
       \/ /\ is_leader
          /\ PartitionMetadata(b).leader_epoch = req_epoch
    THEN [epoch |-> req_epoch, offset |-> LeoOf(b)]
    ELSE 
        LET higher_epoch_offset ==
                           \* If there is a higher epoch in the log, then select the start offset
                           \* of the lowest epoch > required epoch.
                           IF \E offset \in LogOffsets(b) :
                                LogEntryEpoch(b, offset) > req_epoch
                           THEN CHOOSE offset \in LogOffsets(b) :
                                    /\ LogEntryEpoch(b, offset) > req_epoch
                                    /\ ~\E offset2 \in LogOffsets(b) :
                                        /\ offset2 < offset
                                        /\ LogEntryEpoch(b, offset2) > req_epoch
                                        /\ LogEntryEpoch(b, offset2) < LogEntryEpoch(b, offset)
                           \* Else, if this is the leader, the current leader epoch counts as a
                           \* higher epoch. If it is higher then choose the LEO.
                           ELSE IF /\ is_leader
                                   /\ PartitionMetadata(b).leader_epoch > req_epoch
                                THEN LeoOf(b)
                                ELSE Nil \* this should not happen so we set an illegal value to crash it.
            floor_epoch_offset == 
                           \* Choose the highest offset of the highest epoch that is <= required epoch.
                           \* This is used for selecting the epoch to be returned.
                           CHOOSE offset \in LogOffsets(b) :
                                /\ LogEntryEpoch(b, offset) <= req_epoch
                                /\ ~\E offset2 \in LogOffsets(b) :
                                    /\ LogEntryEpoch(b, offset2) <= req_epoch
                                    /\ LogEntryEpoch(b, offset2) > LogEntryEpoch(b, offset)
        IN \* If we have an epoch <= required epoch in the log, then return
           \* the floor epoch with the higher epoch offset.
           IF \E offset \in LogOffsets(b) :
                  LogEntryEpoch(b, offset) <= req_epoch
           THEN [epoch  |-> LogEntryEpoch(b, floor_epoch_offset),
                 offset |-> higher_epoch_offset]
           \* Else, return the required epoch with the higher epoch offset.    
           ELSE [epoch  |-> req_epoch,
                 offset |-> higher_epoch_offset]


=============================================================================    