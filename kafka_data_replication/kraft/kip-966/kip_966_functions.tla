--------------------------- MODULE kip_966_functions ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC,
        kip_966_types, message_passing

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
     
BlankMetadata ==
    [replicas        |-> {},
     isr             |-> {},
     maximal_isr     |-> {},
     leader          |-> NoLeader,
     leader_epoch    |-> 0,
     partition_epoch |-> 0]     

ResetAllFollowerState(b) ==
    partition_replica_state' = [partition_replica_state EXCEPT ![b] = 
                                    [b1 \in Brokers |-> BlankReplicaState]]
                                    
ResetFollowerStateOfAllButISR(b, new_part_md) ==
    partition_replica_state' = [partition_replica_state EXCEPT ![b] = 
                                    [b1 \in Brokers |->
                                        IF b1 \notin new_part_md.isr
                                        THEN BlankReplicaState
                                        ELSE partition_replica_state[b][b1]]]                                    

\* partition_pending_ap is used by the spec to know when it is pending 
\* an AP request. If the epoch is higher than the current partition epoch
\* then it is pending a response.
ResetPendingAlterPartition(b) ==
    partition_pending_ap' = [partition_pending_ap EXCEPT ![b] = 
                                [epoch   |-> 0,
                                 request |-> Nil]]

\* TRUE if we are expecting a response with a higher partition epoch
PendingAlterPartitionResponse(b) ==
    partition_pending_ap[b].epoch > partition_metadata[b].partition_epoch
    
IsLeaderEpochBump(b, md_offset) ==
    con_metadata_log[md_offset].leader_epoch > partition_metadata[b].leader_epoch    

ReassignmentInProgress ==
    \/ con_partition_metadata.adding # {}
    \/ con_partition_metadata.removing # {}

\* ==========================================================================
\* -- State-space reducers and anti-cycle checks 
\*    (for liveness properties and state space limiting) --
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
    LET leader == partition_metadata[b].leader
        matching_epoch == partition_metadata[b].leader_epoch = partition_metadata[leader].leader_epoch
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
\* epoch than its own (when LimitFetchesOnLeaderEpoch=TRUE).
\* It shouldn't cause liveness issues as eventually the replica will learn of 
\* the new leader epoch.
__ReceiveFetchMakesProgress(m) ==
    IF /\ LimitFetchesOnLeaderEpoch = TRUE
       /\ m.partition.leader_epoch > partition_metadata[m.dest].leader_epoch
    THEN FALSE
    ELSE TRUE
        
\* ======================================================================
\* ------------ Key functions -------------------------------------------
\* These functions may be used in multiple places.

\*----------------------------------------------------
\* FUNCTION: UnreplicatedOffsets, PartitionNeedsAction
\*
\* Functions for metadata replication. PartitionNeedsAction
\* is TRUE when the metadata record affects the local
\* replica.

UnreplicatedOffsets(b) ==
    Len(broker_metadata_log[b])+1..Len(con_metadata_log)

PartitionNeedsAction(b, md_offset) ==
    \* Leaders react to all partition changes
    \/ partition_status[b] = Leader 
    \* Existing followers react to leader epoch bumps
    \/ /\ b \in partition_metadata[b].replicas
       /\ IsLeaderEpochBump(b, md_offset) 
    \* New followers (being added) react
    \/ /\ b \notin partition_metadata[b].replicas
       /\ b \in con_metadata_log[md_offset].replicas


\*----------------------------------------------------
\* FUNCTION: CommitOffsetOnFetch, CommitOffsetOnUpdate, CommitOffsetOnWrite
\*
\* Find the highest (contiguous) offset that has been replicated
\* to the leader's maximal ISR - nominally called the commit offset here
\* and is inclusive.

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
    GetCommitOffset(b, partition_metadata[b].maximal_isr, 
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
\* Conditionally advance the high watermark. To advance it, 
\* the ISR must be >= MinISR. 
\* Additionally in this proposal, the maximal ISR is only 
\* guaranteed to be a superset of the controller ISR + ELR when the
\* leader ISR >= MinISR. When the leader ISR is < MinISR, the 
\* leader may make an AlterPartition request such that the 
\* maximal ISR is not a superset. Therefore, while we use the 
\* maximal ISR to evaluate whether a record can be committed,
\* we don't advance the high watermark when the ISR < MinISR 
\* (because the maximal ISR may not be a superset and therefore 
\* not safe).
\* An example could be that the leader ISR={1} and the maximal
\* ISR={1,3} (with 3 being added) but the controller has 
\* ISR={1}, ELR={2}.

SafeToAdvanceHwm(b, isr) ==
   Cardinality(isr) >= MinISR

CanAdvanceHwm(b, isr, old_hwm, new_hwm) ==
    /\ new_hwm > old_hwm 
    /\ SafeToAdvanceHwm(b, isr)

NoHighWatermarkChange ==
    UNCHANGED << partition_data, inv_vars >>

\* Send producer acknowledgements for any records that this
\* replica wrote to its log (it knows this by matching its
\* current leader epoch to the epoch of the record).
SendAcksFor(b, lower, higher, ack_type) ==
    LET curr_epoch == partition_metadata[b].leader_epoch
        values == { v \in inv_sent : /\ v \notin inv_pos_acked
                                     /\ v \notin inv_neg_acked
                                     /\ \E offset \in lower..higher :
                                          /\ LogEntry(b, offset).value = v
                                          /\ LogEntry(b, offset).epoch = curr_epoch }
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
                    
MaybeAdvanceHighWatermark(b, isr, old_hwm, new_hwm, ack_type) ==
    IF CanAdvanceHwm(b, isr, old_hwm, new_hwm)
    THEN /\ partition_data' = [partition_data EXCEPT ![b].hwm = new_hwm]
         /\ UpdateHwmInvariantVars(b, old_hwm, new_hwm, ack_type)
         /\ UNCHANGED inv_sent
    ELSE NoHighWatermarkChange

\*-----------------------------------------------------------
\* FUNCTION: MaybeFailPendingWrites
\*
\* If the ISR is now below MinISR or the replica lost leadership
\* then negatively acknowledge all unacknowledged records from
\* the high watermark and up.

FailPendingWrites(b) ==
    SendAcksFor(b, HwmOf(b), LeoOf(b)-1, FALSE)

MaybeFailPendingWrites(b, part_state) ==
    IF /\ HwmOf(b) < LeoOf(b)
       /\ \/ Cardinality(part_state.isr) < MinISR
          \/ b # part_state.leader
    THEN FailPendingWrites(b)
    ELSE UNCHANGED << inv_sent, inv_pos_acked, inv_neg_acked >>

\*----------------------------------------------------------------
\* FUNCTION: MaybeUpdateHwmAndAckOnPartitionChange
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

MaybeUpdateHwmAndAckOnPartitionChange(b, part_md, is_new_leader) ==
    LET old_hwm == HwmOf(b)
        new_hwm == CommitOffsetOnUpdate(b, part_md.maximal_isr) + 1
        ack_type == IF Cardinality(part_md.maximal_isr) >= MinISR
                    THEN TRUE ELSE FALSE
    IN MaybeAdvanceHighWatermark(b, part_md.isr, old_hwm, new_hwm, ack_type)

\*--------------------------------------------------------------
\* FUNCTIONS: ApplyPartitionChange, NoPartitionChange
\*
\* - ApplyPartitionChange: When a partition state change is required,
\*   the controller does two things: update the in-memory state and
\*   append a PartitionChangeRecord to the metadata log.
\*   If the ISR is now >= MinISR then empty the LastKnownELR set.  
\*   Else if any ELR members got removed (but not from the replica 
\*   set itself) then add them to the LastKnownELR.

NoPartitionChange ==
    UNCHANGED << con_partition_metadata, con_metadata_log >>

ApplyPartitionChange(new_replicas, new_leader, new_isr, new_elr,
                     leader_epoch, part_epoch, adding, removing) ==
    LET last_known_elr == IF Cardinality(new_isr) >= MinISR
                          THEN {}
                          ELSE con_partition_metadata.last_known_elr 
                                \union (new_replicas \intersect
                                       (con_partition_metadata.elr \ new_elr))
    IN
        /\ con_partition_metadata' = 
                   [replicas        |-> new_replicas,
                    isr             |-> new_isr,
                    elr             |-> new_elr,
                    last_known_elr  |-> last_known_elr,
                    leader          |-> new_leader,
                    leader_epoch    |-> leader_epoch,
                    partition_epoch |-> part_epoch,
                    adding          |-> adding,
                    removing        |-> removing]
        /\ con_metadata_log' = 
              Append(con_metadata_log,
                    [type            |-> PartitionChangeRecord,
                     replicas        |-> new_replicas,
                     isr             |-> new_isr,
                     elr             |-> new_elr,
                     last_known_elr  |-> last_known_elr,
                     leader          |-> new_leader,
                     leader_epoch    |-> leader_epoch,
                     partition_epoch |-> part_epoch,
                     adding          |-> adding,
                     removing        |-> removing])

\*------------------------------------------------------------------
\* FUNCTIONS: UpdateElrOnIsrChange, RemoveBrokerFromISR
\*
\* - UpdateElrOnIsrChange: Two-phase process of updating the ELR.
\*    - First, remove from the ELR any members of the proposed ISR. 
\*    - Second, then recursively update the ELR to ensure that the
\*      combined cardinality of the ISR + ELR is <= MinISR.
\* - RemoveBrokerFromISR: There are no restrictions on removal,
\*   the ISR can be empty in this proposal.

UpdateElr(elr, original_isr, proposed_isr, replicas) ==
    LET original_isr1    == original_isr \intersect replicas \* reassignment can remove replicas
        removed_from_isr == original_isr1 \ proposed_isr
        elr1             == elr \intersect replicas 
    IN IF Cardinality(proposed_isr) >= MinISR 
       THEN {} 
       ELSE elr1 \union removed_from_isr                           
        
UpdateElrOnIsrOrReplicaChange(proposed_isr, replicas) ==
    UpdateElr(con_partition_metadata.elr,
              con_partition_metadata.isr,
              proposed_isr,
              replicas)

\* The ISR can become empty
RemoveBrokerFromISR(isr, b) ==
    isr \ {b}

\*--------------------------------------------------------------
\* FUNCTION: MaybeUpdatePartitionOnBrokerChange

\* TRUE iff no leader change is required    
NoLeaderChange(new_isr, new_elr, new_unfenced) ==
    \* either there is no leader and there is no leader candidate either
    \/ /\ con_partition_metadata.leader = NoLeader
       /\ Cardinality(new_isr) = 0
       /\ ~\E candidate \in new_elr : candidate \in new_unfenced
    \* or the leader is in the new ISR, so no change needed
    \/ con_partition_metadata.leader \in new_isr

\* Based on the new ISR and unfenced broker set, decide
\* whether a partition state change is required or not.
MaybeUpdatePartitionOnBrokerChange(new_isr, new_elr, new_unfenced) ==
    LET md == con_partition_metadata
    IN
        CASE /\ NoLeaderChange(new_isr, new_elr, new_unfenced)
             /\ new_isr = md.isr
             /\ new_elr = md.elr ->
                \* no-op
                NoPartitionChange
          [] /\ NoLeaderChange(new_isr, new_elr, new_unfenced)
             /\ \/ new_isr # md.isr
                \/ new_elr # md.elr ->
                \* basically, ISR/ELR change but no leader change. 
                ApplyPartitionChange(md.replicas, md.leader,  
                                     new_isr, new_elr, md.leader_epoch,
                                     md.partition_epoch + 1,
                                     md.adding, md.removing)
          [] Cardinality(new_isr) > 0 ->
            \* There is at least one replica in the ISR, so
            \* elect one non-deterministically.
            \E candidate \in new_isr :
                    ApplyPartitionChange(md.replicas, candidate, new_isr, new_elr,
                                         md.leader_epoch + 1,
                                         md.partition_epoch + 1,
                                         md.adding, md.removing)
          [] \E candidate \in new_elr : candidate \in new_unfenced ->
            \* There is at least one non-fenced leader candidate in the ELR,
            \* so elect one non-deterministically.
            \* Ensure this chosen leader is added to the new ISR and removed from
            \* the ELR.
            \E candidate \in new_elr :
                /\ candidate \in new_unfenced
                /\ LET new_isr2 == new_isr \union {candidate}
                       new_elr2 == new_elr \ {candidate}
                   IN ApplyPartitionChange(md.replicas, candidate, 
                                           new_isr2, new_elr2,
                                           md.leader_epoch + 1,
                                           md.partition_epoch + 1,
                                           md.adding, md.removing)
          [] ~\E candidate \in new_elr : candidate \in new_unfenced ->
                \* The ELR remains the same, but there is no leader.
                \* This is the case where all ELR replicas are now fenced.
                ApplyPartitionChange(md.replicas, NoLeader, new_isr, new_elr, 
                                     md.leader_epoch + 1,
                                     md.partition_epoch + 1,
                                     md.adding, md.removing)
          [] OTHER -> \* no-op 
                NoPartitionChange

\*--------------------------------------------------------------
\* FUNCTIONS: HandleBrokerFenced, HandleBrokerUnfenced

HandleBrokerFenced(b) ==
    LET new_isr      == RemoveBrokerFromISR(con_partition_metadata.isr, b)
        new_elr      == UpdateElrOnIsrOrReplicaChange(new_isr, con_partition_metadata.replicas)
        new_unfenced == con_unfenced \ {b}
    IN /\ MaybeUpdatePartitionOnBrokerChange(new_isr, new_elr, new_unfenced)
       /\ con_unfenced' = new_unfenced

HandleBrokerUnfenced(b) ==
    LET new_isr      == con_partition_metadata.isr \* unfencing doesn't change the ISR
        new_elr      == con_partition_metadata.elr \* unfencing doesn't change the ELR
        new_unfenced == con_unfenced \union {b}
    IN \* if there is no leader the controller can choose one from the ELR.
       /\ IF con_partition_metadata.leader = NoLeader 
          THEN MaybeUpdatePartitionOnBrokerChange(new_isr, new_elr, new_unfenced)
          ELSE NoPartitionChange
       /\ con_unfenced' = new_unfenced

\*--------------------------------------------------------------
\* FUNCTION: LastOffsetForEpoch

\* Find the highest epoch in the log <= the requested epoch, 
\* or use the required epoch if none is lower or equal. Then
\* find the start offset of the next highest epoch from that.
\* The offset is exclusive. See the protocol description for
\* a clearer explanation of this logic (which is much easier
\* than trying to under this TLA+ code).

NoEpochAndOffset == 
    [epoch |-> 0, offset |-> 0]

LastOffsetForEpoch(b, req_epoch, is_leader) ==
    IF \/ LogOf(b) = <<>> 
       \/ /\ LogOf(b) # <<>>
          /\ req_epoch = Last(LogOf(b)).epoch
       \/ /\ is_leader
          /\ partition_metadata[b].leader_epoch = req_epoch
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
                                   /\ partition_metadata[b].leader_epoch > req_epoch
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


\*--------------------------------------------------------------
\* FUNCTION: DropFetchSessions

\* Fetch requests are synchronous, one at a time and also protected 
\* by fetch sessions not modeled in this spec (to reduce additional
\* complexity) so we achieve the same properties by simply dropping 
\* all inflight fetch requests and responses where this broker is 
\* involved (to avoid these messages from being processed in the future).

DropFetchSessions(b) ==
    /\ messages' = [m \in DOMAIN messages |->
                        CASE /\ m.type \in {FetchRequest, FetchResponse}
                             /\ \/ m.dest = b
                                \/ m.source = b -> 0 \* delivery count 0
                          [] OTHER -> messages[m]]
    \* All fetcher state on this broker is lost. Also, the fetches fail on
    \* the brokers that have sent a fetch request to this broker.
    /\ broker_fetchers' = [b1 \in Brokers |->
                                CASE \* --- CASE local state lost --------------------------
                                     b = b1 ->
                                        [b2 \in Brokers |-> BlankFetchState]
                                  \* --- CASE remote broker fetch request fails ------------
                                  [] /\ broker_fetchers[b1][b].pending_response = TRUE
                                     /\ broker_fetchers[b1][b].partition # Nil ->
                                        [broker_fetchers[b1] EXCEPT ![b].pending_response = FALSE,
                                                                    ![b].partition.delayed = TRUE]
                                  \* --- CASE remote broker fetch request fails after removing partition --
                                  [] /\ broker_fetchers[b1][b].pending_response = TRUE
                                     /\ broker_fetchers[b1][b].partition = Nil ->
                                        [broker_fetchers[b1] EXCEPT ![b].pending_response = FALSE]
                                  \* --- CASE no change to unaffected fetch sessions --------
                                  [] OTHER -> broker_fetchers[b1]]
                                  \* CASE END


=============================================================================    