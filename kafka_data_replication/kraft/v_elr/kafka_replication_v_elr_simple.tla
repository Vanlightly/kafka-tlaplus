-------------------------- MODULE kafka_replication_v_elr_simple --------------------------

EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences, SequencesExt, TLC, 
        message_passing, 
        v_elr_types,
        v_elr_properties,
        v_elr_functions

(*
-------------------------------------------------------------------------------------
------- SIMPLIFIED Kafka data replication protocol with the KRaft Controller --------

Eligible Leader Replicas Proposal - Simplified

Models a proposed change to the replication protocol to enhance the recovery 
mechanism to better handle unclean shutdowns.

KIP has complete description: https://cwiki.apache.org/confluence/display/KAFKA/KIP-966%3A+Eligible+Leader+Replicas

Based on the kafka_replication_v3_5_simple.tla specification which omits
some parts of the protocol such as the complete broker lifecycle and heartbeats.

Jump to the bottom of the spec for the Next state formula which lists all
the actions.
*)

vars == << con_vars, broker_vars, part_vars, messages, inv_vars, aux_vars >>
view == << con_vars, broker_vars, part_vars, messages, inv_vars >>

\* ==================================================================
\*              ACTIONS
\* ==================================================================

(* ---------------------------------------------------------------
   ACTION: BrokerStart

   A stopped broker starts-up in the STARTING status and sends a 
   new broker registration request to the controller with a new 
   incarnation id. The purpose of the incarnation id is simply
   to avoid an automation error creating two brokers with the same
   node id.

   ++ PROPOSAL CHANGE +++++++++++++++++++++++++
   The broker reads its broker epoch from file and passes it in
   its broker registration request. If the file does not exist
   then pass the epoch as 0.
   ++++++++++++++++++++++++++++++++++++++++++++
   ---------------------------------------------------------------*)

SendBrokerRegistration(b) ==
    /\ Send([type           |-> RegisterBrokerRequest,
             broker_id      |-> b,
             \* PROPOSAL CHANGE - send any broker epoch on file
             broker_epoch   |-> broker_state[b].broker_epoch,
             incarnation_id |-> aux_ctrs.incarn_ctr,
             dest           |-> Controller,
             source         |-> b])
    \* increment the auxilliary incarnation counter to ensure unique incarnation ids
    /\ aux_ctrs' = [aux_ctrs EXCEPT !.incarn_ctr = @ + 1]

BrokerStart ==
    \E b \in Brokers :
        \* enabling conditions
        /\ broker_state[b].status \in { OFFLINE_CLEAN, OFFLINE_DIRTY }
        \* state mutations
        /\ broker_state' = [broker_state EXCEPT ![b] = 
                                [status            |-> STARTING,
                                 \* PROPOSAL CHANGE - keep any broker epoch on file unchanged
                                 broker_epoch      |-> broker_state[b].broker_epoch,
                                 incarnation_id    |-> aux_ctrs.incarn_ctr,
                                 registered        |-> FALSE]]
        /\ partition_status' = [partition_status EXCEPT ![b] = Nil]
        /\ SendBrokerRegistration(b)
        /\ UNCHANGED << con_vars, broker_fetchers, broker_metadata_log, 
                        partition_metadata, partition_data,
                        partition_replica_state, partition_pending_ap, 
                        inv_vars, aux_broker_epoch >>        

(* ---------------------------------------------------------------
   ACTION: ReceiveBrokerRegRequest

   The controller receives a RegisterBrokerRequest and
   only accepts it if:
   - there is no registration record (not modeled)
   - the broker is FENCED
   - the broker is not FENCED and the incarnation id matches
     the existing registration.
   
   ++ PROPOSAL CHANGE +++++++++++++++++++++++++++++
   In this proposal, if the request is from a broker with an existing
   broker registration but the broker_epoch of the request is 0,
   then the controller treats the broker as unclean. 
   
   Whether clean or unclean, the broker is assigned a broker epoch based
   on the last offset in the metadata log.
       
   If the broker is unclean, the broker is removed from partition
   leadership and any ISRs and ELRs (regardless of the MinISR).
   
   A broker is only removed from the ELR when either it starts up
   unclean, or it gets elected leader, or the combined size of the
   ISR + ELR > MinISR.
   +++++++++++++++++++++++++++++++++++++++++++++++++
   
   In this simplified spec, the full start-up sequence is omitted
   which results in the following differences:
    - The broker starts in the UNFENCED status.
    - No BrokerRegistration record is added to the metadata log. This
      necesitates a new variable aux_broker_epoch used for ensuring
      monotonic broker epochs.
      
   Note also in this spec, all brokers start already registered and
   the spec has no unregistration logic, so there is no check for
   broker registration existence. 
------------------------------------------------------------------*)

ProcessUncleanBroker(b) ==
    LET new_isr      == RemoveBrokerFromISR(con_partition_metadata.isr, b)
        new_elr      == con_partition_metadata.elr \ {b}
        new_unfenced == con_unfenced \union {b}
    IN /\ MaybeUpdatePartitionState(new_isr, new_elr, new_unfenced)
       /\ con_unfenced' = new_unfenced

ReceiveBrokerRegRequest ==
    \E m \in DOMAIN messages :
        \* enabling conditions
        /\ ReceivableMsg(m, RegisterBrokerRequest)
        /\ \/ con_broker_reg[m.source].status = FENCED
           \/ /\ con_broker_reg[m.source].status # FENCED
              /\ con_broker_reg[m.source].incarnation_id = m.incarnation_id
        \* state mutations
        /\ LET b              == m.source
               broker_epoch   == aux_broker_epoch + 1
            IN
                /\ IF m.broker_epoch = 0 \* AND a registration exists
                   THEN ProcessUncleanBroker(b)
                   ELSE HandleBrokerUnfenced(b) 
                /\ con_broker_reg' = [con_broker_reg EXCEPT ![b] =
                                            [status              |-> UNFENCED,
                                             broker_epoch        |-> broker_epoch,
                                             incarnation_id      |-> m.incarnation_id]]
                /\ Reply(m, 
                        [type            |-> RegisterBrokerResponse,
                         broker_epoch    |-> broker_epoch,
                         metadata_offset |-> Len(con_metadata_log), \* spec only field (see ReceiveBrokerRegResponse)
                         dest            |-> b,
                         source          |-> Controller])
                /\ aux_broker_epoch' = aux_broker_epoch + 1 \* used instead of metadata write offset
                /\ UNCHANGED << broker_vars, part_vars, inv_vars, aux_ctrs >>

(*---------------------------------------------------------------
  ACTION: ReceiveBrokerRegResponse

  A broker receives a RegisterBrokerResponse and updates its 
  broker epoch and registered state. 

  In this simplified spec, the full start-up sequence is omitted
  which results in the following differences:
  - The broker jumps straight to RUNNING.
  - The broker cannot catch-up with its own BrokerRegistration
    record as we do not model those records in this spec. However, 
    we must guarantee that the broker catches up to its own
    BrokerRegistration record before running as a fully functional
    broker. This is simulated here by:
    - catching up to the controller metadata log at the time of 
      registration but minus one record.
    - Not initializing the partition 
    We leave it to the ReceiveMetadataUpdate action to receive the
    metadata record of the time of registration and correctly 
    initializing the partition replica.

    NO PROPOSAL CHANGE
----------------------------------------------------------------*)

__CatchUpBarOne(b, m) ==
    LET log == IF m.metadata_offset <= 1
               THEN <<>>
               ELSE SubSeq(con_metadata_log, 1, m.metadata_offset-1)
    IN /\ broker_metadata_log' = [broker_metadata_log EXCEPT ![b] = log]
       /\ partition_metadata' = [partition_metadata EXCEPT ![b] = 
                                    \* non-initialized partition
                                    [isr             |-> {},
                                     maximal_isr     |-> {},
                                     leader          |-> NoLeader,
                                     leader_epoch    |-> 0,
                                     partition_epoch |-> 0]] 

ReceiveBrokerRegResponse ==
    \E m \in DOMAIN messages :
        \* enabling conditions
        /\ ReceivableMsg(m, RegisterBrokerResponse)
        /\ broker_state[m.dest].registered = FALSE 
        \* state mutations
        /\ broker_state' = [broker_state EXCEPT ![m.dest] = 
                                [status         |-> RUNNING,
                                 broker_epoch   |-> m.broker_epoch,
                                 incarnation_id |-> broker_state[m.dest].incarnation_id,
                                 registered     |-> TRUE]]
        /\ __CatchUpBarOne(m.dest, m)
        /\ Discard(m)
        /\ UNCHANGED << con_vars, broker_fetchers, partition_status, partition_data,  
                        partition_replica_state, partition_pending_ap, 
                        inv_vars, aux_vars >>

(*--------------------------------------------------------------------
  ACTION: UnfenceBroker

  The controller unfences a fenced broker. In the implementation
  this would happen due to a heartbeat. This spec simply
  allows this to occur at any time to a fenced broker.

  ++ PROPOSAL CHANGE ++++++++++++++++++++++++++++++++++++
  The replicas of unfenced the broker will remain outside of the
  ISR unless:
    1. There is no current leader (ISR is empty).
    2. The replica is in the ELR.
  If the above two conditions are met, the replica can be
  made the new leader, being removed from the ELR and being
  placed in the ISR.
  +++++++++++++++++++++++++++++++++++++++++++++++++++++++
  
  In this simplified version, this unfence action replaces
  the heartbeat. As long as the broker is running, we simulate
  that heartbeats can be received without actually modeling them.
---------------------------------------------------------------------*)

UnfenceBroker ==
    \* enabling conditions
    \E b \in Brokers :
        /\ con_broker_reg[b].status = FENCED
        /\ broker_state[b].status = RUNNING
        \* state mutations
        /\ HandleBrokerUnfenced(b)
        /\ con_broker_reg' = [con_broker_reg EXCEPT ![b].status = UNFENCED]
        /\ UNCHANGED << broker_vars, part_vars, messages, inv_vars, 
                        aux_vars >>

(*--------------------------------------------------------------------
  ACTION: FenceBroker

  The controller fences an unfenced broker. In the implementation
  this would happen due to a lack of heartbeats. This spec simply
  allows this to occur at any time to an unfenced broker.

  A fenced broker is removed from any leadership. Also it is removed
  from any ISRs but not ELRs.

  ++ PROPOSAL CHANGE +++++++++++++++++++++++++++++
  In this proposal, the ISR can be empty.
  ++++++++++++++++++++++++++++++++++++++++++++++++
---------------------------------------------------------------------*)

FenceBroker ==
    \* enabling conditions
    /\ aux_ctrs.fence_broker_ctr < FenceBrokerLimit
    /\ \E b \in Brokers :
        /\ con_broker_reg[b].status = UNFENCED
        \* state mutations
        /\ HandleBrokerFenced(b)
        /\ con_broker_reg' = [con_broker_reg EXCEPT ![b].status = FENCED]
        /\ aux_ctrs' = [aux_ctrs EXCEPT !.fence_broker_ctr = @ + 1]
        /\ UNCHANGED << broker_vars, part_vars, messages, inv_vars,
                        aux_broker_epoch >>

(*-----------------------------------------------------------------------
  ACTION: ReceiveMetadataUpdate

  NOTE! This action contains a lot of logic.

  In this simplified spec, only PartitionChange records are added to the 
  metadata log and brokers receive metadata records one at a time. When a 
  broker receives a PartionChange metadata record it can take various 
  actions:
   - It may have become the partition leader in a new leader epoch:
        - records the start offset for this leader epoch (the LEO on 
          becoming leader).
        - If it is a follower->leader change then remove the partition
          from any fetcher it is added to.
   - It may have retained leadership in the same leader epoch and the 
     metadata change relates to the ISR only:
        - it may need to advance the HWM.
   - It may have remained a follower in the same leader epoch:
        - do nothing
   - It may have become a follower in a new leader epoch:
        - Adds the partition to the right fetcher and removes the partition
          from any other fetcher if it exists. 
        - The follower does not perform truncation, this spec implements
          the diverging epoch on fetch.
   - There may be no leader, so it simply waits for the next PartionChangeRecord.
   - Uncommitted pending writes may need to be negatively acknowledged:
       - if the replica has lost leadership
       - the ISR has shrunk below minISR.

    NO PROPOSAL CHANGE
-----------------------------------------------------------------------*)           

\* Add the partition to the fetcher in the case that:
\*    - this is a new leader epoch.
\*    - the partition has not already been added.
\* Adding the partition to one fetcher removes it from another,
\* if it existed on another. The Last Fetch Epoch is set to the
\* epoch of the last record in the log.
AddPartitionToFetcher(b, leader, leader_epoch) ==
    IF \/ leader_epoch > PartitionMetadata(b).leader_epoch
       \/ ~IsPartitionAdded(b, leader)
    THEN LET add_partition == [fetch_offset       |-> LeoOf(b),
                               last_fetched_epoch |-> IF LogOf(b) = <<>> 
                                                      THEN 0
                                                      ELSE Last(LogOf(b)).epoch,
                               delayed            |-> FALSE]
             fetcher       == broker_fetchers[b][leader]
         IN 
            broker_fetchers' = [broker_fetchers EXCEPT ![b] =
                                    [peer \in Brokers |->
                                        [broker_fetchers[b][peer] EXCEPT 
                                            !.partition = IF peer = leader
                                                          THEN add_partition
                                                          ELSE Nil]]]
    ELSE UNCHANGED << broker_fetchers >>

RemovePartitionFromFetchers(b) ==
    broker_fetchers' = [broker_fetchers EXCEPT ![b] =
                            [b1 \in Brokers |-> 
                                [partition        |-> Nil,
                                 \* leave this unchanged
                                 pending_response |-> Fetcher(b, b1).pending_response]]]

NoFetcherChanges ==
    UNCHANGED broker_fetchers

IsLeaderEpochBump(b, md_offset) ==
    con_metadata_log[md_offset].leader_epoch > PartitionMetadata(b).leader_epoch

\* As leader we care about every partition change but as follower
\* we only care about leader epoch changes (as a state space reduction).
ExistMetadataUpdates(b) ==
    /\ Len(broker_metadata_log[b]) < Len(con_metadata_log)
    /\ IF partition_status[b] = Leader
       THEN TRUE
       ELSE \E md_offset \in Len(broker_metadata_log[b])+1..Len(con_metadata_log) :
                IsLeaderEpochBump(b, md_offset)
       

\* As leader we care about every partition change but as follower
\* we only care about leader epoch changes (as a state space reduction)
\* so we skip any records that are ISR only changes.
RECURSIVE NextMetadataRecord(_,_)
NextMetadataRecord(b, md_offset) ==
    IF \/ partition_status[b] = Leader 
       \/ IsLeaderEpochBump(b, md_offset)
    THEN [record |-> con_metadata_log[md_offset],
          offset |-> md_offset]
    ELSE NextMetadataRecord(b, md_offset + 1)
    
\* Ensure all state related to former leadership is clear    
EnsureLeadershipRenounced(b, new_part_md) ==
    /\ MaybeFailPendingWrites(b, new_part_md)
    /\ ResetReplicaState(b, FALSE)
    /\ ResetPendingAlterPartition(b)    
    
\* The replica remains leader, all it must do is conditionally advance the HWM.
RemainLeader(b, new_part_md) ==
    /\ MaybeUpdateHwmOnPartitionChange(b, new_part_md)
    /\ IF new_part_md.partition_epoch >= partition_pending_ap[b].epoch
       THEN ResetPendingAlterPartition(b)
       ELSE UNCHANGED partition_pending_ap
    /\ UNCHANGED << partition_status, partition_replica_state, broker_fetchers>>

\* The replica has become a leader in a new leader epoch. This includes
\* a leader being reelected in a new leader epoch. So it must set its
\* Epoch Start Offset, reset any peer replica state and remove the
\* partition from any fetcher if it is added.   
BecomeLeaderInNewEpoch(b) ==
    /\ partition_status' = [partition_status EXCEPT ![b] = Leader]
    /\ partition_data' = [partition_data EXCEPT ![b].epoch_start_offset = LeoOf(b)]
    /\ ResetReplicaState(b, TRUE)
    /\ ResetPendingAlterPartition(b)
    /\ RemovePartitionFromFetchers(b)
    /\ UNCHANGED << inv_vars >>

\* The replica is still a follower in the same leader epoch. So do nothing.     
RemainFollower ==
    UNCHANGED << partition_status, partition_data, partition_replica_state, 
                 partition_pending_ap, broker_fetchers, inv_vars >>

\* The replica has become a follower and adds the partition to the right fetcher
\* setting its fetch offset to its current LEO. If log truncation is required,
\* it will occur on its first fetch response.        
BecomeFollowerInNewEpoch(b, new_part_md) ==
    /\ partition_status' = [partition_status EXCEPT ![b] = Follower]
    /\ AddPartitionToFetcher(b, new_part_md.leader, new_part_md.leader_epoch)
    \* in case it was formerly a leader
    /\ EnsureLeadershipRenounced(b, new_part_md)
    /\ UNCHANGED << partition_data, inv_true_hwm, inv_consumed >>
    
\* The replica learns there is no leader, so waits in limbo until
\* it gets new information.    
WaitForLeaderChange(b, new_part_md) ==
    /\ partition_status' = [partition_status EXCEPT ![b] = Nil]
    /\ RemovePartitionFromFetchers(b)
    \* in case it was formerly a leader
    /\ EnsureLeadershipRenounced(b, new_part_md)
    /\ UNCHANGED << partition_data, inv_true_hwm, inv_consumed >>

MetadataNoOp ==
    UNCHANGED << part_vars, broker_fetchers, inv_vars >>

ReceiveMetadataUpdate ==
    \E b \in Brokers :
        LET curr_md_offset == Len(broker_metadata_log[b])
            metadata       == NextMetadataRecord(b, curr_md_offset + 1)
            append_records == SubSeq(con_metadata_log, curr_md_offset + 1, metadata.offset) 
            curr_part_md   == PartitionMetadata(b)
            new_part_md    == [isr             |-> metadata.record.isr,
                               maximal_isr     |-> metadata.record.isr,
                               leader          |-> metadata.record.leader,
                               leader_epoch    |-> metadata.record.leader_epoch,
                               partition_epoch |-> metadata.record.partition_epoch]
        IN
            \* enabling conditions
            /\ ExistMetadataUpdates(b)
            /\ broker_state[b].status \notin {OFFLINE_CLEAN, OFFLINE_DIRTY}
            /\ broker_state[b].registered = TRUE
            \* state mutations
            /\ broker_metadata_log' = [broker_metadata_log EXCEPT ![b] = @ \o append_records]
               \* If the last PartitionChangeRecord has a higher partition epoch, then update 
               \* the local partition state and possibly become a leader or follower.
               \* The partition epoch will not be lower if the change is the result of a completed
               \* PartitionChange request and the response was already processed.
            /\ IF new_part_md.partition_epoch > curr_part_md.partition_epoch
               THEN
                    /\ partition_metadata' = [partition_metadata EXCEPT ![b] = new_part_md]
                    /\ CASE 
                         \* CASE --- Remains leader --------------------------------
                            /\ PartitionMetadata(b).leader = b
                            /\ metadata.record.leader = b -> 
                                IF PartitionMetadata(b).leader_epoch = new_part_md.leader_epoch
                                THEN \* Remains leader in the same leader epoch
                                     RemainLeader(b, new_part_md)
                                ELSE \* Leader reelected in a new leader epoch
                                     BecomeLeaderInNewEpoch(b)
                         \* CASE --- Follower elected as leader----------------------
                         [] /\ PartitionMetadata(b).leader # b
                            /\ metadata.record.leader = b ->
                                BecomeLeaderInNewEpoch(b)
                         \* CASE --- Chosen as a follower ---------------------------
                         [] /\ metadata.record.leader # NoLeader ->
                                IF /\ new_part_md.leader_epoch = curr_part_md.leader_epoch
                                   /\ curr_part_md.leader # b
                                   /\ new_part_md.leader # b
                                THEN RemainFollower
                                ELSE BecomeFollowerInNewEpoch(b, new_part_md)
                         \* CASE --- No leader chosen -------------------------------
                         [] OTHER ->
                                WaitForLeaderChange(b, new_part_md)
                         \* END CASE
               ELSE MetadataNoOp
            /\ UNCHANGED << con_vars, broker_state, messages, aux_vars >>

(*--------------------------------------------------------------------------
  ACTION: SendAlterPartitionRequest

  The leader tries to modify the ISR. 

  The leader first identifies all replicas that are caught up and adds
  them to the proposed ISR. The definition of "caught up" is that:
    a. The replica has not timed out.
    b. The replica fetch offset is >= HWM.
    c. The replica fetch offset is >= Start Epoch Offset.
  
  We simulate timed out followers without actually tracking fetch
  requests. Instead we simply allow a non-deterministic subset of
  the followers to be treated as timed-out. This is done via
  "\E timed_out_followers \in SUBSET Brokers" which translates to
  "there exists some subset of the brokers" and the model checker 
  will explore all subsets.
  
  The leader builds an AlterPartitionRequest, including the broker 
  epochs of itself and any added replicas in the proposed ISR. 
  The reason why we don't need to set the broker epoch for existing
  ISR followers is that if an ISR follower is now no longer valid,
  the partition epoch will have been incremented by the controller
  and the AlterPartition request that is attempting to include a 
  non-valid ISR member will be rejected due to a stale Partition epoch. 
  
  The leader eagerly applies the maximal ISR but leaves the ISR unchanged.
  The maximal ISR is the union of the proposed ISR with the current ISR.

  NO PROPOSAL CHANGE
--------------------------------------------------------------------------*)  

\* Create a map of broker id -> broker epoch. Set all current ISR
\* member epochs to 0 (-1 in the implementation), only set the
\* broker epoch of new members and the leader.
IsrAndEpochs(b, proposed_isr, curr_isr) ==
    [b1 \in proposed_isr 
        |-> CASE 
              \* --- CASE member is the leader ------------------------
                 b = b1 -> broker_state[b].broker_epoch
              \* --- CASE member is in the current ISR (i.e. not added) --
              [] b1 \in curr_isr -> 0
              \* --- CASE member is added --------------------------------
              [] OTHER -> partition_replica_state[b][b1].broker_epoch]
              \* END CASE

\* For a follower to be caught up:
FollowerIsCaughtUp(b, follower, follower_leo, timed_out_followers) ==
    \* The leader must have received a fetch request from the follower
    /\ follower_leo # Nil
    \* The follower must have reached the high watermark
    /\ follower_leo >= HwmOf(b)
    \* The follower must have reached the epoch start offset
    /\ follower_leo >= PartitionData(b).epoch_start_offset
    \* The follower cannot have timed out
    /\ follower \notin timed_out_followers

SendAlterPartitionRequest ==
    \* enabling conditions
    /\ aux_ctrs.alter_part_ctr < AlterPartitionLimit
    /\ \E b \in Brokers :
        /\ broker_state[b].status = RUNNING
        /\ ~PendingAlterPartitionResponse(b)
        /\ partition_status[b] = Leader
        /\ \E timed_out_followers \in SUBSET Brokers :
            /\ b \notin timed_out_followers
            /\ LET curr_isr     == PartitionMetadata(b).isr
                   proposed_isr == { b1 \in Brokers : \/ b1 = b 
                                                      \/ FollowerIsCaughtUp(b, b1,
                                                            partition_replica_state[b][b1].leo,
                                                            timed_out_followers) }
                   ap_request   == [type            |-> AlterPartitionRequest,
                                    isr             |-> proposed_isr,
                                    isr_and_epochs  |-> IsrAndEpochs(b, proposed_isr, curr_isr),
                                    leader          |-> b,
                                    leader_epoch    |-> PartitionMetadata(b).leader_epoch,
                                    partition_epoch |-> PartitionMetadata(b).partition_epoch,
                                    broker_epoch    |-> broker_state[b].broker_epoch,
                                    source          |-> b,
                                    dest            |-> Controller]
               IN 
                  /\ proposed_isr # curr_isr
                  \* state mutations
                  /\ Send(ap_request)
                  /\ partition_metadata' = [partition_metadata EXCEPT ![b].isr = curr_isr, \* we do not update this yet
                                                                      ![b].maximal_isr = 
                                                                            proposed_isr \union curr_isr]
                  /\ partition_pending_ap' = [partition_pending_ap EXCEPT ![b] = 
                                                    [epoch   |-> PartitionMetadata(b).partition_epoch + 1,
                                                     request |-> ap_request]]
                  /\ aux_ctrs' = [aux_ctrs EXCEPT !.alter_part_ctr = @ + 1]
                  /\ UNCHANGED << con_vars, broker_vars, partition_data, partition_replica_state, 
                                  partition_status, inv_vars, aux_broker_epoch >>

(*--------------------------------------------------------------------------
  ACTION: ReceiveAlterPartitionRequest

  The controller receives an AlterPartition request.

  It accepts the request if:
  - the request is from the current partition leader.
  - the broker epoch of the leader matches.
  - the leader epoch matches.
  - the broker epoch of all brokers in the proposed ISR matches
    or the supplied broker epoch is 0 (-1 in the implementation).
  - All brokers in the proposed ISR are active and unfenced.

  The leader epoch is not incremented as this spec only models
  leader epoch changes when a leader change has occurred,
  else it remains the same. Note, this is looser than the current
  implemention in 3.5.
  
  The controller sends a response with the new state of the ISR.
      
  ++ PROPOSAL CHANGE +++++++++++++++++++++++++++++++++
  Based on the new proposed ISR, the ELR is modified so
  that if possible the cardinality of ISR + ELR is equal
  to Min ISR.
      - if the proposed ISR >= MinISR then make the ELR empty.
      - if the proposed ISR + current ELR = MinISR then leave
        the ELR untouched.
      - else if proposed ISR + current ELR < MinISR AND this
        partition change is a shrinkage, then add replicas
        that have been removed such that the ISR + ELR = MinISR.
        (Note this is safe because when ISR < Min ISR the
        high watermark cannot advance.)
  ++++++++++++++++++++++++++++++++++++++++++++++++++++    
---------------------------------------------------------------------------*)

IsEligibleBroker(b, broker_epoch) ==
    /\ con_broker_reg[b].status = UNFENCED
    /\ \/ broker_epoch = 0
       \/ con_broker_reg[b].broker_epoch = broker_epoch
    
EligibleIsr(m) ==
    \A b \in DOMAIN m.isr_and_epochs :
        IsEligibleBroker(b, m.isr_and_epochs[b])    

ValidateRequest(b, m) ==
    IF /\ b = con_partition_metadata.leader
       /\ m.broker_epoch = con_broker_reg[b].broker_epoch
       /\ m.partition_epoch = con_partition_metadata.partition_epoch
       /\ m.leader_epoch = con_partition_metadata.leader_epoch
    THEN IF EligibleIsr(m)
         THEN Nil
         ELSE IneligibleReplica
    ELSE FencedLeaderEpoch

ReceiveAlterPartitionRequest ==
    \E m \in DOMAIN messages : 
        \* enabling conditions
        /\ ReceivableMsg(m, AlterPartitionRequest)
        /\ LET b == m.source
               new_ldr_epoch  == con_partition_metadata.leader_epoch \* unchanged
               new_part_epoch == con_partition_metadata.partition_epoch +1
               \* first remove any ELR members that are in the proposed ISR
               new_elr        == UpdateElrOnIsrChange(m.isr)
               error          == ValidateRequest(b, m)
           IN
              \* state mutations
              /\ IF error = Nil
                 THEN \* apply the requested partition state change
                      /\ con_partition_metadata' =
                                           [isr             |-> m.isr,
                                            elr             |-> new_elr,
                                            leader          |-> m.leader,
                                            leader_epoch    |-> new_ldr_epoch,
                                            partition_epoch |-> new_part_epoch]
                      /\ con_metadata_log' = Append(con_metadata_log, 
                                                  [type            |-> PartitionChangeRecord,
                                                   isr             |-> m.isr,
                                                   elr             |-> new_elr,
                                                   leader          |-> m.leader,
                                                   leader_epoch    |-> new_ldr_epoch,
                                                   partition_epoch |-> new_part_epoch])
                      /\ Reply(m,
                              [type            |-> AlterPartitionResponse,
                               error           |-> Nil,
                               isr             |-> m.isr,
                               leader          |-> m.leader,
                               leader_epoch    |-> new_ldr_epoch,
                               partition_epoch |-> new_part_epoch,
                               request         |-> m, \* not actually part of the message, 
                                                      \* a trick used for correlation in this spec.
                               dest            |-> b,
                               source          |-> Controller])
                 ELSE \* Reject the request by sending an error code back to the replica 
                      /\ Reply(m,
                              [type            |-> AlterPartitionResponse,
                               error           |-> error,
                               request         |-> m, \* not actually part of the message, 
                                                      \* a trick used for correlation in this spec.
                               dest            |-> b,
                               source          |-> Controller])
                      /\ UNCHANGED << con_partition_metadata, con_metadata_log>>
        /\ UNCHANGED << con_broker_reg, con_unfenced, broker_vars, 
                        part_vars, aux_vars, inv_vars >>
              

(*------------------------------------------------------------------------------
  ACTION: ReceiveAlterPartitionResponse

  A broker receives an AlterPartition response. 

  If the response is ignored in the following cases:
    - The response does not match the requested change
    - Has a Nil error code but the partition epoch is not higher.
      This happens when a metadata update for this change was
      processed before receiving the AlterPartition response.
   
  If the response matches the expected requested change, and indicates 
  success then updates its local partition state. If the response 
  indicates an IneligibleReplica or FencedEpoch, it rolls back its 
  eagerly applied partition state change, reverting to the last 
  partition state.

  NO PROPOSAL CHANGE
--------------------------------------------------------------------------------*)

CommitPartitionChange(b, part_state) ==
    /\ partition_metadata' = [partition_metadata EXCEPT ![b] = part_state]
    /\ MaybeUpdateHwmOnPartitionChange(b, part_state)

CompletePartitionChange(b, m) ==
    CommitPartitionChange(b, [isr             |-> m.isr,
                              maximal_isr     |-> m.isr,
                              leader          |-> m.leader,
                              leader_epoch    |-> m.leader_epoch,
                              partition_epoch |-> m.partition_epoch])

RollbackPartitionChange(b) ==
    LET last_part_state == [PartitionMetadata(b) EXCEPT !.maximal_isr =   
                                    PartitionMetadata(b).isr]                      
    IN CommitPartitionChange(b, last_part_state)

ReceiveAlterPartitionResponse ==
    \E m \in DOMAIN messages : 
        \* enabling conditions
        /\ ReceivableMsg(m, AlterPartitionResponse)
        /\ LET b == m.dest
           IN
              /\ broker_state[b].status = RUNNING
              /\ partition_status[b] = Leader
              /\ PendingAlterPartitionResponse(b)
              /\ partition_pending_ap[b].request = m.request
              /\ IF m.error = Nil
                 THEN m.partition_epoch > PartitionMetadata(b).partition_epoch
                 ELSE TRUE
              \* state mutations
              /\ IF m.error = Nil 
                 THEN CompletePartitionChange(b, m)
                 ELSE RollbackPartitionChange(b)
              /\ ResetPendingAlterPartition(b)
              /\ Discard(m)
        /\ UNCHANGED << con_vars, broker_vars, partition_status, 
                        partition_replica_state, aux_vars >>

(*-----------------------------------------------------------------------
  ACTION: SendFetchRequest

  A follower sends a fetch request to the partition leader.
  To avoid an infinite cycle of fetch request and responses
  we limit fetch requests to when a request can help the
  cluster make progress.
  
  The fetch request includes the fetch offset to indicate what
  records the partition needs and the last_fetched_epoch that
  the leader will use to detect log divergence.

  NO PROPOSAL CHANGE
---------------------------------------------------------------------*)

SendFetchRequest ==
    \E from, to \in Brokers :
        \* enabling conditions
        /\ from # to
        /\ broker_state[from].status = RUNNING         \* The broker is running
        /\ Fetcher(from, to).partition # Nil           \* The fetcher has the partition added
        /\ Fetcher(from, to).pending_response = FALSE  \* The fetcher is not waiting for a response
        /\ PartitionMetadata(from).leader = to         \* This replica believes the destination 
                                                       \* broker hosts the leader replica
        /\ __SendFetchMakesProgress(from) \* prevents infinite cycles
        \* state mutations
        /\ Send([type               |-> FetchRequest,
                 broker_epoch       |-> broker_state[from].broker_epoch,
                 partition |-> \* only one partition modeled
                    [leader_epoch       |-> PartitionMetadata(from).leader_epoch,
                     fetch_offset       |-> Fetcher(from, to).partition.fetch_offset,
                     last_fetched_epoch |-> Fetcher(from, to).partition.last_fetched_epoch],
                 dest               |-> to,
                 source             |-> from])
        /\ broker_fetchers' = [broker_fetchers EXCEPT ![from][to].pending_response = TRUE,
                                                      ![from][to].partition.delayed = FALSE]
        /\ UNCHANGED << con_vars, broker_state, broker_metadata_log, 
                        part_vars, inv_vars, aux_vars >>
        
(*----------------------------------------------------------------------------
  ACTION: ReceiveFetchRequest
  
  A broker receives a fetch request and responds with a fetch response. 
  
  The fetch response is determined by the results of partition validation and 
  a diverging epoch check. One of the following will occur:
  - If the broker does not host the partition leader or the leader epoch does
    not match then reply with an error code.
  - If the fetch_offset and last_fetched_epoch are not consistent with the 
    partition log then reply with a diverging epoch.
  - If all matches up then the leader will return the next log record in its response. 
  
  The partition replica may advance the high watermark based on the fetch 
  offset in the fetch request. The broker includes the HWM in fetch response.
  
  This spec only sends one record at a time.

  ++ PROPOSAL CHANGES +++++++++++++++++++++++++++++++++++
  The high watermark can only advance when ISR >= MinISR.
  There are two reasons for this:
     1. Before the ELR, we used to have the invariant that
        the maximal ISR was a superset of the ISR known to
        the controller. Basically, the controller couldn't
        elect a replica that was not part of the leader's
        maximal ISR.
        However, now the controller elects from the ISR + 
        ELR and the leader has no knowledge of the ELR. The
        maximal ISR may not be superset of the ISR + ELR
        when the ISR < MinISR. Therefore, we must ensure that
        the high watermark cannot advance when the leader's ISR
        (not maximal ISR) is less than Min ISR. For example,
        if: MinISR=2, ISR=[1], MaximalISR=[1,2] then the
        high watermark cannot advance.
     2. Before the ELR, if the last replica standing went
        down, then only it could be elected leader. That
        meant as long as the leader came back intact, then
        it was ok for the leader to advance the high watermark 
        even though the ISR was 1 replica (as we guaranteed that
        the same replica that advanced the high watermark became
        leader again).
        However, with the ELR, if the last replica standing
        goes down, it is possible a different replica (from
        the ELR) gets elected. If the former leader had advanced
        the high watermark, then the new leader wouldn't have 
        known about that, and we would break the monotonicity of
        the real high watermark.
  +++++++++++++++++++++++++++++++++++++++++++++++++++++++
---------------------------------------------------------------------*)  

ReceiveFetchRequest ==
    \E m \in DOMAIN messages :
        \* enabling conditions
        /\ ReceivableMsg(m, FetchRequest)
        /\ __ReceiveFetchMakesProgress(m)
        /\ LET b          == m.dest
               last_epoch == LastOffsetForEpoch(b, m.partition.last_fetched_epoch, TRUE)
           IN
              /\ broker_state[b].status = RUNNING
              \* state mutations
              /\ CASE \* --- CASE stale leader/not leader/fenced leader epoch ---------------
                      \/ partition_status[b] # Leader
                      \/ PartitionMetadata(b).leader_epoch # m.partition.leader_epoch ->
                          \* In the case of being a stale leader, don't do any state changes,
                          \* wait for the metadata update to bring this stale leader up to date.        
                          /\ Reply(m,
                                    [type             |-> FetchResponse,
                                     partition |-> \* only one partition modeled
                                        [error           |-> CASE PartitionMetadata(b).leader_epoch < 
                                                                            m.partition.leader_epoch -> UnknownLeaderEpoch
                                                               [] PartitionMetadata(b).leader_epoch > 
                                                                            m.partition.leader_epoch -> FencedLeaderEpoch
                                                               [] OTHER                              -> NotLeaderOrFollower,
                                         leader_epoch    |-> PartitionMetadata(b).leader_epoch,
                                         fetch_offset    |-> m.partition.fetch_offset,
                                         diverging_epoch |-> Nil,
                                         hwm             |-> HwmOf(b),
                                         records         |-> <<>>],
                                     dest             |-> m.source,
                                     source           |-> m.dest])
                          /\ UNCHANGED << partition_replica_state, partition_data, inv_vars >> 
                   \* --- CASE diverging epoch ------------------------------------------
                   [] \/ last_epoch.epoch < m.partition.last_fetched_epoch
                      \/ last_epoch.offset < m.partition.fetch_offset ->
                          /\ Reply(m,
                                    [type             |-> FetchResponse,
                                     partition |-> \* only one partition modeled
                                        [error           |-> Nil,
                                         leader_epoch    |-> PartitionMetadata(b).leader_epoch,
                                         fetch_offset    |-> m.partition.fetch_offset,
                                         diverging_epoch |-> last_epoch,
                                         hwm             |-> HwmOf(b),
                                         records         |-> <<>>],
                                     dest             |-> m.source,
                                     source           |-> m.dest])
                          /\ UNCHANGED << partition_replica_state, partition_data, inv_vars >>
                   \* --- CASE OK -------------------------------------------------------
                   [] OTHER -> 
                          LET updated_rep_state == [partition_replica_state[b] EXCEPT ![m.source] =
                                                        [leo              |-> m.partition.fetch_offset,
                                                         broker_epoch     |-> m.broker_epoch]]
                              old_hwm == HwmOf(b)
                              max_committed == HighestCommitted(b, partition_metadata[b].maximal_isr, 
                                                                updated_rep_state)
                              new_hwm == IF CanAdvanceHwm(b, partition_metadata[b].isr,
                                                          old_hwm, max_committed + 1)
                                         THEN max_committed + 1
                                         ELSE old_hwm
                          IN
                              /\ MaybeAdvanceHighWatermark(b, partition_metadata[b].isr,
                                                           old_hwm, new_hwm, TRUE)
                              /\ partition_replica_state' = [partition_replica_state EXCEPT ![b] = updated_rep_state]
                              /\ Reply(m,
                                        [type             |-> FetchResponse,
                                         partition |-> \* only one partition modeled
                                            [type            |-> FetchResponse,
                                             error           |-> Nil,
                                             leader_epoch    |-> PartitionMetadata(b).leader_epoch,
                                             fetch_offset    |-> m.partition.fetch_offset,
                                             diverging_epoch |-> Nil,
                                             hwm             |-> IF new_hwm > old_hwm
                                                                 THEN new_hwm ELSE old_hwm,
                                             records         |-> IF m.partition.fetch_offset < LeoOf(b)
                                                                 THEN <<LogEntry(b, m.partition.fetch_offset)>> 
                                                                 ELSE <<>>], 
                                         dest             |-> m.source,
                                         source           |-> m.dest])
                    \* CASE END ------------------------------------------
              /\ UNCHANGED << con_vars, broker_state, broker_fetchers, broker_metadata_log,
                              partition_metadata, partition_status, partition_pending_ap, aux_vars >>        

(*-------------------------------------------------------------------
  ACTION: ReceiveFetchResponse

  A broker receives a fetch response. 
  
  The following behavior can occur:
  - If the local replica is no longer a follower
        or this fetcher no longer hosts the partition
        or the fetch offset doesn't match
    then this is basically a no-op.
  - If the response contains an error, then set delayed=TRUE.
    In this spec this postpones the next fetch request to when the follower
    and leader are on the same leader epoch - this prevents an infinite
    cycle of fetch and error response.
  - If the diverging epoch is set then the follower truncates its log.
  - Else, if all is ok, the follower:
        a. appends the record to its log.
        b. updates the high watermark if the response HWM falls within
           the bounds of the log. This means that the high watermark
           on a follower is not monotonic.

    NO PROPOSAL CHANGES
---------------------------------------------------------------------*)  

FindTruncatePoint(b, diverging_epoch) ==
    LET local_last_epoch == LastOffsetForEpoch(b, diverging_epoch.epoch, FALSE)
    IN
        IF local_last_epoch.epoch # diverging_epoch.epoch
        THEN local_last_epoch.offset
        ELSE IF local_last_epoch.offset < diverging_epoch.offset
             THEN local_last_epoch.offset 
             ELSE diverging_epoch.offset

\* Truncate the log to the highest consistent offset that both leader and follower share
TruncateToSafePoint(b, diverging_epoch) ==
    LET truncate_to == FindTruncatePoint(b, diverging_epoch)
    IN IF truncate_to > 1
       THEN [log                |-> [offset \in 1..truncate_to-1 |-> LogEntry(b, offset)],
             leo                |-> truncate_to,
             hwm                |-> HwmOf(b), \* truncating does not affect the hwm
             epoch_start_offset |-> Nil] 
       ELSE [log |-> <<>>, hwm |-> HwmOf(b), leo |-> 1, epoch_start_offset |-> Nil]

IsFollowerOf(b, leader) ==
    /\ partition_status[b] = Follower
    /\ broker_fetchers[b][leader].partition # Nil

ReceiveFetchResponse ==
    \E m \in DOMAIN messages :
        \* enabling conditions
        /\ ReceivableMsg(m, FetchResponse)
        /\ LET b       == m.dest
           IN
              /\ broker_state[b].status = RUNNING
              /\ Fetcher(b, m.source).pending_response = TRUE
              \* state mutations
              /\ CASE
                   \* --- CASE NoOp ------------------------------------------
                      \* The local replica is longer a follower, or this fetcher
                      \* no longer hosts the partition or the fetch offset doesn't match.
                      \/ ~IsFollowerOf(b, m.source)
                      \/ /\ Fetcher(b, m.source).partition # Nil
                         /\ Fetcher(b, m.source).partition.fetch_offset # 
                                                    m.partition.fetch_offset ->
                          \* state mutations
                          /\ broker_fetchers' = [broker_fetchers EXCEPT 
                                                        ![b][m.source].pending_response = FALSE]
                          /\ UNCHANGED << partition_status, partition_data >>
                   \* --- CASE error -------------------------------------------------------
                   [] m.partition.error # Nil ->
                          \* state mutations
                          /\ broker_fetchers' = [broker_fetchers EXCEPT 
                                                        ![b][m.source].pending_response = FALSE,
                                                        ![b][m.source].partition.delayed = TRUE]
                          /\ UNCHANGED << partition_status, partition_data >> 
                   \* --- CASE diverging epoch ---------------------------------------------
                   [] m.partition.diverging_epoch # Nil ->
                          \* the follower log has diverged, truncate the log and update fetch state
                          LET after_trunc        == TruncateToSafePoint(b, m.partition.diverging_epoch)
                              last_fetched_epoch == IF after_trunc.log = <<>>
                                                    THEN 0
                                                    ELSE Last(after_trunc.log).epoch
                          IN  \* state mutations
                              /\ partition_data' = [partition_data EXCEPT ![b] = after_trunc] 
                              /\ broker_fetchers' = [broker_fetchers EXCEPT ![b][m.source] =  
                                                            [partition |-> [fetch_offset       |-> after_trunc.leo,
                                                                            last_fetched_epoch |-> last_fetched_epoch,
                                                                            delayed            |-> FALSE],
                                                             pending_response |-> FALSE]]
                              /\ UNCHANGED << partition_status >>
                   \* --- CASE OK -----------------------------------------------------------
                   [] OTHER ->
                          LET new_leo == Len(LogOf(b)) + Len(m.partition.records) + 1
                              last_fetched_epoch == IF m.partition.records # <<>>
                                                    THEN Last(m.partition.records).epoch
                                                    ELSE Fetcher(b, m.source).partition.last_fetched_epoch
                          IN
                              /\ LeoOf(b) = m.partition.fetch_offset \* double check the fetch offset matches the LEO
                              \* state mutations
                              /\ partition_data' = [partition_data EXCEPT 
                                                        ![b].log = LogOf(b) \o m.partition.records, \* append the new data
                                                        ![b].leo = new_leo,
                                                        \* just overwrite HWM as long as it falls within bounds of the log
                                                        ![b].hwm = IF m.partition.hwm <= new_leo
                                                                   THEN m.partition.hwm ELSE HwmOf(b)] 
                              /\ broker_fetchers' = [broker_fetchers EXCEPT ![b][m.source] =  
                                                            [partition |-> [fetch_offset       |-> new_leo,
                                                                            last_fetched_epoch |-> last_fetched_epoch,
                                                                            delayed            |-> FALSE],
                                                             pending_response |-> FALSE]]
                              /\ UNCHANGED << partition_status >>
                  \* CASE END -----------------------------------------
              /\ Discard(m)
              /\ UNCHANGED << con_vars, broker_state, broker_metadata_log, partition_metadata, 
                              partition_replica_state, partition_pending_ap, inv_vars, aux_vars >> 

(*--------------------------------------------------------------
  ACTION: WriteRecordToLeader

  A leader receives a produce request if the maximal ISR 
  size >= minISR, it writes the value to its local partition log.

  NO PROPOSAL CHANGES
---------------------------------------------------------------------*)  

WriteRecordToLeader ==
    \E b \in Brokers, v \in Values :
        \* enabling conditions
        /\ v \notin inv_sent \* this value has not yet been written
        /\ broker_state[b].status = RUNNING
        /\ partition_status[b] = Leader
        /\ Cardinality(PartitionMetadata(b).maximal_isr) >= MinISR
        \* state mutations
        /\ LET new_leo    == LeoOf(b) + 1
               new_record == [epoch  |-> PartitionMetadata(b).leader_epoch,
                              offset |-> LeoOf(b),
                              value  |-> v]
               new_log    == Append(LogOf(b), new_record)
           IN
              /\ partition_data' = [partition_data EXCEPT ![b] =
                                         [partition_data[b] EXCEPT !.leo = new_leo,
                                                                   !.log = new_log]]
              /\ partition_replica_state' = [partition_replica_state EXCEPT ![b][b].leo = new_leo]
              /\ inv_sent' = inv_sent \union {v}
              /\ UNCHANGED << con_vars, broker_vars, partition_metadata, partition_status, 
                              partition_pending_ap, messages, aux_vars, inv_true_hwm, 
                              inv_consumed, inv_pos_acked, inv_neg_acked >>

(*-----------------------------------------------------------------------
  ACTION: UncleanShutdown

  A broker shutsdown uncleanly. In this spec, the entire partition log is 
  truncated. Also, in this action, the controller detects the broker 
  is unavailable and fences the broker.
  
---------------------------------------------------------------------*)  

DropFetchSessions(b) ==
    \* Fetch requests are synchronous, one at a time and also protected 
    \* by fetch sessions not modeled in this spec (to reduce additional
    \* complexity) so we achieve the same properties by simply dropping 
    \* all inflight fetch requests and responses where this broker is 
    \* involved (to avoid these messages from being processed in the future).
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

FailPendingWritesIfLeader(b) ==
    IF /\ partition_status[b] = Leader 
       /\ HwmOf(b) < LeoOf(b)
    THEN FailPendingWrites(b)
    ELSE UNCHANGED << inv_sent, inv_pos_acked, inv_neg_acked >>

UncleanShutdown ==
    \* enabling conditions
    /\ aux_ctrs.unclean_shutdown_ctr < UncleanShutdownLimit
    /\ \E b \in Brokers :
        /\ broker_state[b].status \notin { OFFLINE_CLEAN, OFFLINE_DIRTY }
        \* state mutations
        /\ broker_state' = [broker_state EXCEPT ![b] = 
                                [status            |-> OFFLINE_DIRTY,
                                 broker_epoch      |-> 0,
                                 incarnation_id    |-> 0,
                                 registered        |-> FALSE]]
        /\ DropFetchSessions(b)
        /\ partition_status' = [partition_status EXCEPT ![b] = Nil]
        /\ partition_data' = [partition_data EXCEPT ![b] = 
                                        [log |-> <<>>, hwm |-> 1, leo |-> 1,
                                         epoch_start_offset |-> 0]]
        /\ partition_replica_state' = [partition_replica_state EXCEPT ![b] = 
                                        [b1 \in Brokers |-> BlankReplicaState]]
        /\ ResetPendingAlterPartition(b)
        /\ aux_ctrs' = [aux_ctrs EXCEPT !.unclean_shutdown_ctr = @ + 1]
        /\ FailPendingWritesIfLeader(b)
        \* make the controller detect it
        /\ HandleBrokerFenced(b)
        /\ con_broker_reg' = [con_broker_reg EXCEPT ![b].status = FENCED]
        /\ UNCHANGED << partition_metadata, broker_metadata_log, inv_true_hwm,
                        inv_consumed, aux_broker_epoch >>
                        
(*-----------------------------------------------------------------------
  ACTION: CleanShutdown

  A broker shutsdown cleanly. Also, in this action, the controller detects the broker 
  is unavailable and fences the broker.
  
  In this simplified version, we do not include the controlled
  shutdown sequence.

  ++ PROPOSAL CHANGES ++++++++++++++++++++++++++++++++
  The broker writes its broker epoch to a file on shutdown.
  ++++++++++++++++++++++++++++++++++++++++++++++++++++
---------------------------------------------------------------------*)  

CleanShutdown ==
    \* enabling conditions
    /\ aux_ctrs.clean_shutdown_ctr < CleanShutdownLimit
    /\ \E b \in Brokers :
        /\ broker_state[b].status \notin { OFFLINE_CLEAN, OFFLINE_DIRTY }
        \* state mutations
        /\ broker_state' = [broker_state EXCEPT ![b] = 
                                [status            |-> OFFLINE_CLEAN,
                                 broker_epoch      |-> broker_state[b].broker_epoch,
                                 incarnation_id    |-> 0,
                                 registered        |-> FALSE]]
        /\ DropFetchSessions(b)
        /\ partition_status' = [partition_status EXCEPT ![b] = Nil]
        /\ partition_replica_state' = [partition_replica_state EXCEPT ![b] = 
                                        [b1 \in Brokers |-> BlankReplicaState]]
        /\ ResetPendingAlterPartition(b)
        /\ aux_ctrs' = [aux_ctrs EXCEPT !.clean_shutdown_ctr = @ + 1]
        /\ FailPendingWritesIfLeader(b)
        \* make the controller detect it
        /\ HandleBrokerFenced(b)
        /\ con_broker_reg' = [con_broker_reg EXCEPT ![b].status = FENCED]
        /\ UNCHANGED << partition_metadata, partition_data, broker_metadata_log, 
                        inv_true_hwm, inv_consumed, aux_broker_epoch >>

\* ==================================================================
\*              INIT and NEXT
\* ==================================================================

\* The cluster starts in an already established state.
\* When InitIsrSize < ReplicationFactor then a subset of broker start outside 
\* of the ISR with a stale partiion_epoch. This allows us to explore
\* more state space by initializing the cluster with a smaller ISR.

Init ==
    LET init_isr   == CHOOSE isr \in SUBSET Brokers :
                        /\ 1 \in isr \* we always start with broker 1 as the leader
                        /\ Cardinality(isr) = InitIsrSize
        init_elr   == IF InitIsrSize < MinISR
                      THEN CHOOSE s \in SUBSET Brokers :
                                /\ Cardinality(s) = MinISR - InitIsrSize
                                /\ s \intersect init_isr = {}
                      ELSE {}
        \* if the inital ISR is < RF then we make the partition_epoch = 2 
        \* to simulate a change having already occurred.
        part_epoch  == IF init_isr = Brokers THEN 1 ELSE 2
        metadata_log  == <<>>
        metadata_log1 == Append(metadata_log, 
                                  [type            |-> PartitionChangeRecord,
                                   leader          |-> 1,
                                   isr             |-> init_isr,
                                   elr             |-> init_elr,
                                   leader_epoch    |-> 1,
                                   partition_epoch |-> part_epoch])                                  
    IN 
        /\ con_unfenced = init_isr
        /\ con_broker_reg = [b \in Brokers |->
                \* use the broker_id integer as a value for multiple fields
                \* as it serves as a good value at this stage. 
                [status              |-> IF b \in init_isr
                                         THEN UNFENCED ELSE FENCED,
                 broker_epoch        |-> b, 
                 incarnation_id      |-> b]]
        /\ con_metadata_log = metadata_log1
        /\ con_partition_metadata = 
                [isr             |-> init_isr,
                 elr             |-> init_elr,
                 leader          |-> 1, \* broker 1
                 leader_epoch    |-> 1,
                 partition_epoch |-> part_epoch] 
        /\ broker_state = [b \in Brokers |-> 
                [status            |-> RUNNING,
                 broker_epoch      |-> b,
                 incarnation_id    |-> b,
                 registered        |-> TRUE]]
        /\ broker_fetchers = [b \in Brokers |->
                                    [b1 \in Brokers |->
                                        IF b # 1 /\ b1 = 1
                                        THEN [partition        |-> [fetch_offset       |-> 1,
                                                                    last_fetched_epoch |-> 0,
                                                                    delayed            |-> FALSE],
                                              pending_response |-> FALSE]
                                        ELSE BlankFetchState]]
        /\ broker_metadata_log = [b \in Brokers |-> IF b \in init_isr
                                                    THEN metadata_log1
                                                    ELSE metadata_log]
        /\ partition_status = [b \in Brokers |-> IF b = 1 THEN Leader ELSE Follower]
        /\ partition_metadata = [b \in Brokers |-> 
                                    [isr          |-> IF b \in init_isr 
                                                      THEN init_isr ELSE Brokers,
                                     maximal_isr  |-> IF b \in init_isr 
                                                      THEN init_isr ELSE Brokers,
                                     leader       |-> 1, \* broker 1
                                     leader_epoch |-> 1,
                                     \* if the "initial ISR = Brokers" then all brokers
                                     \* have the same partition_epoch, else, the brokers in the
                                     \* ISR have the up-to-date epoch and the rest have a stale one.
                                     partition_epoch |-> CASE init_isr = Brokers -> 1 
                                                           [] b \in init_isr -> 2
                                                           [] OTHER -> 1]]
        \* the partition log on each replica starts empty
        /\ partition_data = [b \in Brokers |->
                                    [log                |-> <<>>,
                                     hwm                |-> 1,
                                     leo                |-> 1,
                                     epoch_start_offset |-> 0]]
        /\ partition_replica_state = [b \in Brokers |->
                                        [b1 \in Brokers |-> BlankReplicaState]]
        /\ partition_pending_ap = [b \in Brokers |-> [epoch |-> 0, request |-> Nil]]
        /\ aux_broker_epoch = ReplicationFactor
        /\ aux_ctrs = [incarn_ctr           |-> ReplicationFactor + 1,
                       clean_shutdown_ctr   |-> 0,
                       unclean_shutdown_ctr |-> 0,
                       fence_broker_ctr     |-> 0,
                       alter_part_ctr       |-> 0]
        /\ inv_sent = {}
        /\ inv_pos_acked = {}
        /\ inv_neg_acked = {}
        /\ inv_true_hwm = 1
        /\ inv_consumed = <<>>
        /\ messages = <<>>

Next ==
    \* broker/replica actions
    \/ BrokerStart
    \/ ReceiveBrokerRegResponse
    \/ ReceiveMetadataUpdate
    \/ SendAlterPartitionRequest
    \/ ReceiveAlterPartitionResponse
    \/ SendFetchRequest
    \/ ReceiveFetchRequest
    \/ ReceiveFetchResponse
    \/ WriteRecordToLeader
    \/ UncleanShutdown 
    \/ CleanShutdown
    \* controller actions  
    \/ ReceiveBrokerRegRequest
    \/ ReceiveAlterPartitionRequest
    \/ FenceBroker
    \/ UnfenceBroker

\* We only need actions that help the cluster make progress and
\* recover from failures here.
Liveness ==
    WF_vars(\/ BrokerStart
            \/ ReceiveBrokerRegResponse
            \/ ReceiveMetadataUpdate
            \/ SendAlterPartitionRequest
            \/ ReceiveAlterPartitionResponse
            \/ SendFetchRequest
            \/ ReceiveFetchRequest
            \/ ReceiveFetchResponse
            \/ WriteRecordToLeader
            \/ ReceiveBrokerRegRequest
            \/ ReceiveAlterPartitionRequest
            \/ UnfenceBroker)    
    
Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Liveness
=============================================================================
