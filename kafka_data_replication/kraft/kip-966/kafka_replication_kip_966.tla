-------------------------- MODULE kafka_replication_kip_966 --------------------------

EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences, SequencesExt, TLC, 
        message_passing, 
        kip_966_types,
        kip_966_properties,
        kip_966_functions

(*
-------------------------------------------------------------------------------------
------- KIP-966 based Kafka data replication protocol with the KRaft Controller -----

KIP-966 Eligible Leader Replicas Proposal

Models a proposed change to the replication protocol to enhance the recovery 
mechanism to better handling of unclean shutdowns.

KIP has complete description: https://cwiki.apache.org/confluence/display/KAFKA/KIP-966%3A+Eligible+Leader+Replicas

See the accompanying English prose protocol description for a thorough walkthrough 
of how the replication protocol works. This specification uses ample comments to 
describe each action but it is best to start with the prose then understand specifics
in the TLA+.

If you are new to TLA+ it is best to start learning with a simple specification,
the Kafka replication protocol specification is large and complex.
  
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
   WHO: Broker

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
             \* PROPOSAL CHANGE - send the broker epoch on file (if it exists)
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
                                 \* PROPOSAL CHANGE - use the broker epoch on file
                                 broker_epoch      |-> broker_state[b].broker_epoch,
                                 incarnation_id    |-> aux_ctrs.incarn_ctr,
                                 registered        |-> FALSE]]
        /\ partition_status' = [partition_status EXCEPT ![b] = Nil]
        /\ SendBrokerRegistration(b)
        /\ UNCHANGED << con_vars, broker_fetchers, broker_metadata_log, 
                        partition_metadata, partition_data, partition_leso,
                        partition_replica_state, partition_pending_ap, 
                        inv_vars, aux_broker_epoch >>        

(* ---------------------------------------------------------------
   ACTION: ReceiveBrokerRegRequest
   WHO: Controller

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
   
   Whether clean or unclean, the broker is assigned a new broker epoch based
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
    IN /\ MaybeUpdatePartitionOnBrokerChange(new_isr, new_elr, new_unfenced)
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
                         incarnation_id  |-> m.incarnation_id,
                         metadata_offset |-> Len(con_metadata_log), \* spec only field (see ReceiveBrokerRegResponse)
                         dest            |-> b,
                         source          |-> Controller])
                /\ aux_broker_epoch' = aux_broker_epoch + 1 \* used instead of metadata write offset
                /\ UNCHANGED << broker_vars, part_vars, inv_vars, aux_ctrs >>

(*---------------------------------------------------------------
  ACTION: ReceiveBrokerRegResponse
  WHO: Broker

  A broker receives a RegisterBrokerResponse for its current
  incarnation id and updates its broker epoch and registered state. 

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
    initialize the partition replica.

    NO PROPOSAL CHANGE
----------------------------------------------------------------*)

__CatchUpBarOne(b, m) ==
    LET log == IF m.metadata_offset <= 1
               THEN <<>>
               ELSE SubSeq(con_metadata_log, 1, m.metadata_offset-1)
    IN /\ broker_metadata_log' = [broker_metadata_log EXCEPT ![b] = log]
       /\ partition_metadata' = [partition_metadata EXCEPT ![b] = BlankMetadata] 

ReceiveBrokerRegResponse ==
    \E m \in DOMAIN messages :
        \* enabling conditions
        /\ ReceivableMsg(m, RegisterBrokerResponse)
        /\ broker_state[m.dest].status = STARTING
        /\ broker_state[m.dest].registered = FALSE
        /\ broker_state[m.dest].incarnation_id = m.incarnation_id \* CHECK
        \* state mutations
        /\ broker_state' = [broker_state EXCEPT ![m.dest] = 
                                [status         |-> RUNNING,
                                 broker_epoch   |-> m.broker_epoch,
                                 incarnation_id |-> broker_state[m.dest].incarnation_id,
                                 registered     |-> TRUE]]
        /\ __CatchUpBarOne(m.dest, m)
        /\ Discard(m)
        /\ UNCHANGED << con_vars, broker_fetchers, partition_status, partition_data,  
                        partition_leso, partition_replica_state, partition_pending_ap, 
                        inv_vars, aux_vars >>

(*--------------------------------------------------------------------
  ACTION: UnfenceBroker
  WHO: Controller

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
  WHO: Controller

  The controller fences an unfenced broker. In the implementation
  this would happen due to a lack of heartbeats. This spec simply
  allows this to occur at any time to an unfenced broker.

  ++ PROPOSAL CHANGE +++++++++++++++++++++++++++++
  In this proposal, the ISR can be empty. A fenced broker is 
  removed from any leadership and ISR (even if it leaves the 
  ISR empty).
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
  WHO: Broker/Partition replica

  NOTE! This action contains a lot of logic.

  In this simplified spec, only PartitionChange records are added to the 
  metadata log. This specification deviates from the implementation in 
  that metadata records are full snapshots of partition metadata rather 
  than deltas which require a merge function to turn current metadata
  state -> next metadata state. This was for simplification and may be
  updated at some point in the future.
  
  Brokers may receive an arbitrary number of records at a time, and because
  this spec models updates as full snapshots rather than deltas, essentially
  we just overwrite the partition metadata with the values of the last 
  record of the batch (rather than applying a merge function on each record
  in the batch, serially). This simplifies the TLA+ code and makes it faster.
  
  Not all metadata records are relevant to a partition, for example, a follower
  is unaffected by an ISR change. So this action is only enabled when there
  is an unreplicated metadata record which results in some kind of local
  partition action.
    
  When a broker receives an applicable PartionChange metadata record it can
  take various actions. There are 6 sub-actions:
   1. RemainLeader
        - it may need to advance the HWM as the ISR changed.
        - Negatively acknowledge pending requests if the ISR has 
          shrunk below minISR.
   2. BecomeLeaderInNewEpoch
        - Records the start offset for this leader epoch (the LEO on 
          becoming leader).
        - If it is a follower->leader change then remove the partition
          from any fetcher it is added to.
        - If the replica set has changed it may need to clear any follower
          state of removed replicas.
   3. RemainFollower
        - No actions
   4. BecomeFollowerInNewEpoch
        - Adds the partition to the right fetcher and removes the partition
          from any other fetcher if it exists.
        - The follower does not perform truncation, this spec implements
          the diverging epoch on fetch.
        - Negatively acknowledge pending requests if the replica lost leadership.
   5. WaitForLeaderChange
        - Negatively acknowledge pending requests if the replica lost leadership.
   6. DeletePartition
        - Negatively acknowledge pending requests if the replica lost leadership.
        - Remove the partition from the fetcher

   NO PROPOSAL CHANGE
 -----------------------------------------------------------------------*)           

\* Add the partition to the fetcher in the case that:
\*    - this is a new leader epoch.
\*    - the partition has not already been added.
\* Adding the partition to one fetcher removes it from another,
\* if it existed on another. The Last Fetch Epoch is set to the
\* epoch of the last record in the log.
AddPartitionToFetcher(b, leader, leader_epoch) ==
    IF 
       \/ leader_epoch > partition_metadata[b].leader_epoch \* CHECK
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

\* Ensure all state related to former leadership is clear    
EnsureLeadershipRenounced(b, new_part_md) ==
    /\ MaybeFailPendingWrites(b, new_part_md)
    /\ ResetAllFollowerState(b)
    /\ ResetPendingAlterPartition(b)    

\* --- Sub-Action 1: RemainLeader ---
\* The replica remains leader, all it must do is conditionally advance the HWM
\* and potentially send producer acknowledgements. Acknowledgements will be
\* positive if ISR >= MinISR and negative if ISR < MinISR.
RemainLeader(b, new_part_md) ==
    /\ MaybeUpdateHwmAndAckOnPartitionChange(b, new_part_md, FALSE)
    /\ IF new_part_md.partition_epoch >= partition_pending_ap[b].epoch
       THEN ResetPendingAlterPartition(b)
       ELSE UNCHANGED partition_pending_ap
    /\ UNCHANGED << partition_status, partition_replica_state, 
                    partition_leso, broker_fetchers>>

\* --- Sub-Action 2: BecomeLeaderInNewEpoch ---
\* The replica has become a leader in a new leader epoch. This includes
\* a leader being reelected in a new leader epoch. So it must set its
\* Leader Epoch Start Offset, conditionally reset peer replica state and 
\* remove the partition from any fetcher if it is added.
\* It may also now be able to advance the high watermark if the ISR consists
\* only of itself. It doesn't yet know the LEO of the followers so HWM would
\* only advance if the ISR were only this leader.
BecomeLeaderInNewEpoch(b, new_part_md, is_new_leader) ==
    /\ partition_status' = [partition_status EXCEPT ![b] = Leader]
    /\ MaybeUpdateHwmAndAckOnPartitionChange(b, new_part_md, TRUE)
    /\ partition_leso' = [partition_leso EXCEPT ![b] = LeoOf(b)]
    /\ IF is_new_leader
       THEN \* is a new leader and we know nothing of the followers
            ResetAllFollowerState(b)
       ELSE \* we reset the state of any out-of-sync followers as out-of-sync 
            \* followers have not proved themselves yet. Any prior knowledge
            \* of their LEO is untrustworthy, we must receive a new fetch request
            \* in this new leader epoch before they could be classified as in-sync.
            ResetFollowerStateOfAllButISR(b, new_part_md) \* CHECK
    /\ ResetPendingAlterPartition(b)
    /\ RemovePartitionFromFetchers(b)

\* --- Sub-Action 3: RemainFollower ---
\* The replica is still a follower in the same leader epoch. So do nothing.     
RemainFollower ==
    UNCHANGED << partition_status, partition_data, partition_replica_state, 
                 partition_leso, partition_pending_ap, broker_fetchers, inv_vars >>

\* --- Sub-Action 4: BecomeFollowerInNewEpoch ---
\* The replica has become a follower in a new leader epoch and adds the 
\* partition to the right fetcher, setting its fetch offset to its 
\* current LEO. If log truncation is required, it will occur on its first
\* fetch response.        
BecomeFollowerInNewEpoch(b, new_part_md) ==
    /\ partition_status' = [partition_status EXCEPT ![b] = Follower]
    /\ AddPartitionToFetcher(b, new_part_md.leader, new_part_md.leader_epoch)
    /\ partition_leso' = [partition_leso EXCEPT ![b] = Nil]
    \* in case it was formerly a leader
    /\ EnsureLeadershipRenounced(b, new_part_md)
    /\ UNCHANGED << partition_data, inv_true_hwm, inv_consumed >>

\* --- Sub-Action 5: WaitForLeaderChange ---    
\* The replica learns there is no leader, so waits in limbo until
\* it gets new information.    
WaitForLeaderChange(b, new_part_md) ==
    /\ partition_status' = [partition_status EXCEPT ![b] = Nil]
    /\ RemovePartitionFromFetchers(b)
    /\ partition_leso' = [partition_leso EXCEPT ![b] = Nil]
    \* in case it was formerly a leader
    /\ EnsureLeadershipRenounced(b, new_part_md)
    /\ UNCHANGED << partition_data, inv_true_hwm, inv_consumed >>
    
\* --- Sub-Action 6: DeletePartition ---    
\* The replica learns it has been removed from the replica set and
\* must be deleted locally on this broker.    
DeletePartition(b, new_part_md) ==
    /\ partition_status' = [partition_status EXCEPT ![b] = Nil]
    /\ RemovePartitionFromFetchers(b)
    /\ partition_leso' = [partition_leso EXCEPT ![b] = Nil]
    /\ partition_data' = [partition_data EXCEPT ![b] = 
                                [log                |-> <<>>,
                                 hwm                |-> 1,
                                 leo                |-> 1]]
    \* in case it was formerly a leader
    /\ EnsureLeadershipRenounced(b, new_part_md)
    /\ UNCHANGED << inv_true_hwm, inv_consumed >>    

MetadataNoOp ==
    UNCHANGED << part_vars, broker_fetchers, inv_vars >>

ReceiveMetadataUpdate ==
    \E b \in Brokers :
        \* enabling conditions
        /\ broker_state[b].status \notin {OFFLINE_CLEAN, OFFLINE_DIRTY}
        /\ broker_state[b].registered = TRUE
        /\ \E md_offset \in UnreplicatedOffsets(b) :
            /\ PartitionNeedsAction(b, md_offset)
            /\ LET md_record      == con_metadata_log[md_offset]
                   append_records == SubSeq(con_metadata_log, 
                                            Len(broker_metadata_log[b])+1,
                                            md_offset) 
                   curr_part_md   == partition_metadata[b]
                   new_part_md    == [replicas        |-> md_record.replicas,
                                      isr             |-> md_record.isr,
                                      maximal_isr     |-> md_record.isr,
                                      leader          |-> md_record.leader,
                                      leader_epoch    |-> md_record.leader_epoch,
                                      partition_epoch |-> md_record.partition_epoch]
                   is_new_leader  == /\ partition_status[b] # Leader
                                     /\ md_record.leader = b
               IN \* state mutations
                  /\ broker_metadata_log' = [broker_metadata_log EXCEPT ![b] = @ \o append_records]
                     \* The partition epoch may not always be higher as an AlterPartition response may have
                     \* already have been received tht matches this epoch.
                  /\ IF new_part_md.partition_epoch > curr_part_md.partition_epoch
                     THEN
                          /\ partition_metadata' = [partition_metadata EXCEPT ![b] = IF b \in new_part_md.replicas
                                                                                     THEN new_part_md
                                                                                     ELSE BlankMetadata]
                          /\ CASE 
                               \* CASE --- Delete partition locally ----------------------
                                  /\ b \in partition_metadata[b].replicas
                                  /\ b \notin new_part_md.replicas ->
                                      DeletePartition(b, new_part_md)
                               \* CASE --- Remains leader --------------------------------
                               [] /\ partition_metadata[b].leader = b
                                  /\ md_record.leader = b -> 
                                      IF partition_metadata[b].leader_epoch = new_part_md.leader_epoch
                                      THEN \* Remains leader in the same leader epoch
                                           RemainLeader(b, new_part_md)
                                      ELSE \* Leader reelected in a new leader epoch
                                           BecomeLeaderInNewEpoch(b, new_part_md, is_new_leader)
                               \* CASE --- Follower elected as leader----------------------
                               [] /\ partition_metadata[b].leader # b
                                  /\ md_record.leader = b ->
                                      BecomeLeaderInNewEpoch(b, new_part_md, is_new_leader)
                               \* CASE --- Chosen as a follower ---------------------------
                               [] /\ b \in new_part_md.replicas
                                  /\ md_record.leader # NoLeader ->
                                      IF /\ new_part_md.leader_epoch = curr_part_md.leader_epoch
                                         /\ curr_part_md.leader # b
                                         /\ new_part_md.leader # b
                                      THEN RemainFollower
                                      ELSE BecomeFollowerInNewEpoch(b, new_part_md)
                               \* CASE --- No leader chosen -------------------------------
                               [] OTHER ->
                                      /\ b \in new_part_md.replicas
                                      /\ WaitForLeaderChange(b, new_part_md)
                               \* END CASE
                     ELSE MetadataNoOp
                  /\ UNCHANGED << con_vars, broker_state, messages, aux_vars, inv_sent >>

(*--------------------------------------------------------------------------
  ACTION: SendAlterPartitionRequest
  WHO: Partition leader

  The leader tries to modify the ISR. 

  The leader first identifies all replicas that are caught up and adds
  them to the proposed ISR. The definition of "caught up" is that:
    a. If the replica is already in the ISR then it hasn't timed out.
    b. If the replica is not currently in the ISR then:
        i.   The replica has not timed out.
        ii.  The replica fetch offset is >= HWM.
        iii. The replica fetch offset is >= Leader Epoch Start Offset.
        iv.  The leader has received a fetch request in the current leader epoch.
  
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
  
  The leader eagerly applies the maximal ISR. The maximal ISR is the
  union of the proposed ISR with the current ISR in order to maintain
  the 'ISR Superset' property that the ISR used to advance the high
  watermark must be a superset of the controller ISR. This in turn
  supports 'ISR Completeness' which is required to avoid data loss 
  where the controller selects a replica without the complete committed
  log.
  
  This AlterPartition request may complete an ongoing reassignment
  that is waiting for all 'adding' replicas to be added to the ISR.
  See the protocol description to understand the reassignment process.

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
FollowerIsCaughtUp(b, follower, follower_leo, curr_isr, timed_out_isr) ==
    \/ /\ follower \in curr_isr
       /\ follower \notin timed_out_isr
    \/ /\ follower \notin curr_isr
       \* The leader must have received a fetch request from the follower
       /\ follower_leo # Nil                \* CHECK
       \* The follower must have reached the high watermark
       /\ follower_leo >= HwmOf(b)          \* CHECK
       \* The follower must have reached the Leader Epoch Start Offset
       /\ follower_leo >= partition_leso[b] \* CHECK

ProposeNewISR(b, curr_isr, timed_out_isr) ==
    { b1 \in partition_metadata[b].replicas : 
        \/ b1 = b 
        \/ FollowerIsCaughtUp(b, b1,
             partition_replica_state[b][b1].leo,
             curr_isr,
             timed_out_isr) }

MaybeIncrementShrinkCtr(curr_isr, proposed_isr) ==
    IF \E b1 \in curr_isr : b1 \notin proposed_isr
    THEN aux_ctrs' = [aux_ctrs EXCEPT !.leader_shrink_isr_ctr = @ + 1]
    ELSE UNCHANGED aux_ctrs

\* if we've sent this exact request before then it got rejected previously
\* so don't try to send it again else we'll enter an infinite cycle
\* that prevents liveness checking
__AvoidCycle(ap_request) ==
    ~\E m \in DOMAIN messages : ap_request = m 

DoSendAlterPartitionRequest(b, timed_out_isr) ==
    /\ b \notin timed_out_isr
    /\ LET curr_isr     == partition_metadata[b].isr
           proposed_isr == ProposeNewISR(b, curr_isr, timed_out_isr)
           ap_request   == [type            |-> AlterPartitionRequest,
                            isr             |-> proposed_isr,
                            isr_and_epochs  |-> IsrAndEpochs(b, proposed_isr, curr_isr),
                            leader          |-> b,
                            leader_epoch    |-> partition_metadata[b].leader_epoch,
                            partition_epoch |-> partition_metadata[b].partition_epoch,
                            broker_epoch    |-> broker_state[b].broker_epoch,
                            source          |-> b,
                            dest            |-> Controller]
       IN 
          /\ proposed_isr # curr_isr
          /\ __AvoidCycle(ap_request)
          \* state mutations
          /\ Send(ap_request)
          /\ partition_metadata' = [partition_metadata EXCEPT ![b].maximal_isr = 
                                       proposed_isr \union curr_isr]
          /\ partition_pending_ap' = [partition_pending_ap EXCEPT ![b] = 
                                            [epoch   |-> partition_metadata[b].partition_epoch + 1,
                                             request |-> ap_request]]
          /\ MaybeIncrementShrinkCtr(curr_isr, proposed_isr)
          /\ UNCHANGED << con_vars, broker_vars, partition_data, partition_leso, 
                          partition_replica_state, partition_status, inv_vars,
                          aux_broker_epoch >>

SendAlterPartitionRequest ==
    \* enabling conditions
    \E b \in Brokers :
        /\ broker_state[b].status = RUNNING
        /\ ~PendingAlterPartitionResponse(b)
        /\ partition_status[b] = Leader
        /\ IF aux_ctrs.leader_shrink_isr_ctr < LeaderShrinkIsrLimit
           THEN \E timed_out_isr \in SUBSET partition_metadata[b].isr :
                    /\ Cardinality(timed_out_isr) > 0
                    /\ b \notin timed_out_isr
                    /\ DoSendAlterPartitionRequest(b, timed_out_isr)
           ELSE DoSendAlterPartitionRequest(b, {})

(*--------------------------------------------------------------------------
  ACTION: ReceiveAlterPartitionRequest
  WHO: Controller

  The controller receives an AlterPartition request.

  It accepts the request if:
  - the partition epoch matches.
  - the request is from the current partition leader.
  - the broker epoch of the leader matches.
  - the broker epoch of all brokers in the proposed ISR matches
    or the supplied broker epoch is 0 (-1 in the implementation).
  - All brokers in the proposed ISR are active and unfenced.

  The leader epoch is not incremented as this spec only models
  leader epoch changes when a leader change has occurred,
  else it remains the same. Note, this is looser than the current
  implemention in 3.5 - this change will be released in a future
  Kafka version.
  
  This AlterPartition request may complete an ongoing reassignment
  if:
    a. it modifies the ISR such that all 'adding' replicas are now
       ISR members. 
    b. the final replica set that would be committed is not empty.
    c. the final ISR that would be committed is not empty.
         
  If it does complete a reassignment then it updates the replicas
  to the target set and removing an ISR replicas if they are members
  of the 'removing' set.
  
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
    /\ \/ broker_epoch = 0                                  \* CHECK
       \/ con_broker_reg[b].broker_epoch = broker_epoch
    
EligibleIsr(m) ==
    \A b \in DOMAIN m.isr_and_epochs :
        IsEligibleBroker(b, m.isr_and_epochs[b])    

ValidateRequest(b, m) ==
    IF /\ b = con_partition_metadata.leader
       /\ m.broker_epoch = con_broker_reg[b].broker_epoch               
       /\ m.partition_epoch = con_partition_metadata.partition_epoch    \* CHECK
    THEN IF EligibleIsr(m)
         THEN Nil
         ELSE IneligibleReplica
    ELSE FencedLeaderEpoch

ReceiveAlterPartitionRequest ==
    \E m \in DOMAIN messages : 
        \* enabling conditions
        /\ ReceivableMsg(m, AlterPartitionRequest)
        /\ LET b     == m.source
               md    == con_partition_metadata
               error == ValidateRequest(b, m)
               final_replicas == md.replicas \ md.removing
               final_isr      == m.isr \ md.removing
               complete       == /\ ReassignmentInProgress
                                 /\ \A b1 \in md.adding : b1 \in final_isr
                                 /\ Cardinality(final_isr) >= MinISR
               new_md         == IF complete
                                 THEN [replicas        |-> final_replicas,
                                       isr             |-> final_isr,
                                       elr             |-> UpdateElrOnIsrOrReplicaChange(final_isr, final_replicas),
                                       leader_epoch    |-> md.leader_epoch + 1,
                                       partition_epoch |-> md.partition_epoch + 1,
                                       adding          |-> {},
                                       removing        |-> {}]
                                 ELSE [replicas        |-> md.replicas,
                                       isr             |-> m.isr, \* just update to the proposed ISR
                                       elr             |-> UpdateElrOnIsrOrReplicaChange(m.isr, md.replicas),
                                       leader_epoch    |-> md.leader_epoch,
                                       partition_epoch |-> md.partition_epoch + 1,
                                       adding          |-> md.adding,
                                       removing        |-> md.removing]
           IN
              \* state mutations
              /\ IF error = Nil
                 THEN \* the leader may actually have been removed as this partition
                      \* change could complete a reassignment where the leader is removed.
                      \E new_leader \in new_md.isr :
                          /\ IF md.leader \in new_md.isr
                             THEN new_leader = con_partition_metadata.leader \* keep the same leader if possible
                             ELSE TRUE \* non-deterministically choose any replica in the new ISR
                          /\ ApplyPartitionChange(new_md.replicas, new_leader, new_md.isr, new_md.elr,
                                                  new_md.leader_epoch, new_md.partition_epoch, 
                                                  new_md.adding, new_md.removing)
                          /\ Reply(m,
                                  [type            |-> AlterPartitionResponse,
                                   error           |-> Nil,
                                   replicas        |-> new_md.replicas,
                                   isr             |-> new_md.isr,
                                   leader          |-> new_leader,
                                   leader_epoch    |-> new_md.leader_epoch,
                                   partition_epoch |-> new_md.partition_epoch,
                                   request         |-> m, \* not actually part of the message, 
                                                          \* a trick used for correlation in this spec.
                                   dest            |-> b,
                                   source          |-> Controller])
                   ELSE \* Reject the request
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
  WHO: Broker/Partition leader

  A broker receives an AlterPartition response. 

  The response is ignored in the following cases:
    - The response does not match the requested change.
    - Has a Nil error code but the partition epoch is not higher.
      This happens when a metadata update for this change was
      processed before receiving the AlterPartition response.
    - Has a Nil error code but the leader epoch does not match.
      This happens when the AlterPartition request completed a
      reassignment which removed this replica from the replica set.
      If this is the case, don't process it here, let the metadata update
      handling handle this case.
   
  If the response matches the expected requested change, and indicates 
  success then updates its local partition state. If the response 
  indicates an IneligibleReplica or FencedEpoch, it rolls back its 
  eagerly applied partition state change, reverting to the last 
  partition state.

  NO PROPOSAL CHANGE
--------------------------------------------------------------------------------*)

CommitPartitionChange(b, part_state) ==
    /\ partition_metadata' = [partition_metadata EXCEPT ![b] = part_state]
    /\ MaybeUpdateHwmAndAckOnPartitionChange(b, part_state, FALSE)

CompletePartitionChange(b, m) ==
    CommitPartitionChange(b, [replicas        |-> m.replicas,
                              isr             |-> m.isr,
                              maximal_isr     |-> m.isr,
                              leader          |-> m.leader,
                              leader_epoch    |-> m.leader_epoch,
                              partition_epoch |-> m.partition_epoch])

RollbackPartitionChange(b) ==
    LET last_part_state == [partition_metadata[b] EXCEPT !.maximal_isr =   
                                    partition_metadata[b].isr]                      
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
              /\ partition_pending_ap[b].request = m.request \* correlates to our request
              /\ IF m.error = Nil
                 THEN \* Not a stale partition epoch
                      /\ m.partition_epoch > partition_metadata[b].partition_epoch
                      \* The request could have completed a reassignment, bumping the leader
                      \* epoch, in that case ignore this response and wait for the metadata update instead.
                      /\ m.leader_epoch = partition_metadata[b].leader_epoch
                 ELSE TRUE
              \* state mutations
              /\ IF m.error = Nil
                 THEN CompletePartitionChange(b, m)
                 ELSE RollbackPartitionChange(b)
              /\ ResetPendingAlterPartition(b)
              /\ Discard(m)
        /\ UNCHANGED << con_vars, broker_vars, partition_status, partition_leso,
                        partition_replica_state, aux_vars >>


(*--------------------------------------------------------------------------
  ACTION: PerformPartitionReassignment
  WHO: Controller

  The controller receives an AlterPartitionReassignments request from
  an admin/operator.
  
  A partition reassignment is where replicas can be added to and/or
  removed from the partition. Known generally as reconfiguration
  in other protocols.
  
  See the protocol description to understand reassignment.
  
  This currently limits reassignments to where the target replica set
  is not lower than the ReplicationFactor constant. Any other reassignment
  is valid.

  ++ PROPOSAL CHANGE +++++++++++++++++++++++++++++++++
  Update the ELR using the same rules as ReceiveAlterPartitionRequest.
  ++++++++++++++++++++++++++++++++++++++++++++++++++++   
---------------------------------------------------------------------------*)

ValidReassignment(adding, removing) ==
    \* There must be some kind of change
    /\ \/ Cardinality(adding) >= 1
       \/ Cardinality(removing) >= 1
    \* The target replica set should not go lower than the MinISR 
    /\ (Cardinality(con_partition_metadata.replicas) + Cardinality(adding)) 
            - Cardinality(removing) >= MinISR
    \* None of the adding set is currently a replica 
    /\ \A r \in adding : r \notin con_partition_metadata.replicas
    \* Every removing member is a current replica
    /\ \A r \in removing : r \in con_partition_metadata.replicas

PerformPartitionReassignment ==
    \* enabling conditions
    /\ aux_ctrs.reassignment_ctr < ReassignmentLimit
    /\ ~ReassignmentInProgress
    /\ \E adding, removing \in SUBSET Brokers :
        /\ ValidReassignment(adding, removing)
        /\ LET md             == con_partition_metadata
               grow_replicas  == md.replicas \union adding
               final_replicas == grow_replicas \ removing
               final_isr      == md.isr \ removing
               complete       == /\ \A b1 \in adding : b1 \in final_isr
                                 /\ Cardinality(final_isr) >= MinISR
                                 /\ Cardinality(final_replicas) > 0
               new_md         == IF complete
                                 THEN [replicas        |-> final_replicas,
                                       isr             |-> final_isr,
                                       elr             |-> UpdateElrOnIsrOrReplicaChange(final_isr, final_replicas),
                                       leader_epoch    |-> md.leader_epoch + 1,
                                       partition_epoch |-> md.partition_epoch + 1,
                                       adding          |-> {},
                                       removing        |-> {}]
                                 ELSE [replicas        |-> grow_replicas,
                                       isr             |-> md.isr,
                                       elr             |-> md.elr,
                                       leader_epoch    |-> md.leader_epoch,
                                       partition_epoch |-> md.partition_epoch + 1,
                                       adding          |-> adding,
                                       removing        |-> removing]
           IN 
              \* state mutations
              \* May be change the leader if we've shrunk the ISR (which can only
              \* happen here at this moment when there are no 'adding' replicas).
              /\ \E new_leader \in new_md.isr :
                    /\ IF md.leader \in new_md.isr
                       THEN new_leader = md.leader \* keep the same leader if possible
                       ELSE TRUE \* else non-deterministically select another replica from the new ISR
                    /\ ApplyPartitionChange(new_md.replicas, 
                                            new_leader,
                                            new_md.isr,
                                            new_md.elr,
                                            new_md.leader_epoch, 
                                            new_md.partition_epoch,
                                            new_md.adding,
                                            new_md.removing)
    /\ aux_ctrs' = [aux_ctrs EXCEPT !.reassignment_ctr = @ + 1]
    /\ UNCHANGED << con_broker_reg, con_unfenced, broker_vars, 
                    part_vars, aux_broker_epoch, inv_vars, messages >>

(*-----------------------------------------------------------------------
  ACTION: SendFetchRequest
  WHO: Broker/Partition follower

  Fetch requests are broker-to-broker with many partitions included
  in each fetch. However, in this spec it is ok to logically think
  about it as follower to leader.

  A follower sends a fetch request to the partition leader. The fetch
  request includes the fetch offset to indicate what records the 
  partition needs and the last_fetched_epoch that the leader will
  use to detect log divergence.
  
  Infinite fetch/response cycles are avoided here to ensure liveness
  checking works.

  NO PROPOSAL CHANGE
---------------------------------------------------------------------*)

SendFetchRequest ==
    \E from, to \in Brokers :
        \* enabling conditions
        /\ from # to
        /\ broker_state[from].status = RUNNING
        /\ Fetcher(from, to).partition # Nil           \* The fetcher has the partition added
        /\ Fetcher(from, to).pending_response = FALSE  \* The fetcher is not waiting for a response
        /\ partition_metadata[from].leader = to        \* This replica believes the destination 
                                                       \* broker hosts the leader replica
        /\ __SendFetchMakesProgress(from) \* prevents infinite cycles
        \* state mutations
        /\ Send([type               |-> FetchRequest,
                 broker_epoch       |-> broker_state[from].broker_epoch,
                 partition |-> \* only one partition modeled
                    [leader_epoch       |-> partition_metadata[from].leader_epoch,
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
  WHO: Partition leader
  
  A broker receives a fetch request and responds with a fetch response. This
  specification only models a single partition so a fetch only fetches for one partition.
  
  The fetch response is determined by the results of partition validation and 
  a diverging epoch check. One of the following will occur:
  - If the broker does not host the partition leader or the leader epoch of the
    partition does not match then reply with an error code.
  - If the fetch_offset and last_fetched_epoch are not consistent with the 
    partition log then reply with a diverging epoch.
  - If all matches up then the leader will return the next log record in its response. 
  
  The leader may advance the high watermark based on the fetch offset in the 
  fetch request. The reply includes the HWM.
  
  This spec only sends one record at a time.

  ++ PROPOSAL CHANGES +++++++++++++++++++++++++++++++++++
  The high watermark can only advance when ISR >= MinISR (note
  that this is the ISR size not the Maximal ISR size).
  There are two reasons for this:
     1. The ISR Superset property now applies to the ISR + ELR.
        However, the property no longer holds in all cases
        in this ELR proposal. The leader candidate pool is no
        longer just the ISR, but now the ISR + ELR. However,
        the leader has no knowledge of the ELR and the Maximal
        ISR is no longer guaranteed to encompass all leader candidates
        at all times.
        
        The good news is that the ISR Superset property is only
        at risk when the ISR < Min ISR. Therefore, we only advance
        the high watermark when the ISR Superset property is 
        guaranteed - which is when the ISR >= Min ISR.      

        As an example: ISR=[1], ELR=[2]. The leader sends an 
        AlterPartition request with ISR=[1,3] settings its own
        Maximal ISR to [1,3]. While the leader makes progress
        with Maximal ISR [1,3] the controller elects replica 2,
        violating the Leader Candidate Pool Completeness property.

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
        the high watermark, that change would not exist on the 
        new leader and we would break the monotonicity of
        the True HWM.
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
                      \/ partition_metadata[b].leader_epoch # m.partition.leader_epoch ->
                          \* In the case of being a stale leader, don't do any state changes,
                          \* wait for the metadata update to bring this stale leader up to date.        
                          /\ Reply(m,
                                    [type             |-> FetchResponse,
                                     partition |-> \* only one partition modeled
                                        [error           |-> CASE partition_metadata[b].leader_epoch < 
                                                                            m.partition.leader_epoch -> UnknownLeaderEpoch
                                                               [] partition_metadata[b].leader_epoch > 
                                                                            m.partition.leader_epoch -> FencedLeaderEpoch
                                                               [] OTHER                              -> NotLeaderOrFollower,
                                         leader_epoch    |-> partition_metadata[b].leader_epoch,
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
                                         leader_epoch    |-> partition_metadata[b].leader_epoch,
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
                              old_hwm       == HwmOf(b)
                              max_committed == CommitOffsetOnFetch(b, updated_rep_state)
                              new_hwm       == IF CanAdvanceHwm(b, partition_metadata[b].isr,
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
                                             leader_epoch    |-> partition_metadata[b].leader_epoch,
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
                              partition_metadata, partition_status, partition_leso,
                              partition_pending_ap, aux_vars >>        

(*-------------------------------------------------------------------
  ACTION: ReceiveFetchResponse
  WHO: Broker/Partition follower

  A broker receives a fetch response (for a single partition only 
  in this spec). 
  
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
             hwm                |-> HwmOf(b)] \* Truncation does not affect HWM
       ELSE [log |-> <<>>, hwm |-> HwmOf(b), leo |-> 1]

FetcherHasPartition(b, leader) ==
    broker_fetchers[b][leader].partition # Nil

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
                      \* The partition is not added to this fetcher 
                      \* or the partition is added but the fetch offset or leader epoch doesn't match.
                      \/ ~FetcherHasPartition(b, m.source)
                      \/ /\ FetcherHasPartition(b, m.source)
                         /\ \/ Fetcher(b, m.source).partition.fetch_offset # m.partition.fetch_offset \* CHECK
                            \/ partition_metadata[b].leader_epoch # m.partition.leader_epoch ->       \* CHECK
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
                              \* state mutations
                              /\ partition_data' = [partition_data EXCEPT ![b] =
                                                        [log |-> LogOf(b) \o m.partition.records, \* append the new data
                                                         leo |-> new_leo,
                                                         \* just overwrite HWM as long as it falls within bounds of the log
                                                         hwm |-> IF m.partition.hwm <= new_leo
                                                                 THEN m.partition.hwm ELSE HwmOf(b)]]
                              /\ broker_fetchers' = [broker_fetchers EXCEPT ![b][m.source] =  
                                                            [partition |-> [fetch_offset       |-> new_leo,
                                                                            last_fetched_epoch |-> last_fetched_epoch,
                                                                            delayed            |-> FALSE],
                                                             pending_response |-> FALSE]]
                              /\ UNCHANGED << partition_status >>
                  \* CASE END -----------------------------------------
              /\ Discard(m)
              /\ UNCHANGED << con_vars, broker_state, broker_metadata_log, partition_metadata, 
                              partition_replica_state, partition_leso, partition_pending_ap,
                              inv_vars, aux_vars >> 

(*--------------------------------------------------------------
  ACTION: WriteRecordToLeader
  WHO: Partition leader

  A leader receives a produce request if the maximal ISR 
  size >= minISR, it writes the value to its local partition log.
  
  If the MinISR = 1 and the ISR is only the leader then it is 
  possible for the high watermark to be incremented too.
  
  LEO and HWM are exclusive (hence the +1).

  ++ PROPOSAL CHANGES +++++++++++++++++++++++++++++++++++
  The high watermark can only advance when ISR >= MinISR (note
  that this is the ISR size not the Maximal ISR size).
  Therefore the HWM can only advance in this action if
  the MinISR=1.
  +++++++++++++++++++++++++++++++++++++++++++++++++++++++
---------------------------------------------------------------------*)  

WriteRecordToLeader ==
    \E b \in Brokers, v \in Values :
        \* enabling conditions
        /\ v \notin inv_sent \* this value has not yet been written
        /\ broker_state[b].status = RUNNING
        /\ partition_status[b] = Leader
        /\ Cardinality(partition_metadata[b].maximal_isr) >= MinISR
        \* state mutations
        /\ LET new_leo       == LeoOf(b) + 1
               new_record    == [epoch  |-> partition_metadata[b].leader_epoch,
                                 offset |-> LeoOf(b),
                                 value  |-> v]
               new_log       == Append(LogOf(b), new_record)
               old_hwm       == HwmOf(b)
               max_committed == CommitOffsetOnWrite(b, new_leo)
               new_hwm       == IF CanAdvanceHwm(b, partition_metadata[b].isr,
                                                 old_hwm, max_committed + 1)
                                THEN max_committed + 1
                                ELSE old_hwm
          IN
              /\ partition_data' = [partition_data EXCEPT ![b] =
                                            [leo |-> new_leo,
                                             hwm |-> IF new_hwm > old_hwm 
                                                     THEN new_hwm ELSE old_hwm,
                                             log |-> new_log]]
              /\ IF new_hwm > old_hwm
                 THEN UpdateHwmInvariantVars(b, old_hwm, new_hwm, TRUE)
                 ELSE UNCHANGED << inv_pos_acked, inv_neg_acked, inv_true_hwm, inv_consumed >>
              /\ inv_sent' = inv_sent \union {v}
              /\ UNCHANGED << con_vars, broker_vars, partition_metadata, partition_status, partition_leso,
                              partition_replica_state, partition_pending_ap, messages, aux_vars >>

(*-----------------------------------------------------------------------
  ACTION: DataLossShutdown
  WHO: Broker

  A broker shutsdown uncleanly. In this spec, the entire partition log is 
  truncated. Also, in this action, the controller detects the broker 
  is unavailable and fences the broker.
---------------------------------------------------------------------*)  

FailPendingWritesIfLeader(b) ==
    IF /\ partition_status[b] = Leader 
       /\ HwmOf(b) < LeoOf(b)
    THEN FailPendingWrites(b)
    ELSE UNCHANGED << inv_pos_acked, inv_neg_acked >>

DataLossShutdown ==
    \* enabling conditions
    /\ aux_ctrs.data_loss_shutdown_ctr < DataLossShutdownLimit
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
                                        [log |-> <<>>, hwm |-> 1, leo |-> 1]]
        /\ partition_leso' = [partition_leso EXCEPT ![b] = Nil]
        /\ partition_replica_state' = [partition_replica_state EXCEPT ![b] = 
                                        [b1 \in Brokers |-> 
                                            BlankReplicaState]]
        /\ ResetPendingAlterPartition(b)
        /\ aux_ctrs' = [aux_ctrs EXCEPT !.data_loss_shutdown_ctr = @ + 1]
        /\ FailPendingWritesIfLeader(b)
        \* make the controller detect it
        /\ HandleBrokerFenced(b)
        /\ con_broker_reg' = [con_broker_reg EXCEPT ![b].status = FENCED]
        /\ UNCHANGED << partition_metadata, broker_metadata_log, inv_true_hwm,
                        inv_consumed, inv_sent, aux_broker_epoch >>
                        
(*-----------------------------------------------------------------------
  ACTION: NoDataLossShutdown
  WHO: Broker

  A broker shutsdown cleanly, or it shutsdown uncleanly but this partition
  did not lose any data locally. Also, in this action, the controller 
  detects the broker is unavailable and fences the broker.
  
  In this simplified version, we do not include the controlled
  shutdown sequence.

  ++ PROPOSAL CHANGES +++++++++++++++++++++++++++++++++++
  The broker writes its broker epoch to file as part of its
  shutdown sequence.
  +++++++++++++++++++++++++++++++++++++++++++++++++++++++
---------------------------------------------------------------------*)  

NoDataLossShutdown ==
    \* enabling conditions
    /\ aux_ctrs.no_data_loss_shutdown_ctr < NoDataLossShutdownLimit
    /\ \E b \in Brokers, is_clean_shutdown \in BOOLEAN :
        /\ broker_state[b].status \notin { OFFLINE_CLEAN, OFFLINE_DIRTY }
        \* state mutations
        /\ broker_state' = [broker_state EXCEPT ![b] = 
                                [status            |-> OFFLINE_CLEAN,
                                 \* writes its broker epoch to file
                                 broker_epoch      |-> IF is_clean_shutdown
                                                       THEN broker_state[b].broker_epoch
                                                       ELSE 0,
                                 incarnation_id    |-> 0,
                                 registered        |-> FALSE]]
        /\ DropFetchSessions(b)
        /\ partition_status' = [partition_status EXCEPT ![b] = Nil]
        /\ partition_replica_state' = [partition_replica_state EXCEPT ![b] = 
                                        [b1 \in Brokers |-> 
                                            BlankReplicaState]]
        /\ ResetPendingAlterPartition(b)
        /\ aux_ctrs' = [aux_ctrs EXCEPT !.no_data_loss_shutdown_ctr = @ + 1]
        /\ FailPendingWritesIfLeader(b)
        \* make the controller detect it
        /\ HandleBrokerFenced(b)
        /\ con_broker_reg' = [con_broker_reg EXCEPT ![b].status = FENCED]
        /\ UNCHANGED << partition_metadata, partition_data, partition_leso,
                        broker_metadata_log, inv_sent, inv_true_hwm, inv_consumed, 
                        aux_broker_epoch >>

\* ==================================================================
\*              INIT and NEXT
\* ==================================================================

\* The cluster starts in an already established state.
\* When InitIsrSize < ReplicationFactor then a subset of the replicas
\* start outside of the ISR with a stale partition epoch. This allows
\* us to explore more state space.
\* REMEMBER: offsets are 1-based because TLA+ is 1-based!

Init ==
    LET \* choose a subset of all the brokers of size RF for the initial replica set
        init_replicas == CHOOSE replicas \in SUBSET Brokers :
                            /\ 1 \in replicas
                            /\ Cardinality(replicas) = InitReplicationFactor
        \* choose a subset of the initial replica set of size InitIsrSize
        init_isr   == CHOOSE isr \in SUBSET init_replicas :
                        /\ 1 \in isr \* we always start with broker 1 as the leader
                        /\ Cardinality(isr) = InitIsrSize
        \* if the inital ISR is < RF then we make the partition_epoch = 2 
        \* to simulate a change having already occurred.
        part_epoch  == IF InitIsrSize = InitReplicationFactor THEN 1 ELSE 2
        metadata_log == <<[type            |-> PartitionChangeRecord,
                           replicas        |-> init_replicas,
                           isr             |-> init_isr,
                           elr             |-> {},
                           last_known_elr  |-> {},
                           leader          |-> 1,
                           leader_epoch    |-> 1,
                           partition_epoch |-> part_epoch]>>
        init_unfenced == Brokers \ (init_replicas \ init_isr) \* everyone except the out-of-sync followers
    IN 
        /\ con_unfenced = init_unfenced
        /\ con_broker_reg = [b \in Brokers |->
                \* use the broker_id integer as a value for multiple fields
                \* as it serves as a good value at this stage. 
                [status              |-> IF b \in init_unfenced
                                         THEN UNFENCED ELSE FENCED,
                 broker_epoch        |-> b, 
                 incarnation_id      |-> b]]
        /\ con_metadata_log = metadata_log
        /\ con_partition_metadata = 
                [replicas        |-> init_replicas,
                 isr             |-> init_isr,
                 elr             |-> {},
                 last_known_elr  |-> {},
                 leader          |-> 1, \* broker 1
                 leader_epoch    |-> 1,
                 partition_epoch |-> part_epoch,
                 adding          |-> {},
                 removing        |-> {}] 
        /\ broker_state = [b \in Brokers |-> 
                [status            |-> RUNNING,
                 broker_epoch      |-> b,
                 incarnation_id    |-> b,
                 registered        |-> TRUE]]
        /\ broker_fetchers = [b \in Brokers |->
                                    [b1 \in Brokers |->
                                        IF b # 1 /\ b1 = 1 \* if is a follower
                                        THEN [partition        |-> [fetch_offset       |-> 1,
                                                                    last_fetched_epoch |-> 0,
                                                                    delayed            |-> FALSE],
                                              pending_response |-> FALSE]
                                        ELSE BlankFetchState]]
        /\ broker_metadata_log = [b \in Brokers |-> IF b \in init_unfenced
                                                    THEN metadata_log \* is an up-to-date replica
                                                    ELSE <<>>] \* is a stale replica
        /\ partition_status = [b \in Brokers |-> CASE b = 1 -> Leader
                                                   [] b \in init_replicas -> Follower
                                                   [] OTHER -> Nil]
        /\ partition_metadata = [b \in Brokers |->
                                    CASE 
                                      \* CASE --- Broker not a partition host --------
                                      b \notin init_replicas ->
                                              BlankMetadata
                                      \* CASE --- Replica is in the initial ISR ------
                                      [] b \in init_isr ->
                                             [replicas        |-> init_replicas,
                                              isr             |-> init_isr,
                                              maximal_isr     |-> init_isr,
                                              leader          |-> 1, \* broker 1
                                              leader_epoch    |-> 1,
                                              partition_epoch |-> part_epoch]
                                      \* CASE --- Replica is not in the initial ISR and stale --
                                      [] OTHER ->
                                             [replicas        |-> init_replicas,
                                              isr             |-> init_replicas,
                                              maximal_isr     |-> init_replicas,
                                              leader          |-> 1, \* broker 1
                                              leader_epoch    |-> 1,
                                              partition_epoch |-> 1]]
        \* the partition data on each replica starts empty
        /\ partition_data = [b \in Brokers |->
                                    [log                |-> <<>>,
                                     hwm                |-> 1,
                                     leo                |-> 1]]
        /\ partition_leso = [b \in Brokers |-> IF b = 1 THEN 1 ELSE Nil]                                     
        /\ partition_replica_state = [b \in Brokers |->
                                        [b1 \in Brokers |-> BlankReplicaState]]
        /\ partition_pending_ap = [b \in Brokers |-> [epoch |-> 0, request |-> Nil]]
        /\ aux_broker_epoch = BrokerCount
        /\ aux_ctrs = [incarn_ctr                |-> BrokerCount + 1,
                       no_data_loss_shutdown_ctr |-> 0,
                       data_loss_shutdown_ctr    |-> 0,
                       fence_broker_ctr          |-> 0,
                       leader_shrink_isr_ctr     |-> 0,
                       reassignment_ctr          |-> 0]
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
    \/ DataLossShutdown 
    \/ NoDataLossShutdown
    \* controller actions  
    \/ ReceiveBrokerRegRequest
    \/ ReceiveAlterPartitionRequest
    \/ FenceBroker
    \/ UnfenceBroker
    \/ PerformPartitionReassignment

\* For liveness checking, we only need actions that help the 
\* cluster make progress and help the cluster recover from 
\* failures. Perturbations are excluded.
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
