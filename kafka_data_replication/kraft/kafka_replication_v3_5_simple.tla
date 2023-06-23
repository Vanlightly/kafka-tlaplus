-------------------------- MODULE kafka_replication_v3_5_simple --------------------------

EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences, SequencesExt, TLC, TLCExt

(*
-------------------------------------------------------------------------------------
------- SIMPLIFIED Kafka data replication protocol with the KRaft Controller --------

A **simplified** TLA+ specification of the protocol as of June 2023 (version 3.5.0).

This specification models the Kafka replication protocol which consists
of the distributed KRaft controller RSM which works in consort with each partition.
Each partition is comprised a leader replica and multiple follower replicas.

The controller is responsible for:
- Broker registration
- Failure detection (fencing/unfencing)
- Leader election.
- Co-management of the ISR of each partition.
- Serving metadata records to the brokers.

Each partition leader is responsible for:
- Handling fetch requests from followers
- Managing the high watermark (HWM)
- Adding and removing replicas to/from the ISR based on how
  caught up (or not) the followers are.
  
This specification has been simplified to remove some aspects of
the controller and broker lifecycle:
- No heartbeats.
- Broker jumps from STARTING to RUNNING without heartbeats.
- The controlled shutdown sequence has been removed.
- Active broker set on the controller not modeled as the
  controlled shutdown sequence is omitted.

NOTES:
- Only models acks=all.
- Only models a single partition.
- This spec does not model the controller as a distributed Raft based RSM as it
  would add a lot of complexity. There is a separate TLA+ specification for
  the KRaft implementation of Raft, therefore we abstract the internals of the 
  RSM for this specification. 
- Does not model replica set changes, only ISR and leader changes.
- Session timeouts simply happen. No tracking of heartbeat times (continuous time
  is not real in TLA+).
- Most communication is done by message passing but the following are modelled
  differently, to reduce the state space:
    - Metadata log records eventually arrive at brokers, in order. There are no
      metadata requests in this spec.
    - The "look up offset for epoch" process by a follower is done atomically.
- The word "broker" refers to broker state (not concerned with partitions).
  The word "replica" refers to one instance of a partition on a broker. One
  broker can host multiple partitions and therefore replicas.
- The state space would be infinite as most actions involve sending
  a message and the history of messages is included in the global state.
  Therefore, some constants are used to limit the number of times certain
  actions can occur.
- Some formula are purely for the spec and should be ignored when using
  the spec to understand the design. These formulas are prefixed with
  __, such as __IgnoreThis.

Invariants:
- No acknowledged data is lost.
- No consumed data is lost.
- No divergence between the leader log and the history of consumed records.
- No divergence between the leader log and follower logs up to the HWM.
- No divergence between the controller metadata log and broker metadata logs.

Liveness checks (assuming any failures are transitory):
- STARTING brokers eventually reach RUNNING
- FENCED brokers eventually become UNFENCED.
- Eventually, all brokers converge on controller metadata state.
- Eventually a write will be acknowledged (positively or negatively.
- Eventually a positively acknowledged write will be fully replicated.

Jump to the bottom of the spec for the Next state formula which lists all
the actions.
*)

CONSTANTS ReplicationFactor, \* the number of replicas (and brokers).
          Values,            \* the producer data values that can be written
          MinISR,            \* the min.insync.replicas
          InitIsrSize        \* the initial ISR size. When InitIsrSize < BrokerCount
                             \* a corresponding number of brokers start outside the ISR.
                             \* This allows us to explore some scenarios that are too costly
                             \* to reach with brute-force model checking.
\* state space limits
CONSTANTS CleanShutdownLimit,       \* limits the number of clean shutdowns
          UncleanShutdownLimit,     \* limits the number of unclean shutdowns
          FenceStaleLimit,          \* limits the number of times the controller arbitrarily fences a broker
          AlterPartitionLimit       \* limits the number of AlterPartition requests that can be sent

\* Controller-side broker statuses
CONSTANTS FENCED,           
          UNFENCED

\* Broker-side statuses
CONSTANTS STARTING,
          RUNNING,
          OFFLINE_CLEAN,\* not really an actual state, used by the spec to say it is offline due to a clean shutdown
          OFFLINE_DIRTY \* not really an actual state, used by the spec to say it is offline due to an unclean shutdown

\* Replica statuses
CONSTANTS Leader,       
          Follower,
          Truncating
          
\* Requests and responses
CONSTANTS RegisterBrokerRequest,
          RegisterBrokerResponse,
          AlterPartitionRequest,
          AlterPartitionResponse,
          FetchRequest,
          FetchResponse

\* metadata log entry types
CONSTANTS PartitionChangeRecord

\* other
CONSTANTS Controller,        \* used to denote the destination or source of a message is the controller
          NoLeader,          \* a constant value to represent the partition has no leader
          IneligibleReplica, \* An AlterPartition error code.
          Nil                \* a constant used to denote 'nothing' or 'not set'

ASSUME InitIsrSize <= ReplicationFactor
ASSUME MinISR <= ReplicationFactor
ASSUME CleanShutdownLimit \in Nat
ASSUME UncleanShutdownLimit \in Nat
ASSUME FenceStaleLimit \in Nat
ASSUME AlterPartitionLimit \in Nat

\* Controller state
VARIABLES con_unfenced,         \* the set of brokers which are in the state UNFENCED.
          con_broker_state,     \* a map of broker id to broker state (known to the controller).
          con_part_state,       \* the current state of the partition (leader, leader_epoch, isr).
          con_metadata_log      \* the KRaft metadata log.
          
\* Broker state not concerned with partitions.
\* Each variable is a map of [broker_id -> some state of that broker].          
VARIABLES broker_state,         \* state of each broker, such as status (RUNNING, STARTING etc)
          broker_metadata_log   \* the strongly eventually consistent copy of the 
                                \* KRaft metadata log on each broker.

\* Broker-side replica and partition state
\* Each variable is a map of [broker_id -> some state of the replica or partition on that broker].          
VARIABLES replica_status,
          replica_part_state,      \* the partition state on each replica.
          replica_part_data,       \* the actual partition log data on each replica.
          replica_fetch_state,     \* the state of the last pending fetch request
          replica_replica_state,   \* a map (used by the leader) to track the state of follower replicas
          replica_pending_ap_epoch \* the partition epoch of an outstanding AlterPartition
                                   \* request. Used to control when AP requests can be sent.

\* Message passing state
VARIABLES messages  \* a collection used by the message passing logic.

\* Auxilliary variables (not part of the protocol)           
VARIABLES aux_ctrs   \* Some counters used to limit the number of times certain actions can occur, to limit the state space.

\* Auxilliary variables for verifying invariants (not part of the protocol)
VARIABLES inv_acked,     \* Tracks whether a producer message has been acknowledged or not.
                         \* This is required to detect data loss.
          inv_hwm,       \* Tracks the max HWM on each broker.
          inv_consumed   \* Tracks the records consumed to detect divergence.

\* Variable lists
con_broker_vars == << con_unfenced, con_broker_state >>
con_vars == << con_metadata_log,  con_broker_vars, con_part_state >>
broker_vars == << broker_state, broker_metadata_log >>
replica_vars == << replica_status, replica_part_state, replica_part_data,
                   replica_replica_state, replica_fetch_state,
                   replica_pending_ap_epoch >>
inv_vars == << inv_acked, inv_hwm, inv_consumed >>
aux_vars == << aux_ctrs >>    
vars == << con_vars, broker_vars, replica_vars, messages, inv_vars, aux_vars >>
view == << con_vars, broker_vars, replica_vars, messages, inv_vars >>

\* The set of brokers. Note that broker ids and replica
\* ids are the same, and so Brokers ised used within replica logic
\* contexts.
Brokers == 1..ReplicationFactor

\* ======================================================================
\* ------------ Object type definitions ---------------------------------

BrokerSideState ==
    [status: { OFFLINE_CLEAN, OFFLINE_DIRTY, STARTING, RUNNING },
     broker_epoch: Nat,
     incarnation_id: Nat,
     registered: BOOLEAN]
     
ControllerSideBrokerState ==
    [status: {FENCED, UNFENCED},
     broker_epoch: Nat,
     incarnation_id: Nat]
     
FetcherState ==
    [\* the current fetch position
     fetch_offset: Nat,
     \* TRUE when the fetcher is waiting for a fetch resonse
     pending_response: BOOLEAN]

ReplicaState ==
    [leo: Nat, 
     broker_epoch: Nat]     
     
ControllerPartitionState ==
    [isr: SUBSET Brokers,
     leader: Brokers \union {NoLeader},
     leader_epoch: Nat,
     partition_epoch: Nat]
     
ReplicaPartitionState ==
    [isr: SUBSET Brokers,
     maximal_isr: SUBSET Brokers,
     leader: Brokers \union {NoLeader},
     leader_epoch: Nat,
     partition_epoch: Nat]     

PartitionRecord ==
    [epoch: Nat,
     offset: Nat,
     value: Values]

PartitionLog ==
    SeqOf(PartitionRecord, Cardinality(Values))

PartitionData ==
    [log: PartitionLog,
     hwm: Nat,
     leo: Nat,
     epoch_start_offset: Nat \union {Nil}]
     
StateSpaceLimitCtrs ==
    [incarn_ctr: Nat,
     clean_shutdown_ctr: Nat,
     unclean_shutdown_ctr: Nat,
     fence_stale_ctr: Nat,
     alter_part_ctr: Nat] 

AuxState ==
    [\* The partition epoch the replica is expecting an AlterPartition response for
     pending_ap_epoch: Nat]

\* ======================================================================
\* ------------ Messages type definitions -------------------------------

RegisterBrokerRequestType ==
    [type: {RegisterBrokerRequest},
     broker_id: Nat,
     incarnation_id: Nat,
     dest: {Controller},
     source: Nat] 

RegisterBrokerResponseType ==
    [type: {RegisterBrokerResponse},
     broker_id: Nat,
     broker_epoch: Nat,
     dest: Nat,
     source: {Controller}]
     
AlterPartitionRequestType ==
    [type: {AlterPartitionRequest},
     isr: SUBSET Brokers,
     isr_and_epochs: SUBSET Brokers :> Nat,
     leader: Brokers,
     leader_epoch: Nat,
     partition_epoch: Nat,
     broker_epoch: Nat,
     source: Brokers,
     dest: {Controller}]
     
AlterPartitionResponseType ==
    [type: {AlterPartitionResponse},
     error: {Nil, IneligibleReplica},   
     isr: SUBSET Brokers,
     leader: Brokers,
     leader_epoch: Nat,
     partition_epoch: Nat,
     dest: {Controller},
     source: Brokers]     

FetchRequestType ==
    [type: {FetchRequest},
     broker_epoch: Nat,
     leader_epoch: Nat,
     fetch_offset: Nat,
     dest: Brokers,
     source: Brokers]
     
FetchResponseType ==
    [type: {FetchResponse},
     leader_epoch: Nat,
     fetch_offset: Nat,
     hwm: Nat,
     data: PartitionRecord,
     dest: Brokers,
     source: Brokers]       

\* ======================================================================
\* ----- Message passing ------------------------------------------------

\* Send the message whether it already exists or not.
\* If it does exist, the delivery count will go above 1 and
\* the message can be delivered multiple times.
SendFunc(m, msgs, deliver_count) ==
    IF m \in DOMAIN msgs
    THEN [msgs EXCEPT ![m] = @ + 1]
    ELSE msgs @@ (m :> deliver_count)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
DiscardFunc(m, msgs) ==
    [msgs EXCEPT ![m] = @ - 1]

\* Send a message, without restriction
Send(m) ==
    messages' = SendFunc(m, messages, 1)

\* Set the delivery count to 0 so the message cannot be processed again.
Discard(d) ==
    messages' = DiscardFunc(d, messages)

\* Discard incoming message and reply with another    
Reply(d, m) ==
    /\ d \in DOMAIN messages
    /\ messages[d] > 0 \* message must exist
    /\ messages' = SendFunc(m, DiscardFunc(d, messages), 1)

\* TRUE iff the message is of the desired type and has not
\* been delivered yet.
ReceivableMsg(m, type) ==
    /\ m.type = type
    /\ messages[m] > 0  \* the message hasn't been delivered yet

\* ==========================================================================
\* -- Anti-cycle checks (for liveness properties and state space limiting) --
\*
\* To avoid cycles such as infinite fetch request/responses, the spec limits
\* fetch requests to when they are required to make progress.
\* Generally speaking, you can ignore this.

__FetchMakesProgress(b) ==
    LET leader == replica_part_state[b].leader
    IN /\ replica_part_state[b].leader_epoch = replica_part_state[leader].leader_epoch
       /\ \/ replica_part_data[b].leo < replica_part_data[leader].leo        \* leader has records to get
          \/ replica_part_data[b].hwm < replica_part_data[leader].hwm        \* leader has hwm to get
          \/ replica_part_data[b].leo > replica_replica_state[leader][b].leo \* leader doesn't know current leo of follower

__NeedFetchRequestForProgress(b, m) ==
    \/ replica_part_data[b].leo > m.fetch_offset - 1
    \/ replica_replica_state[b][m.source].leo < m.fetch_offset - 1
    \/ replica_part_data[b].hwm > replica_part_data[m.source].hwm

\* Used to perform an atomic LookUpOffsetForEpoch to
\* limit state space.
__RemoteBrokerKnowsItIsLeader(l, leader_epoch) ==
    /\ broker_state[l].status = RUNNING
    /\ replica_status[l] = Leader
    /\ replica_part_state[l].leader_epoch = leader_epoch

\* ======================================================================
\* ------------ Helpers -------------------------------------------------

NilRecord ==
    [epoch |-> 0, offset |-> 0, value |-> Nil]

\* TRUE if the record with the offset of the given log
\* matches (or is lower than) the given epoch 
IsEpochEqualOrLower(log, offset, epoch_offset) ==
    /\ offset <= epoch_offset.offset
    /\ log[offset].epoch = epoch_offset.epoch

BlankReplicaState ==
    [leo          |-> 0,
     broker_epoch |-> 0]

\* a replica resets its LEO tracker when it changes role.
ResetReplicaState(b) ==
    replica_replica_state' = [replica_replica_state EXCEPT ![b] = 
                                [b1 \in Brokers |-> BlankReplicaState]]

\* TRUE if all replicas in the ISR have told the leader they have it
IsCommitted(b, maximal_isr, replica_state, offset) ==
    /\ Cardinality(maximal_isr) >= MinISR
    /\ \A b1 \in maximal_isr :
        replica_state[b1].leo >= offset

\* Find the highest (contiguous) offset that has been committed on the leader
HighestCommitted(b, maximal_isr, replica_state) ==
    CASE replica_part_data[b].leo = 0 ->
            0
      [] \E offset \in 1..replica_part_data[b].leo :
            IsCommitted(b, maximal_isr, replica_state, offset) ->
                 CHOOSE offset \in 1..replica_part_data[b].leo :
                    /\ IsCommitted(b, maximal_isr, replica_state, offset)
                    /\ ~\E offset1 \in 1..replica_part_data[b].leo :
                        /\ IsCommitted(b, maximal_isr, replica_state, offset1)
                        /\ offset1 > offset
      [] OTHER -> 0

\* If the new HWM is higher then, advance the HWM and record it in
\* related invariant variables.  
MaybeAdvanceHighWatermark(b, old_hwm, new_hwm) ==
    IF new_hwm > old_hwm
    THEN /\ replica_part_data' = [replica_part_data EXCEPT ![b].hwm = new_hwm]
         \* record which values got acked to producers
         /\ inv_acked' = [v \in DOMAIN inv_acked |->
                                 IF /\ inv_acked[v] = Nil
                                    /\ \E offset \in old_hwm+1..new_hwm :
                                       replica_part_data[b].log[offset].value = v
                                 THEN TRUE
                                 ELSE inv_acked[v]]
         \* record the highest HWM for this replica (for checking monotonicity)
         /\ inv_hwm' = [inv_hwm EXCEPT ![b] = IF new_hwm > inv_hwm[b]
                                              THEN new_hwm ELSE inv_hwm[b]]
         \* record which records got consumed by consumers
         /\ inv_consumed' = inv_consumed \o SubSeq(replica_part_data[b].log, old_hwm+1, new_hwm)
    ELSE UNCHANGED << replica_part_data, inv_acked, inv_hwm, inv_consumed >>

\* If the ISR has shrunk below minISR, or the replica lost leadership
\* then negatively acknowledge all uncommitted records.
MaybeFailPendingWrites(b, part_state) ==
    LET leo == replica_part_data[b].leo
        hwm == replica_part_data[b].hwm
        log == replica_part_data[b].log
    IN
        IF hwm = leo
        THEN UNCHANGED inv_acked
        ELSE IF \/ Cardinality(part_state.maximal_isr) < MinISR
                \/ b # part_state.leader
             THEN inv_acked' = [v \in DOMAIN inv_acked
                                        |-> IF /\ inv_acked[v] = Nil
                                               /\ \E offset \in hwm+1..leo : log[offset].value = v
                                            THEN FALSE \* neg ack
                                            ELSE inv_acked[v]]
             ELSE UNCHANGED inv_acked

\* If the ISR has shrunk but is still >= MinISR, then we may
\* need to advance the high watermark and ack records, else
\* if the ISR is now < MinISR we may need to negatively ack records 
MaybeUpdateHwmOnPartitionChange(b, part_state) ==
    IF Cardinality(part_state.maximal_isr) >= MinISR
    THEN LET old_hwm == replica_part_data[b].hwm
             new_hwm == HighestCommitted(b, part_state.maximal_isr,
                                         replica_replica_state[b])
         IN MaybeAdvanceHighWatermark(b, old_hwm, new_hwm)
    ELSE /\ MaybeFailPendingWrites(b, part_state)
         /\ UNCHANGED << replica_part_data, inv_hwm, inv_consumed >>

\* Restart a fetcher by setting the fetch_offset to the LEO + 1
\* in the case that this is a new leader epoch or there is no
\* pending fetch response. Else keep the fetch offset unchanged
\* as it means the replica was already a follower and has a valid
\* outstanding fetch request.
StartFetcher(b, leader_epoch, leo) ==
    IF \/ leader_epoch > replica_part_state[b].leader_epoch
       \/ replica_fetch_state[b].pending_response = FALSE
    THEN replica_fetch_state' = [replica_fetch_state EXCEPT ![b] = 
                                    [fetch_offset     |-> leo + 1,
                                     pending_response |-> FALSE]]
    ELSE UNCHANGED replica_fetch_state


StopFetcher(b) ==
    replica_fetch_state' = [replica_fetch_state EXCEPT ![b] = 
                                [fetch_offset     |-> 0,
                                 pending_response |-> FALSE]]

ResetPendingAlterPartition(b) ==
    replica_pending_ap_epoch' = [replica_pending_ap_epoch EXCEPT ![b] = 0]

NoPartitionChange ==
    UNCHANGED << con_part_state, con_metadata_log >>

\* When a partition state change is required, the controller
\* does two things: update the in-memory state and append 
\* a PartitionChangeRecord to the metadata log.
\* Note this order is the reverse in the implementation but is
\* not relevant to the spec.
ApplyPartitionChange(new_leader, new_isr, leader_epoch, 
                     part_epoch) ==
    /\ con_part_state' = [isr             |-> new_isr,
                          leader          |-> new_leader, 
                          leader_epoch    |-> leader_epoch,
                          partition_epoch |-> part_epoch]
    /\ con_metadata_log' = Append(con_metadata_log,
                                [type            |-> PartitionChangeRecord,
                                 leader          |-> new_leader,
                                 isr             |-> new_isr,
                                 leader_epoch    |-> leader_epoch,
                                 partition_epoch |-> part_epoch])

\* For when a broker status change occurs, but no change
\* to the partition state is required.
AppendBrokerStateRecordOnly(broker_state_rec) ==
    /\ con_metadata_log' = Append(con_metadata_log, broker_state_rec)
    /\ UNCHANGED con_part_state

\* ==================================================================
\*              ACTIONS
\* ==================================================================

(* ---------------------------------------------------------------
   ACTION: BrokerStart

   A stopped broker starts-up in the STARTING status
   and sends a new broker registration request
   to the controller with a new incarnation id.
   ---------------------------------------------------------------*)

SendBrokerRegistration(b) ==
    /\ Send([type           |-> RegisterBrokerRequest,
             broker_id      |-> b,
             incarnation_id |-> aux_ctrs.incarn_ctr,
             dest           |-> Controller,
             source         |-> b])
    /\ aux_ctrs' = [aux_ctrs EXCEPT !.incarn_ctr = @ + 1]

BrokerStart ==
    \E b \in Brokers :
        \* enabling conditions
        /\ broker_state[b].status \in { OFFLINE_CLEAN, OFFLINE_DIRTY }
        \* state mutations
        /\ broker_state' = [broker_state EXCEPT ![b] = 
                                [status            |-> STARTING,
                                 broker_epoch      |-> 0,
                                 incarnation_id    |-> aux_ctrs.incarn_ctr,
                                 registered        |-> FALSE]]
        /\ replica_status' = [replica_status EXCEPT ![b] = Nil]
        /\ replica_fetch_state' = [replica_fetch_state EXCEPT ![b] = 
                                        [fetch_offset     |-> replica_part_data[b].leo + 1,
                                         pending_response |-> FALSE]]
        /\ replica_replica_state' = [replica_replica_state EXCEPT ![b] =
                                        [b1 \in Brokers |-> BlankReplicaState]]
        /\ ResetPendingAlterPartition(b)
        /\ SendBrokerRegistration(b)
        /\ UNCHANGED << con_vars, broker_metadata_log, replica_part_state,
                        replica_part_data, inv_vars >>        

(* ---------------------------------------------------------------
   ACTION: ReceiveBrokerRegRequest

   The controller receives a RegisterBrokerRequest and
   only accepts it if:
   - there is no registration record (not modelled)
   - the broker is FENCED
   - the broker is not FENCED and the incarnation id matches
     the existing registration.
   
   The controller assigns the broker an epoch based on the last 
   offset in the metadata log. The broker starts in the FENCED status.
------------------------------------------------------------------*)

ReceiveBrokerRegRequest ==
    \E m \in DOMAIN messages :
        \* enabling conditions
        /\ ReceivableMsg(m, RegisterBrokerRequest)
        /\ \/ con_broker_state[m.source].status = FENCED
           \/ /\ con_broker_state[m.source].status # FENCED
              /\ con_broker_state[m.source].incarnation_id = m.incarnation_id
        \* state mutations
        /\ LET b              == m.source
               broker_epoch   == Len(con_metadata_log) + 1
            IN
                /\ con_broker_state' = [con_broker_state EXCEPT ![b] =
                                            [status              |-> FENCED,
                                             broker_epoch        |-> broker_epoch,
                                             incarnation_id      |-> m.incarnation_id]]
                \* this simplified version omits BrokerRegistrationRecords
                /\ con_metadata_log' = con_metadata_log 
                /\ Reply(m, 
                        [type         |-> RegisterBrokerResponse,
                         broker_epoch |-> broker_epoch,
                         dest         |-> b,
                         source       |-> Controller])
                /\ UNCHANGED << broker_vars, replica_vars, con_part_state,
                                con_unfenced, inv_vars, aux_vars >>

(*---------------------------------------------------------------
  ACTION: ReceiveBrokerRegResponse

  A broker receives a RegisterBrokerResponse and updates its 
  broker epoch and registered state. 

  In this simplified version, the broker jumps straight
  to RUNNING. The process of catching up to its own 
  BrokerRegistrationRecord in the metadata log and sending heartbeats
  is omitted.
----------------------------------------------------------------*)

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
        /\ Discard(m)
        /\ UNCHANGED << con_vars, replica_vars, broker_metadata_log, 
                        inv_vars, aux_vars >>

(*--------------------------------------------------------------------
  ACTION: UnfenceBroker

  The controller unfences a fenced broker. In the implementation
  this would happen due to a heartbeat. This spec simply
  allows this to occur at any time to a fenced broker.

  A unfenced broker is not added to an ISR but can be made
  leader of a partition which has no leader as long as it
  is a member of the ISR.
  
  In this simplified version, this unfence action replaces
  the heartbeat. As long as the broker is running, we simulate
  that heartbeats can be received without actually modeling them.
---------------------------------------------------------------------*)

\* The ISR cannot drop below 1
MaybeRemoveBrokerFromISR(isr, b) ==
    IF Cardinality(isr) = 1
    THEN isr
    ELSE isr \ {b}    
    
\* TRUE iff no leader change is required    
NoLeaderChange(new_isr, new_unfenced) ==
    \* either there is no leader and there is no leader candidate either
    \/ /\ con_part_state.leader = NoLeader
       /\ ~\E candidate \in new_isr : candidate \in new_unfenced
    \* or the leader is in the ISR and is unfenced (so no need to change it)
    \/ /\ con_part_state.leader \in new_isr
       /\ con_part_state.leader \in new_unfenced

\* Based on the new ISR and unfenced broker set, decide
\* whether a partition state change is required or not.
MaybeUpdatePartitionState(new_isr, new_unfenced) ==
    CASE /\ NoLeaderChange(new_isr, new_unfenced)
         /\ new_isr = con_part_state.isr ->
            \* no-op
            NoPartitionChange
      [] /\ NoLeaderChange(new_isr, new_unfenced)
         /\ new_isr # con_part_state.isr ->
            \* basically, ISR change but no leader change. 
            \* Update partition state and append partition change record.
            ApplyPartitionChange(con_part_state.leader, new_isr, 
                                 con_part_state.leader_epoch,
                                 con_part_state.partition_epoch + 1)
      [] \E candidate \in new_isr : candidate \in new_unfenced ->
            \* basically, at the very least, there is a leader change.
            \* Non-deterministically choose a valid candidate for leader.
            \* Update partition state and append partition change record.
            \E candidate \in new_isr :
                /\ candidate \in new_unfenced
                /\ ApplyPartitionChange(candidate, new_isr, 
                                        con_part_state.leader_epoch + 1,
                                        con_part_state.partition_epoch + 1)
      [] ~\E candidate \in new_isr : candidate \in new_unfenced ->
            \* The ISR remains the same, but there is no leader.
            \* This is the case where the ISR was 1 and the leader got fenced.
            \* Update partition state and append partition change record.
            ApplyPartitionChange(NoLeader, new_isr, 
                                 con_part_state.leader_epoch + 1,
                                 con_part_state.partition_epoch + 1)
      [] OTHER -> \* no-op 
            NoPartitionChange

HandleBrokerUnfenced(b, bstate) ==
    LET new_isr      == con_part_state.isr \* unfencing doesn't change the ISR
        new_unfenced == con_unfenced \union {b}
    IN \* if there is no leader the controller can choose one from the ISR.
       /\ IF con_part_state.leader = NoLeader 
          THEN MaybeUpdatePartitionState(new_isr, new_unfenced)
          ELSE NoPartitionChange
       /\ con_unfenced' = new_unfenced

UnfenceBroker ==
    \* enabling conditions
    \E b \in Brokers :
        /\ con_broker_state[b].status = FENCED
        /\ broker_state[b].status = RUNNING
        \* state mutations
        /\ HandleBrokerUnfenced(b, con_broker_state[b])
        /\ con_broker_state' = [con_broker_state EXCEPT ![b].status = UNFENCED]
        /\ UNCHANGED << broker_vars, replica_vars, messages, inv_vars, 
                        aux_ctrs >>

(*--------------------------------------------------------------------
  ACTION: FenceBroker

  The controller fences an unfenced broker. In the implementation
  this would happen due to a lack of heartbeats. This spec simply
  allows this to occur at any time to an unfenced broker.

  A fenced broker is removed from any leadership. Also it is removed
  from any ISRs though the ISR cannot drop below 1.
---------------------------------------------------------------------*)

HandleBrokerFenced(b, bstate) ==
    LET new_isr      == MaybeRemoveBrokerFromISR(con_part_state.isr, b)
        new_unfenced == con_unfenced \ {b}
    IN /\ MaybeUpdatePartitionState(new_isr, new_unfenced)
       /\ con_unfenced' = new_unfenced

FenceBroker ==
    \* enabling conditions
    /\ aux_ctrs.fence_stale_ctr < FenceStaleLimit
    /\ \E b \in Brokers :
        /\ con_broker_state[b].status = UNFENCED
        \* state mutations
        /\ HandleBrokerFenced(b, con_broker_state[b])
        /\ con_broker_state' = [con_broker_state EXCEPT ![b].status = FENCED]
        /\ aux_ctrs' = [aux_ctrs EXCEPT !.fence_stale_ctr = @ + 1]
        /\ UNCHANGED << broker_vars, replica_vars, messages, inv_vars >>

(*-----------------------------------------------------------------------
  ACTION: ReceiveMetadataPartitionChangeRecords

  NOTE! This action contains a lot of logic.

  When a broker receives sequence of metadata log PartitionChangeRecords 
  it can take various actions:
  - When it receives multiple PartionChangeRecords, it acts on the most recent:
       - it may have become the partition leader and therefore records the
         start offset for this leader epoch (the LEO on becoming leader).
       - it may have become a follower and now needs to switch to
         "truncating" then to "follower". If the new leader has assumed
         leadership then, the replica performs a "lookup offset for epoch"
         against the leader. The follower truncates its log depending on 
         the result of the lookup. If the leader hasn't assumed leadership yet,
         the replica switches to "truncating" until the leader assumes leadership
         and the follower can perform the "lookup offset for epoch".
       - there may be no leader, so it simply waits for the next PartionChangeRecord.
       - uncommitted pending writes may need to be failed:
           - if the replica has lost leadership
           - the ISR has shrunk below minISR.
           
   In this simplified version, there are no broker registration or
   fence/unfence records.
-----------------------------------------------------------------------*)           

RECURSIVE FindHighestOffsetUpToEpoch(_,_,_)
FindHighestOffsetUpToEpoch(b, epoch, offset) ==
    \* search log backwards
    CASE offset = 0 -> NilRecord
      [] replica_part_data[b].log[offset].epoch <= epoch ->
            replica_part_data[b].log[offset]
      [] OTHER -> FindHighestOffsetUpToEpoch(b, epoch, offset - 1)
    
\* this does an atomic lookup against the leader which is
\* cheating, but it reduces the state space.
LookupOffsetForEpoch(leader, follower) ==
    \* if the follower log is empty, then use offset 0 
    IF replica_part_data[follower].leo = 0
    THEN NilRecord
    ELSE LET follower_log == replica_part_data[follower].log
             leader_log   == replica_part_data[leader].log
             last_epoch   == Last(follower_log).epoch
         IN FindHighestOffsetUpToEpoch(leader, 
                                       last_epoch, 
                                       Len(leader_log)) \* start at the end of the leader log

TruncateToSafePoint(b, log, hwm, part_state) ==
    LET epoch_offset == LookupOffsetForEpoch(part_state.leader, b)
        highest_common == CHOOSE offset \in DOMAIN log :
                            /\ IsEpochEqualOrLower(log, offset, epoch_offset)
                            /\ ~\E offset2 \in DOMAIN log :
                                /\ IsEpochEqualOrLower(log, offset2, epoch_offset)
                                /\ offset2 > offset
    IN IF \E offset \in DOMAIN log : IsEpochEqualOrLower(log, offset, epoch_offset)
       THEN [log                |-> [offset \in 1..highest_common |-> log[offset]],
             leo                |-> highest_common,
             hwm                |-> hwm, \* truncating does not affect the hwm
             epoch_start_offset |-> Nil] 
       ELSE [log |-> <<>>, hwm |-> 0, leo |-> 0, epoch_start_offset |-> Nil]

NextRecords(index) ==
    SubSeq(con_metadata_log, index, Len(con_metadata_log))

RemainLeader(b, new_part_state) ==
    /\ MaybeUpdateHwmOnPartitionChange(b, new_part_state)
    /\ UNCHANGED << replica_status, replica_replica_state, 
                    replica_fetch_state, replica_pending_ap_epoch>>
    
BecomeLeader(b) ==
    /\ replica_status' = [replica_status EXCEPT ![b] = Leader]
    /\ replica_part_data' = [replica_part_data EXCEPT ![b].epoch_start_offset = 
                                replica_part_data[b].leo]
    /\ ResetReplicaState(b)
    /\ ResetPendingAlterPartition(b)
    /\ StopFetcher(b)
    /\ UNCHANGED << inv_vars >>
    
BecomeFollower(b, log, hwm, new_part_state) ==
    LET new_part_data == TruncateToSafePoint(b, log, hwm, new_part_state)
    IN
        /\ MaybeFailPendingWrites(b, new_part_state)
        /\ replica_status' = [replica_status EXCEPT ![b] = Follower]
        /\ replica_part_data' = [replica_part_data EXCEPT ![b] = new_part_data]
        /\ ResetReplicaState(b)
        /\ StartFetcher(b, new_part_state.leader_epoch, new_part_data.leo)
        /\ ResetPendingAlterPartition(b)
        /\ UNCHANGED << inv_hwm, inv_consumed >>
    
SwitchToTruncating(b, new_part_state) ==
    /\ MaybeFailPendingWrites(b, new_part_state)
    /\ replica_status' = [replica_status EXCEPT ![b] = Truncating]
    /\ ResetReplicaState(b)
    /\ ResetPendingAlterPartition(b)
    /\ StopFetcher(b)
    /\ UNCHANGED << replica_part_data, inv_hwm, inv_consumed >>
    
WaitForLeaderChange(b, new_part_state) ==
    /\ MaybeFailPendingWrites(b, new_part_state)
    /\ replica_status' = [replica_status EXCEPT ![b] = Nil]
    /\ ResetPendingAlterPartition(b)
    /\ StopFetcher(b)
    /\ UNCHANGED << replica_part_data, replica_replica_state, 
                    inv_hwm, inv_consumed >>

ReceiveMetadataPartitionChangeRecords ==
    \E b \in Brokers :
        LET curr_md_offset == Len(broker_metadata_log[b])
            next_records   == NextRecords(curr_md_offset + 1)
            last_pc_record == Last(next_records)
            new_part_state == [isr             |-> last_pc_record.isr,
                               maximal_isr     |-> last_pc_record.isr,
                               leader          |-> last_pc_record.leader,
                               leader_epoch    |-> last_pc_record.leader_epoch,
                               partition_epoch |-> last_pc_record.partition_epoch]
            can_truncate   == IF \/ last_pc_record.leader = NoLeader
                                 \/ b = last_pc_record.leader
                              THEN FALSE 
                              ELSE __RemoteBrokerKnowsItIsLeader(last_pc_record.leader,
                                                                 last_pc_record.leader_epoch)
        IN
            \* enabling conditions
            /\ broker_state[b].status \notin {OFFLINE_CLEAN, OFFLINE_DIRTY}
            /\ broker_state[b].registered = TRUE
            /\ curr_md_offset < Len(con_metadata_log) \* there are metadata records to receive
            \* state mutations
            /\ broker_metadata_log' = [broker_metadata_log EXCEPT ![b] = @ \o next_records]
               \* If the last PartitionChangeRecord is valid, then update the local
               \* partition state and possibly become a leader or follower
            /\ IF new_part_state.partition_epoch > replica_part_state[b].partition_epoch
               THEN
                    /\ replica_part_state' = [replica_part_state EXCEPT ![b] = new_part_state]
                    /\ CASE /\ replica_part_state[b].leader = b
                            /\ last_pc_record.leader = b -> 
                                RemainLeader(b, new_part_state)
                         [] /\ replica_part_state[b].leader # b
                            /\ last_pc_record.leader = b ->
                                BecomeLeader(b)
                         [] /\ last_pc_record.leader # NoLeader
                            /\ can_truncate ->
                                \* this includes truncation then switching to follower
                                BecomeFollower(b, 
                                           replica_part_data[b].log,
                                           replica_part_data[b].hwm,
                                           new_part_state)
                         [] /\ last_pc_record.leader # NoLeader
                            /\ ~can_truncate ->
                                SwitchToTruncating(b, new_part_state)
                         [] OTHER -> WaitForLeaderChange(b, new_part_state)
               ELSE UNCHANGED << replica_vars, inv_vars >>
            /\ UNCHANGED << con_vars, broker_state, messages, aux_ctrs >>

(*-------------------------------------------------------------------------
  ACTION: DelayedTruncateAsFollower

  When the broker received the last PartitionChangeRecord that
  indicated that this broker should become a follower,
  it was unable to truncate its log to the leader because
  the leader did not yet know it was the leader.
  Now the leader knows it is leader and the lookup and truncate
  operation can complete.
--------------------------------------------------------------------------*)  

DelayedTruncateAsFollower ==
    \E b \in Brokers :
        \* enabling conditions
        /\ broker_state[b].status = RUNNING
        /\ replica_status[b] = Truncating
        /\ replica_part_state[b].leader # b
        /\ replica_part_state[b].leader # NoLeader
        /\ __RemoteBrokerKnowsItIsLeader(replica_part_state[b].leader,
                                         replica_part_state[b].leader_epoch)
        \* state mutations
        /\ BecomeFollower(b, 
                          replica_part_data[b].log,
                          replica_part_data[b].hwm,
                          replica_part_state[b])
        /\ replica_status' = [replica_status EXCEPT ![b] = Follower]
        /\ UNCHANGED << con_vars, broker_state, broker_metadata_log, replica_part_state,
                        replica_replica_state, messages, aux_ctrs >>

(*--------------------------------------------------------------------------
  ACTION: SendAlterPartitionRequest

  The leader tries to modify the ISR. 

  The leader first identifies all replicas that are caught up and adds
  them to the proposed ISR. The definition of "caught up" is that:
    a. The replica has not timed out.
    b. The replica fetch offset is >= HWM.
    c. The replica fetch offset is >= Start Epoch Offset.
  
  The leader builds an AlterPartitionRequest, including the broker 
  epochs of the brokers in the proposed ISR. The leader eagerly
  applies the maximal ISR. The maximal ISR is the union of the proposed
  ISR with the current ISR in order to maintain the invariant that the
  leader ISR must be a superset of the controller ISR. This invariant
  is required to avoid data loss where the controller selects a leader
  outside of the current leader's maximal ISR.
--------------------------------------------------------------------------*)  

IsrAndEpochs(b, isr) ==
    [b1 \in isr |-> IF b = b1
                    THEN broker_state[b].broker_epoch
                    ELSE replica_replica_state[b][b1].broker_epoch]

PendingAlterPartitionResponse(b) ==
    replica_pending_ap_epoch[b] > replica_part_state[b].partition_epoch

FollowerIsCaughtUp(b, follower, timed_out_followers) ==
    /\ replica_replica_state[b][follower].leo >= replica_part_data[b].hwm
    /\ replica_replica_state[b][follower].leo >= replica_part_data[b].epoch_start_offset
    /\ follower \notin timed_out_followers

SendAlterPartitionRequest ==
    \* enabling conditions
    /\ aux_ctrs.alter_part_ctr < AlterPartitionLimit
    /\ \E b \in Brokers :
        /\ broker_state[b].status = RUNNING
        /\ ~PendingAlterPartitionResponse(b)
        /\ replica_status[b] = Leader
        /\ \E timed_out_followers \in SUBSET Brokers :
            /\ b \notin timed_out_followers
            /\ LET curr_isr     == replica_part_state[b].isr
                   proposed_isr == { b1 \in Brokers : \/ b1 = b 
                                                      \/ FollowerIsCaughtUp(b, b1, timed_out_followers) }
               IN 
                  /\ proposed_isr # curr_isr
                  \* state mutations
                  /\ Send([type            |-> AlterPartitionRequest,
                           isr             |-> proposed_isr,
                           isr_and_epochs  |-> IsrAndEpochs(b, proposed_isr),
                           leader          |-> b,
                           leader_epoch    |-> replica_part_state[b].leader_epoch,
                           partition_epoch |-> replica_part_state[b].partition_epoch,
                           broker_epoch    |-> broker_state[b].broker_epoch,
                           source          |-> b,
                           dest            |-> Controller])
                  /\ replica_part_state' = [replica_part_state EXCEPT ![b].maximal_isr = 
                                               proposed_isr \union curr_isr]
                  /\ replica_pending_ap_epoch' = [replica_pending_ap_epoch EXCEPT ![b] = 
                                                    replica_part_state[b].partition_epoch + 1]
                  /\ aux_ctrs' = [aux_ctrs EXCEPT !.alter_part_ctr = @ + 1]
                  /\ UNCHANGED << con_vars, broker_metadata_log, broker_state,  
                                    replica_part_data, replica_fetch_state, replica_replica_state,
                                    replica_status, inv_vars >>

(*--------------------------------------------------------------------------
  ACTION: ReceiveAlterPartitionRequest

  The controller receives an AlterPartition request.

  It accepts the request if:
  - the request is from the current partition leader.
  - the broker epoch matches.
  - the leader epoch matches.
  - the broker epoch of all brokers in the proposed ISR matches.
  - All brokers in the proposed ISR are active and unfenced.

  The leader epoch is not incremented as this spec only models
  leader epoch changes when a leader change has occurred,
  else it remains the same. Note, this is looser than the current
  implemention.
  
  The controller sends a response with the new state of the ISR.
---------------------------------------------------------------------------*)

IsEligibleBroker(b, broker_epoch) ==
    /\ con_broker_state[b].status = UNFENCED
    /\ con_broker_state[b].broker_epoch = broker_epoch
    
EligibleIsr(m) ==
    \A b \in DOMAIN m.isr_and_epochs :
        IsEligibleBroker(b, m.isr_and_epochs[b])    

ReceiveAlterPartitionRequest ==
    \E m \in DOMAIN messages : 
        \* enabling conditions
        /\ ReceivableMsg(m, AlterPartitionRequest)
        /\ LET b == m.source
               new_ldr_epoch  == con_part_state.leader_epoch \* unchanged
               new_part_epoch == con_part_state.partition_epoch +1
           IN
              /\ b = con_part_state.leader
              /\ m.broker_epoch = con_broker_state[b].broker_epoch
              /\ m.partition_epoch = con_part_state.partition_epoch
              /\ m.leader_epoch = con_part_state.leader_epoch
              \* state mutations
              /\ IF EligibleIsr(m)
                 THEN 
                      /\ con_part_state' = [isr             |-> m.isr,
                                            leader          |-> m.leader,
                                            leader_epoch    |-> new_ldr_epoch,
                                            partition_epoch |-> new_part_epoch]
                      /\ con_metadata_log' = Append(con_metadata_log, 
                                                  [type            |-> PartitionChangeRecord,
                                                   isr             |-> m.isr,
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
                               dest            |-> b,
                               source          |-> Controller])
                 ELSE Reply(m,
                            [type            |-> AlterPartitionResponse,
                             error           |-> IneligibleReplica,
                             isr             |-> con_part_state.isr,
                             leader          |-> con_part_state.leader,
                             leader_epoch    |-> con_part_state.leader_epoch,
                             partition_epoch |-> con_part_state.partition_epoch,
                             dest            |-> b,
                             source          |-> Controller])
                    /\ UNCHANGED << con_part_state, con_metadata_log>>
        /\ UNCHANGED << con_broker_state, con_unfenced, broker_vars, 
                        replica_vars, aux_vars, inv_vars >>
              

(*------------------------------------------------------------------------------
  ACTION: ReceiveAlterPartitionResponse

  A broker receives an AlterPartition response with a partition epoch 
  that is >= to the partition epoch it knows. 

  If the response indicates success then updates its local partition
  state. If the response indicates an IneligibleReplica, it rolls back
  its eagerly applied partition state change, reverting to the last
  partition state.
--------------------------------------------------------------------------------*)

CommitPartitionChange(b, part_state) ==
    /\ replica_part_state' = [replica_part_state EXCEPT ![b] = part_state]
    /\ MaybeUpdateHwmOnPartitionChange(b, part_state)

CompletePartitionChange(b, m) ==
    CommitPartitionChange(b, [isr             |-> m.isr,
                              maximal_isr     |-> m.isr,
                              leader          |-> m.leader,
                              leader_epoch    |-> m.leader_epoch,
                              partition_epoch |-> m.partition_epoch])

RollbackPartitionChange(b) ==
    LET last_part_state == [replica_part_state[b] EXCEPT !.maximal_isr =   
                                    replica_part_state[b].isr]                      
    IN CommitPartitionChange(b, last_part_state)

ReceiveAlterPartitionResponse ==
    \E m \in DOMAIN messages : 
        \* enabling conditions
        /\ ReceivableMsg(m, AlterPartitionResponse)
        /\ LET b == m.dest
           IN
              /\ broker_state[b].status = RUNNING
              /\ replica_status[b] = Leader
              /\ PendingAlterPartitionResponse(b)
              /\ m.partition_epoch > replica_part_state[b].partition_epoch
              \* state mutations
              /\ IF m.error = Nil \* only IneligibleReplica error is modeled at the moment
                 THEN CompletePartitionChange(b, m)
                 ELSE RollbackPartitionChange(b)
              /\ ResetPendingAlterPartition(b)
              /\ Discard(m)
        /\ UNCHANGED << con_vars, broker_vars, replica_replica_state, 
                        replica_fetch_state, replica_status, 
                        aux_ctrs >>

(*-----------------------------------------------------------------------
  ACTION: SendFetchRequest

  A follower sends a fetch request to the partition leader.
  To avoid an infinite cycle of fetch request and responses
  we limit fetch requests to when a request can help the
  cluster make progress.
---------------------------------------------------------------------*)

SendFetchRequest ==
    \E b \in Brokers :
        \* enabling conditions
        /\ broker_state[b].status = RUNNING
        /\ replica_fetch_state[b].pending_response = FALSE
        /\ replica_status[b] = Follower
        /\ replica_part_state[b].leader # NoLeader
        /\ __FetchMakesProgress(b)
        \* state mutations
        /\ Send([type         |-> FetchRequest,
                 broker_epoch |-> broker_state[b].broker_epoch,
                 leader_epoch |-> replica_part_state[b].leader_epoch,
                 fetch_offset |-> replica_fetch_state[b].fetch_offset,
                 dest         |-> replica_part_state[b].leader,
                 source       |-> b])
        /\ replica_fetch_state' = [replica_fetch_state EXCEPT ![b].pending_response = TRUE]
        /\ UNCHANGED << con_vars, broker_vars, replica_part_state, replica_part_data,
                        replica_replica_state, replica_status, replica_pending_ap_epoch,
                        inv_vars, aux_vars >>
        
(*----------------------------------------------------------------------------
  ACTION: ReceiveFetchRequest
  
  A partition leader receives a fetch request. The broker may advance
  the high watermark based on the fetch offset of the fetch request.
  The broker responds to the request with a sequence of records
  and the latest high watermark.
  
  This spec only sends one record at a time.
---------------------------------------------------------------------*)  

ReceiveFetchRequest ==
    \E m \in DOMAIN messages :
        \* enabling conditions
        /\ ReceivableMsg(m, FetchRequest)
        /\ LET b      == m.dest
               updated_rep_state == [replica_replica_state[b] EXCEPT ![m.source] =
                                        [leo          |-> m.fetch_offset - 1,
                                         broker_epoch |-> m.broker_epoch]]
               old_hwm == replica_part_data[b].hwm
               new_hwm == HighestCommitted(b, replica_part_state[b].maximal_isr, 
                                           updated_rep_state)
           IN
              /\ broker_state[b].status = RUNNING
              /\ replica_status[b] = Leader
              /\ replica_part_state[b].leader_epoch = m.leader_epoch
              /\ __NeedFetchRequestForProgress(b, m)
              \* state mutations
              /\ MaybeAdvanceHighWatermark(b, old_hwm, new_hwm)
              /\ replica_replica_state' = [replica_replica_state EXCEPT ![b] = 
                                                updated_rep_state]
              /\ Reply(m,
                        [type         |-> FetchResponse,
                         leader_epoch |-> replica_part_state[b].leader_epoch,
                         fetch_offset |-> m.fetch_offset,
                         hwm          |-> IF new_hwm > old_hwm
                                          THEN new_hwm ELSE old_hwm,
                         data         |-> IF m.fetch_offset <= replica_part_data[b].leo
                                          THEN <<replica_part_data[b].log[m.fetch_offset]>> \* only send one entry
                                          ELSE <<>>, 
                         dest         |-> m.source,
                         source       |-> m.dest])
              /\ UNCHANGED << con_vars, broker_vars, replica_part_state, replica_status,
                              replica_fetch_state, replica_pending_ap_epoch, aux_vars >>        

(*-------------------------------------------------------------------
  ACTION: ReceiveFetchResponse

  A follower receives a fetch response and if the leader epoch
  matches, it appends any records to its partition log and updates
  the high watermark if needed.
  
  To prevent a stale fetch reponse from being processed, it is only
  accepted if the fetch offset matches the fetch offset of the last
  fetch request. 
---------------------------------------------------------------------*)  

ReceiveFetchResponse ==
    \E m \in DOMAIN messages :
        \* enabling conditions
        /\ ReceivableMsg(m, FetchResponse)
        /\ LET b       == m.dest
               new_leo == Len(replica_part_data[b].log) + Len(m.data)
           IN
              /\ broker_state[b].status = RUNNING
              /\ replica_status[b] = Follower
              /\ replica_fetch_state[b].pending_response = TRUE
              /\ replica_fetch_state[b].fetch_offset = m.fetch_offset
              /\ replica_part_state[b].leader_epoch = m.leader_epoch
              \* state mutations
              /\ replica_part_data' = [replica_part_data EXCEPT 
                                        ![b].log = replica_part_data[b].log \o m.data, \* append the new data
                                        ![b].leo = new_leo,
                                        \* just overwrite HWM as long as it falls within bounds of the log
                                        ![b].hwm = IF m.hwm <= new_leo
                                                   THEN m.hwm ELSE replica_part_data[b].hwm] 
              /\ replica_fetch_state' = [replica_fetch_state EXCEPT ![b] =
                                            [fetch_offset     |-> new_leo + 1,
                                             pending_response |-> FALSE]]
              /\ inv_hwm' = [inv_hwm EXCEPT ![b] = IF m.hwm > inv_hwm[b]
                                                   THEN m.hwm ELSE inv_hwm[b]]
              /\ Discard(m)
              /\ UNCHANGED << con_vars, broker_vars, replica_part_state, replica_replica_state,
                              replica_status, replica_pending_ap_epoch,
                              inv_acked, inv_consumed, aux_vars >> 

(*--------------------------------------------------------------
  ACTION: WriteRecordToLeader

  A leader receives a produce request if the maximal ISR 
  size >= minISR, it writes the value to its local partition log.
---------------------------------------------------------------------*)  

WriteRecordToLeader ==
    \E b \in Brokers, v \in Values :
        \* enabling conditions
        /\ v \notin DOMAIN inv_acked
        /\ broker_state[b].status = RUNNING
        /\ replica_status[b] = Leader
        /\ Cardinality(replica_part_state[b].maximal_isr) >= MinISR
        \* state mutations
        /\ LET new_leo == replica_part_data[b].leo + 1
               new_log == Append(replica_part_data[b].log, 
                                  [epoch  |-> replica_part_state[b].leader_epoch,
                                   offset |-> replica_part_data[b].leo + 1,
                                   value  |-> v])
           IN
              /\ replica_part_data' = [replica_part_data EXCEPT ![b] =
                                         [replica_part_data[b] EXCEPT !.leo = new_leo,
                                                                      !.log = new_log]]
              /\ replica_replica_state' = [replica_replica_state EXCEPT ![b][b].leo = 
                                            new_leo]
              /\ inv_acked' = inv_acked @@ (v :> Nil)
              /\ UNCHANGED << con_vars, broker_vars, replica_part_state, replica_status, 
                              replica_fetch_state, replica_pending_ap_epoch,
                              messages, aux_vars, inv_hwm, inv_consumed >>

(*-----------------------------------------------------------------------
  ACTION: UncleanShutdown

  A broker shutsdown uncleanly. In this spec, the entire partition log is 
  truncated. Also, in this action, the controller detects the broker 
  is unavailable and fences the broker.
---------------------------------------------------------------------*)  

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
        /\ replica_status' = [replica_status EXCEPT ![b] = Nil]
        /\ replica_part_data' = [replica_part_data EXCEPT ![b] = 
                                        [log |-> <<>>, hwm |-> 0, leo |-> 0,
                                         epoch_start_offset |-> 0]]
        /\ replica_fetch_state' = [replica_fetch_state EXCEPT ![b] = 
                                        [fetch_offset     |-> 0,
                                         pending_response |-> FALSE]]
        /\ replica_replica_state' = [replica_replica_state EXCEPT ![b] = 
                                        [b1 \in Brokers |-> BlankReplicaState]]
        /\ ResetPendingAlterPartition(b)
        /\ aux_ctrs' = [aux_ctrs EXCEPT !.unclean_shutdown_ctr = @ + 1]
        \* make the controller detect it
        /\ HandleBrokerFenced(b, con_broker_state[b])
        /\ con_broker_state' = [con_broker_state EXCEPT ![b].status = FENCED]
        /\ UNCHANGED << replica_part_state, broker_metadata_log, inv_vars,
                        messages >>
                        
(*-----------------------------------------------------------------------
  ACTION: CleanShutdown

  A broker shutsdown cleanly. Also, in this action, the controller detects the broker 
  is unavailable and fences the broker.
  
  In this simplified version, we do not include the controlled
  shutdown sequence.
---------------------------------------------------------------------*)  

CleanShutdown ==
    \* enabling conditions
    /\ aux_ctrs.clean_shutdown_ctr < CleanShutdownLimit
    /\ \E b \in Brokers :
        /\ broker_state[b].status \notin { OFFLINE_CLEAN, OFFLINE_DIRTY }
        \* state mutations
        /\ broker_state' = [broker_state EXCEPT ![b] = 
                                [status            |-> OFFLINE_CLEAN,
                                 broker_epoch      |-> 0,
                                 incarnation_id    |-> 0,
                                 registered        |-> FALSE]]
        /\ replica_status' = [replica_status EXCEPT ![b] = Nil]
        /\ replica_fetch_state' = [replica_fetch_state EXCEPT ![b] = 
                                        [fetch_offset     |-> 0,
                                         pending_response |-> FALSE]]
        /\ replica_replica_state' = [replica_replica_state EXCEPT ![b] = 
                                        [b1 \in Brokers |-> BlankReplicaState]]
        /\ ResetPendingAlterPartition(b)
        /\ aux_ctrs' = [aux_ctrs EXCEPT !.clean_shutdown_ctr = @ + 1]
        \* make the controller detect it
        /\ HandleBrokerFenced(b, con_broker_state[b])
        /\ con_broker_state' = [con_broker_state EXCEPT ![b].status = FENCED]
        /\ UNCHANGED << replica_part_state, replica_part_data, broker_metadata_log, inv_vars,
                        messages >>

\* ===============================================================
\* INVARIANTS
\* ===============================================================

\* INV: TypeOK
\* Basic type checking
TypeOK ==
    /\ con_unfenced \in SUBSET Brokers
    /\ con_broker_state \in [Brokers -> ControllerSideBrokerState]
    /\ con_part_state \in ControllerPartitionState
    /\ broker_state \in [Brokers -> BrokerSideState]
    /\ replica_part_state \in [Brokers -> ReplicaPartitionState]
    /\ replica_fetch_state \in [Brokers -> FetcherState]
    /\ replica_replica_state \in [Brokers -> [Brokers -> ReplicaState]]
    /\ replica_pending_ap_epoch \in [Brokers -> Nat]
    /\ aux_ctrs \in StateSpaceLimitCtrs
    /\ replica_status \in [Brokers -> {Leader, Follower, Truncating, Nil}]

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
        /\ IF replica_status[b] = Leader
           THEN replica_part_state[b].leader = b
           ELSE TRUE
        /\ replica_part_data[b].leo = Len(replica_part_data[b].log)
        /\ \A offset \in 1..replica_part_data[b].leo :
                replica_part_data[b].log[offset].offset = offset

\* INV: ValidControllerState
\* For catching spec bugs, ensure controller state is legal.
ValidControllerState ==
    \* there is no broker such that its fenced status is
    \* inconsistent with its membership to the unfenced set.
    /\ ~\E b \in Brokers :
        \/ /\ con_broker_state[b].status = FENCED
           /\ b \in con_unfenced              
        \/ /\ con_broker_state[b].status = UNFENCED
           /\ b \notin con_unfenced
    \* A fenced broker cannot be in an ISR of size > 1
    /\ IF Cardinality(con_part_state.isr) > 1
       THEN ~\E b \in Brokers :
               /\ con_broker_state[b].status = FENCED
               /\ b \in con_part_state.isr
       ELSE TRUE
    \* The ISR cannot be empty
    /\ con_part_state.isr # {} 

\* INV: ValidLeaderMaximalISR
\* The maximal ISR is critical for safety. The invariant here is that
\* the maximal ISR on the (non-stale) leader must be a superset of
\* the controller ISR. Else we can lose data. 
IsNonStaleLeader(b) ==
    /\ replica_status[b] = Leader
    /\ replica_part_state[b].leader_epoch = con_part_state.leader_epoch

ValidLeaderMaximalISR ==
    \A b \in Brokers :
        \* if the leader is a non-stale leader
        IF IsNonStaleLeader(b)
        THEN 
              \* if it doesn't have a pending AP Req then: maximal ISR = ISR
              /\ IF ~PendingAlterPartitionResponse(b)
                 THEN replica_part_state[b].maximal_isr = replica_part_state[b].isr
                 ELSE TRUE
              \* the leader maximal ISR must be a superset of the controller ISR 
              /\ \A b1 \in con_part_state.isr :
                    b1 \in replica_part_state[b].maximal_isr
        ELSE TRUE

\* INV: LeaderHasCompleteCommittedLog
\* The replica selected as leader by the controller must have
\* the entire acknowledged log else this is data loss.
LeaderHasCompleteCommittedLog ==
    \/ con_part_state.leader = NoLeader
    \/ /\ con_part_state.leader # NoLeader
       /\ \A v \in DOMAIN inv_acked :
            \/ inv_acked[v] \in { Nil, FALSE } \* not committed
            \/ /\ inv_acked[v] = TRUE          \* is committed
               /\ \E offset \in DOMAIN replica_part_data[con_part_state.leader].log :
                    replica_part_data[con_part_state.leader].log[offset].value = v

\* INV: NoPartitionLogDivergence
\* The partition log on the leader must be consistent with
\* every follower (up to the HWM per replica).
NoPartitionLogDivergence == 
    \A offset \in 1..Cardinality(Values) :
        ~\E b1, b2 \in Brokers :
            /\ replica_part_data[b1].leo >= offset
            /\ replica_part_data[b2].leo >= offset
            /\ replica_part_data[b1].hwm >= offset
            /\ replica_part_data[b2].hwm >= offset
            /\ replica_part_data[b1].log[offset].value # replica_part_data[b2].log[offset].value

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
    \A v \in DOMAIN inv_acked :
        \/ inv_acked[v] \in { Nil, FALSE }
        \/ /\ inv_acked[v] = TRUE
           /\ \E b \in Brokers :
               \E offset \in DOMAIN replica_part_data[b].log :
                   replica_part_data[b].log[offset].value = v

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
                /\ offset \in DOMAIN replica_part_data[b].log
                /\ replica_part_data[b].log[offset] = inv_consumed[offset]
        ELSE TRUE

\* Not actually an invariant as the HWM is not monotonic on any
\* given replica. The "true" high watermark is monotonic but
\* is not recorded anywhere, it is implicit.    
HighWatermarkIsMonotonic ==
    \A b \in Brokers :
        replica_part_data[b].hwm >= inv_hwm[b]
        

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
            /\ con_broker_state[b].status = UNFENCED

\* LIVENESS: EventuallyUnfenced
\* Eventually, a broker that is fenced becomes unfenced.
EventuallyUnfenced ==
    \A b \in Brokers :
        con_broker_state[b].status = FENCED ~>
            con_broker_state[b].status = UNFENCED

\* LIVENESS: AlterPartitionEpochEventuallyReachedOrZero
\* Eventually, a replica that has sent an AlterPartition request
\* reaches the expected partition epoch, or the request is rejected.
AlterPartitionEpochEventuallyReachedOrZero ==
    []<>(\A b \in Brokers :
        replica_pending_ap_epoch[b] > 0 ~> 
            \/ replica_pending_ap_epoch[b] = replica_part_state[b].partition_epoch
            \/ replica_pending_ap_epoch[b] = 0)

\* LIVENESS: EventuallyMetadataConverges
\* Eventually, each broker converges on the same metadata as the controller.
EventuallyMetadataConverges ==
    []<>(\A b \in Brokers : 
            /\ replica_part_state[b].isr = con_part_state.isr
            /\ replica_part_state[b].leader = con_part_state.leader
            /\ replica_part_state[b].leader_epoch = con_part_state.leader_epoch
            /\ replica_part_state[b].partition_epoch = con_part_state.partition_epoch)

\* LIVENESS: EventuallyWriteIsAcceptedOrRejected
\* A produce request will eventually be positively or negatively acknowledged
EventuallyWriteIsAcceptedOrRejected ==
    \A v \in Values :
        v \in DOMAIN inv_acked ~> /\ v \in DOMAIN inv_acked
                                  /\ inv_acked[v] \in {FALSE, TRUE}

\* LIVENESS: EventuallyAcknowledgedValueFullyReplicated
\* A record that gets positively acknowledged eventually becomes
\* fully replicated.
EventuallyAcknowledgedValueFullyReplicated ==
    \A v \in Values :
        <>[](/\ v \in DOMAIN inv_acked
             /\ inv_acked[v] = TRUE
             /\ \A b \in Brokers : \E offset \in DOMAIN replica_part_data[b].log :
                                      replica_part_data[b].log[offset].value = v)


\* ==================================================================
\*              INIT and NEXT
\* ==================================================================

\* The cluster starts in an already established state.
\* When InitIsrSize < BrokerCount then a subset of broker start outside 
\* of the ISR with a stale leader_epoch. This allows us to explore
\* more state space.

Init ==
    LET init_isr   == CHOOSE isr \in SUBSET Brokers :
                        /\ 1 \in isr \* we always start with broker 1 as the leader
                        /\ Cardinality(isr) = InitIsrSize
        \* if the inital ISR is < RF then we make the leader/partition_epoch = 2 
        \* to simulate a change having already occurred.
        ldr_epoch  == IF init_isr = Brokers THEN 1 ELSE 2
        part_epoch == ldr_epoch
        metadata_log  == <<>>
        metadata_log1 == Append(metadata_log, 
                                  [type            |-> PartitionChangeRecord,
                                   leader          |-> 1,
                                   isr             |-> init_isr,
                                   leader_epoch    |-> ldr_epoch,
                                   partition_epoch |-> part_epoch])                                  
    IN 
        /\ con_unfenced = init_isr
        /\ con_broker_state = [b \in Brokers |->
                \* use the broker_id integer as a value for multiple fields
                \* as it serves as a good value at this stage. 
                [status              |-> IF b \in init_isr
                                         THEN UNFENCED ELSE FENCED,
                 broker_epoch        |-> b, 
                 incarnation_id      |-> b]]
        /\ con_metadata_log = metadata_log1
        /\ con_part_state = 
                [isr             |-> init_isr,
                 leader          |-> 1, \* broker 1
                 leader_epoch    |-> ldr_epoch,
                 partition_epoch |-> part_epoch] 
        /\ broker_state = [b \in Brokers |-> 
                [status            |-> RUNNING,
                 broker_epoch      |-> b,
                 incarnation_id    |-> b,
                 registered        |-> TRUE]]
        /\ broker_metadata_log = [b \in Brokers |-> IF b \in init_isr
                                                    THEN metadata_log1
                                                    ELSE metadata_log]
        /\ replica_status = [b \in Brokers |-> IF b = 1 THEN Leader ELSE Follower]
        /\ replica_part_state = [b \in Brokers |-> 
                                    [isr          |-> IF b \in init_isr 
                                                      THEN init_isr ELSE Brokers,
                                     maximal_isr  |-> IF b \in init_isr 
                                                      THEN init_isr ELSE Brokers,
                                     leader       |-> 1, \* broker 1
                                     \* if the "initial ISR = Brokers" then all brokers
                                     \* have the same leader_epoch, else, the brokers in the
                                     \* ISR have the up-to-date epoch and the rest have a stale one.
                                     leader_epoch |-> CASE init_isr = Brokers -> 1 
                                                        [] b \in init_isr -> 2
                                                        [] OTHER -> 1,
                                     partition_epoch |-> CASE init_isr = Brokers -> 1 
                                                           [] b \in init_isr -> 2
                                                           [] OTHER -> 1]]
        \* the partition log on each replica starts empty
        /\ replica_part_data = [b \in Brokers |->
                                    [log                |-> <<>>,
                                     hwm                |-> 0,
                                     leo                |-> 0,
                                     epoch_start_offset |-> 0]]
        /\ replica_fetch_state = [b \in Brokers |-> 
                                    [fetch_offset     |-> 1,
                                     pending_response |-> FALSE]]
        /\ replica_replica_state = [b \in Brokers |->
                                        [b1 \in Brokers |-> BlankReplicaState]]
        /\ replica_pending_ap_epoch = [b \in Brokers |-> 0]
        /\ aux_ctrs = [incarn_ctr           |-> ReplicationFactor + 1,
                       clean_shutdown_ctr   |-> 0,
                       unclean_shutdown_ctr |-> 0,
                       fence_stale_ctr      |-> 0,
                       alter_part_ctr       |-> 0]
        /\ inv_acked = <<>>
        /\ inv_hwm = [b \in Brokers |-> 0]
        /\ inv_consumed = <<>>
        /\ messages = <<>>

Next ==
    \* broker actions
    \/ BrokerStart
    \/ ReceiveBrokerRegResponse
    \/ ReceiveMetadataPartitionChangeRecords
    \/ DelayedTruncateAsFollower
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
    
Liveness ==
    WF_vars(Next)

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Liveness    
=============================================================================
