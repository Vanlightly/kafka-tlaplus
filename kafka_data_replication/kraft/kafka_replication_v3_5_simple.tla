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
- The controller can fence and unfence arbitrarily (simulating
  heartbeats or lack thereof).
- The controlled shutdown sequence has been removed.
- Active broker set on the controller not modeled as the
  controlled shutdown sequence is omitted.

NOTES:
- Offsets are 1-based, not 0-based like in the implementation. This is due to
  TLA+ sequences being 1-based.
- The Log End Offset (LEO) and High Watermark (HWM) are exclusive. For example,
  if the last offset in the log is 5, then the LEO is 6. If the highest committed
  offset is 3 then the HWM is 4. Because offsets are 1-based, an empty log will have 
  an LEO and HWM of 1.  
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
- No consumed data is lost and consumed data remains consistent with the leader log.
- No divergence between the leader log and the history of consumed records.
- No divergence between the leader log and follower logs up to the HWM.
- No divergence between the controller metadata log and broker metadata logs.

Liveness checks (assuming any failures are transitory):
- STARTING brokers eventually reach RUNNING
- FENCED brokers eventually become UNFENCED.
- Eventually, all brokers converge on controller metadata state.
- Eventually a write will be acknowledged (positively or negatively).
- Eventually a positively acknowledged write will be fully replicated.

Jump to the bottom of the spec for the Next state formula which lists all
the actions.
*)

CONSTANTS ReplicationFactor, \* the number of replicas (and brokers).
          Values,            \* the producer data values that can be written
          MinISR,            \* the min.insync.replicas
          InitIsrSize        \* the initial ISR size. When InitIsrSize < ReplicationFactor
                             \* a corresponding number of brokers start outside the ISR.
                             \* This allows us to explore some scenarios that are too costly
                             \* to reach with brute-force model checking.
\* state space limits
CONSTANTS CleanShutdownLimit,       \* limits the number of clean shutdowns
          UncleanShutdownLimit,     \* limits the number of unclean shutdowns
          FenceBrokerLimit,         \* limits the number of times the controller arbitrarily fences a broker
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
          Follower
          
\* Requests and responses
CONSTANTS RegisterBrokerRequest,
          RegisterBrokerResponse,
          AlterPartitionRequest,
          AlterPartitionResponse,
          FetchRequest,
          FetchResponse

\* metadata log entry types
CONSTANTS PartitionChangeRecord

\* errors
CONSTANTS IneligibleReplica,  \* An AlterPartition error code - a proposed ISR member is invalid.
          FencedEpoch,        \* An AlterPartition/Fetch error code - epoch of a request was stale.
          UnknownLeaderEpoch, \* A fetch error code - when a stale leader receives a fetch.
          NotLeaderOrFollower \* A fetch error code - when a non-leader receives a fetch.

\* other
CONSTANTS Controller,        \* used to denote the destination or source of a message is the controller
          NoLeader,          \* a constant value to represent the partition has no leader
          Nil                \* a constant used to denote 'nothing' or 'not set'

ASSUME InitIsrSize <= ReplicationFactor
ASSUME MinISR <= ReplicationFactor
ASSUME CleanShutdownLimit \in Nat
ASSUME UncleanShutdownLimit \in Nat
ASSUME FenceBrokerLimit \in Nat
ASSUME AlterPartitionLimit \in Nat

\* Controller state
VARIABLES con_unfenced,         \* the set of brokers which are in the state UNFENCED.
          con_broker_reg,       \* a map of broker id to broker registration on the controller.
          con_part_state,       \* the current state of the partition (leader, leader_epoch, isr).
          con_metadata_log      \* the KRaft metadata log.
          
\* Broker state not concerned with partitions.
\* Each variable is a map of [broker_id -> some state of that broker].          
VARIABLES broker_state,         \* state of each broker, such as status (RUNNING, STARTING etc)
          broker_fetch_session, \* the fetch sessions for each broker pairing
          broker_fetchers,      \* the fetchers of each broker
          broker_metadata_log   \* the strongly eventually consistent copy of the 
                                \* KRaft metadata log on each broker.

\* Broker-side replica and partition state
\* Each variable is a map of [broker_id -> some state of the replica or partition on that broker].          
VARIABLES replica_status,
          replica_part_state,      \* the partition metadata state on each replica.
          replica_part_data,       \* the actual partition log data on each replica.
          replica_replica_state,   \* a map (used by the leader) to track the state of follower replicas
          replica_pending_ap       \* info related to a pending AlterPartition request

\* Message passing state
VARIABLES messages  \* a collection used by the message passing logic.

\* Auxilliary variables (not part of the protocol)           
VARIABLES aux_broker_epoch, \* Because we omit some metadata records, broker epochs cannot be based on metadata offsets.
          aux_session,      \* Used for generating unique fetch session ids
          aux_ctrs          \* Some counters used to limit the number of times certain actions can occur, to limit the state space.

\* Auxilliary variables for verifying invariants (not part of the protocol)
VARIABLES inv_acked,     \* Tracks whether a producer message has been acknowledged or not.
                         \* This is required to detect data loss.
          inv_true_hwm,  \* Tracks the true HWM
          inv_consumed   \* Tracks the records consumed to detect divergence.

\* Variable lists
con_broker_vars == << con_unfenced, con_broker_reg >>
con_vars == << con_metadata_log,  con_broker_vars, con_part_state >>
broker_vars == << broker_state, broker_fetch_session, 
                  broker_fetchers, broker_metadata_log >>
replica_vars == << replica_status, replica_part_state, replica_part_data,
                   replica_replica_state, replica_pending_ap >>
inv_vars == << inv_acked, inv_true_hwm, inv_consumed >>
aux_vars == << aux_broker_epoch, aux_session, aux_ctrs >>    
vars == << con_vars, broker_vars, replica_vars, messages, inv_vars, aux_vars >>
view == << con_vars, broker_vars, replica_vars, messages, inv_vars >>

\* The set of brokers. Note that broker ids and replica
\* ids are the same, and so Brokers ids are used within replica logic
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

FetchSession ==
    [\* the unique session id of this session
     id: Nat,
     \* the current fetch epoch
     epoch: Nat]

PartitionFetchState ==
    [fetch_offset: Nat,
     last_fetched_epoch: Nat]

BrokerFetcher ==
    [\* the partition that should be fetched for (only modeling one partition)
     partition: PartitionFetchState \union {Nil},
     \* TRUE when the fetcher is waiting for a fetch resonse
     pending_response: BOOLEAN]

ReplicaState ==
    [leo: Nat \union {Nil}, 
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

PartitionDataType ==
    [log: PartitionLog,
     hwm: Nat,
     leo: Nat,
     epoch_start_offset: Nat \union {Nil}]
     
StateSpaceLimitCtrs ==
    [incarn_ctr: Nat,
     clean_shutdown_ctr: Nat,
     unclean_shutdown_ctr: Nat,
     fence_broker_ctr: Nat,
     alter_part_ctr: Nat]

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
     metadata_offset: Nat, \* spec-only (not in implementation)
     dest: Nat,
     source: {Controller}]
     
AlterPartitionRequestType ==
    [type: {AlterPartitionRequest},
     isr: SUBSET Brokers,
     isr_and_epochs: [SUBSET Brokers -> Nat],
     leader: Brokers,
     leader_epoch: Nat,
     partition_epoch: Nat,
     broker_epoch: Nat,
     source: Brokers,
     dest: {Controller}]
     
AlterPartitionResponseTypeSuccess ==
    [type: {AlterPartitionResponse},
     error: {Nil},   
     isr: SUBSET Brokers,
     leader: Brokers,
     leader_epoch: Nat,
     partition_epoch: Nat,
     request: {AlterPartitionRequestType},
     dest: {Controller},
     source: Brokers]     
     
AlterPartitionResponseTypeFailure ==
    [type: {AlterPartitionResponse},
     error: {FencedEpoch, IneligibleReplica},   
     request: {AlterPartitionRequestType},
     dest: {Controller},
     source: Brokers]     

FetchRequestType ==
    [type: {FetchRequest},
     broker_epoch: Nat,
     fetch_session_id: Nat,
     fetch_epoch: Nat,
     \* only one partition modeled
     partition: [leader_epoch: Nat,
                 fetch_offset: Nat,
                 last_fetched_epoch: Nat],
     dest: Brokers,
     source: Brokers]
     
FetchResponseType ==
    [type: {FetchResponse},
     fetch_session_id: Nat,
     \* only one partition modeled
     partition: [error: {Nil, NotLeaderOrFollower, UnknownLeaderEpoch, FencedEpoch},
                 leader_epoch: Nat,
                 fetch_offset: Nat,
                 hwm: Nat,
                 diverging_epoch: [epoch: Nat,
                                   end_offset: Nat] \union {Nil},
                 records: PartitionRecord],
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

\* ======================================================================
\* ------------ Helpers -------------------------------------------------

LogOffsets(b) ==
    DOMAIN replica_part_data[b].log

LogOf(b) ==
    replica_part_data[b].log
    
LogEntry(b, offset) ==
    replica_part_data[b].log[offset]
    
LogEntryEpoch(b, offset) ==
    replica_part_data[b].log[offset].epoch
    
LeoOf(b) ==
    replica_part_data[b].leo
    
HwmOf(b) ==
    replica_part_data[b].hwm

PartitionState(b) ==
    replica_part_state[b]

PartitionData(b) ==
    replica_part_data[b]
    
LeaderFetchSessionId(b1, b2) ==
    broker_fetch_session[b1][b2].recv.id
    
FollowerFetchSessionId(b1, b2) ==
    broker_fetch_session[b1][b2].send.id
    
LeaderFetchEpoch(b1, b2) ==
    broker_fetch_session[b1][b2].recv.epoch  
    
FollowerFetchEpoch(b1, b2) ==
    broker_fetch_session[b1][b2].send.epoch    
    
LeaderFetchSessionMatch(b1, b2, session_id, fetch_epoch) ==
    /\ broker_fetch_session[b1][b2].recv # Nil
    /\ broker_fetch_session[b1][b2].recv.id = session_id
    /\ broker_fetch_session[b1][b2].recv.epoch = fetch_epoch
    
FollowerFetchSessionMatch(b1, b2, session_id) ==
    /\ broker_fetch_session[b1][b2].send # Nil
    /\ broker_fetch_session[b1][b2].send.id = session_id

IncrementFollowerFetchEpoch(b1, b2) ==
    broker_fetch_session' = [broker_fetch_session EXCEPT ![b1][b2].send.epoch = @ + 1]
    
IncrementLeaderFetchEpoch(b1, b2) ==
    broker_fetch_session' = [broker_fetch_session EXCEPT ![b1][b2].recv.epoch = @ + 1]    

Fetcher(b1, b2) ==
    broker_fetchers[b1][b2]

BlankFetchSession ==
    [id |-> 0, epoch |-> 0]    
     
BlankFetchState ==
    [partition        |-> Nil,
     pending_response |-> FALSE]     

BlankReplicaState ==
    [leo          |-> Nil,
     broker_epoch |-> 0]

\* A replica resets its peer replica state when it changes role.
\* If it has become a leader then it sets its own replica state as this
\* spec uses that when computing the HWM advancement.
ResetReplicaState(b, is_leader) ==
    replica_replica_state' = [replica_replica_state EXCEPT ![b] = 
                                [b1 \in Brokers |-> 
                                    IF b1 = b /\ is_leader
                                    THEN [leo |-> LeoOf(b),
                                          broker_epoch |-> broker_state[b].broker_epoch]
                                    ELSE BlankReplicaState]]

\* replica_pending_ap is used by the spec to know when it is pending 
\* an AP request. If the epoch is higher than the current partition epoch
\* then it is pending a response.
ResetPendingAlterPartition(b) ==
    replica_pending_ap' = [replica_pending_ap EXCEPT ![b] = 
                            [epoch   |-> 0,
                             request |-> Nil]]

\* ==========================================================================
\* -- Anti-cycle checks (for liveness properties and state space limiting) --
\*
\* To avoid cycles such as infinite fetch request/responses, the spec limits
\* fetch requests to when they are required to make progress.
\* Generally speaking, you can ignore this.

__FetchMakesProgress(b) ==
    LET leader == PartitionState(b).leader
    IN \* they are on the same leader epoch (needed for preventing infinite fetch cycles)
       /\ PartitionState(b).leader_epoch = PartitionState(leader).leader_epoch
       \* one of the following is true:
       /\ \* leader has records to get
          \/ LeoOf(b) < LeoOf(leader)
          \* leader has hwm to get                  
          \/ HwmOf(b) < HwmOf(leader)        
          \* leader hasn't received any fetch request of follower
          \/ replica_replica_state[leader][b].leo = Nil
          \* leader doesn't know current leo of follower   
          \/ /\ replica_replica_state[leader][b].leo # Nil   
             /\ replica_replica_state[leader][b].leo < LeoOf(b)

__MetadataCaughtUp(b) ==
    Len(broker_metadata_log[b]) = Len(con_metadata_log)

\* ======================================================================
\* ------------ Key functions -------------------------------------------
\* These functions may be used in multiple places.

\*----------------------------------------------------
\* FUNCTION: HighestCommitted
\*
\* Find the highest (contiguous) offset that has been committed
\* (replicated to the leader's maximal ISR).

IsCommitted(b, maximal_isr, replica_state, offset) ==
    \A b1 \in maximal_isr :
        /\ replica_state[b1].leo # Nil
        /\ replica_state[b1].leo > offset

HighestCommitted(b, maximal_isr, replica_state) ==
    CASE LeoOf(b) = 1 ->
            0
      [] \E offset \in 1..LeoOf(b)-1:
            IsCommitted(b, maximal_isr, replica_state, offset) ->
                \* This is a TLA+ way of saying choose the highest offset which is committed.
                \* Basically, choose an offset such that it is committed and no other offset
                \* exists that is also committed and is higher.
                CHOOSE offset \in 1..LeoOf(b)-1 :
                    /\ IsCommitted(b, maximal_isr, replica_state, offset)
                    /\ ~\E offset1 \in 1..LeoOf(b)-1 :
                        /\ IsCommitted(b, maximal_isr, replica_state, offset1)
                        /\ offset1 > offset
      [] OTHER -> 0

\*-------------------------------------------------------------
\* FUNCTION: MaybeAdvanceHighWatermark
\*
\* If the new HWM is higher then, advance the HWM and record it in
\* related invariant variables.  

MaybeAdvanceHighWatermark(b, old_hwm, new_hwm, ack_type) ==
    IF new_hwm > old_hwm
    THEN /\ replica_part_data' = [replica_part_data EXCEPT ![b].hwm = new_hwm]
         \* record which values got acked (positively or negatively) to producers
         /\ inv_acked' = [v \in DOMAIN inv_acked |->
                                 IF /\ inv_acked[v] = Nil
                                    /\ \E offset \in old_hwm..new_hwm-1 :
                                       LogEntry(b, offset).value = v
                                 THEN ack_type
                                 ELSE inv_acked[v]]
         \* update the true high watermark
         /\ inv_true_hwm' = IF new_hwm > inv_true_hwm
                            THEN new_hwm ELSE inv_true_hwm
         \* If the "real" HWM has advanced, record which records
         \* got consumed by consumers.
         /\ inv_consumed' = IF new_hwm > inv_true_hwm
                            THEN inv_consumed \o SubSeq(LogOf(b), inv_true_hwm, new_hwm-1)
                            ELSE inv_consumed
    ELSE UNCHANGED << replica_part_data, inv_vars >>

\*-----------------------------------------------------------
\* FUNCTION: MaybeFailPendingWrites
\*
\* If the ISR is now below MinISR or the replica lost leadership
\* then negatively acknowledge all unacknowledged and 
\* uncommitted records.

FailPendingWrites(b) ==
    inv_acked' = [v \in DOMAIN inv_acked
                    |-> IF /\ inv_acked[v] = Nil
                           /\ \E offset \in HwmOf(b)..LeoOf(b)-1 : LogEntry(b, offset).value = v
                        THEN FALSE \* neg ack
                        ELSE inv_acked[v]]

MaybeFailPendingWrites(b, part_state) ==
    IF /\ HwmOf(b) < LeoOf(b)
       /\ \/ Cardinality(part_state.isr) < MinISR
          \/ b # part_state.leader
    THEN FailPendingWrites(b)
    ELSE UNCHANGED inv_acked

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
\* that have been replicated to all members in the new ISR (in the
\* case of shrinkage). If the ISR has shrunk below MinISR then any 
\* unacknowledged records up to the new high watermark should be
\* negatively acknowledged (NotEnoughReplicasAfterAppend).
\*
\* Note that the calculated new high watermark may be lower than 
\* the old high watermark as after a leader change, the leader may 
\* still not have enough information on its followers to know to 
\* compute the new high watermark.

MaybeUpdateHwmOnPartitionChange(b, part_state) ==
    LET old_hwm == HwmOf(b)
        new_hwm == HighestCommitted(b, part_state.maximal_isr,
                                    replica_replica_state[b]) + 1
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
    UNCHANGED << con_part_state, con_metadata_log >>

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

\*--------------------------------------------------------------
\* FUNCTION: MaybeUpdatePartitionState, MaybeRemoveBrokerFromISR

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

\*--------------------------------------------------------------
\* FUNCTIONS: HandleBrokerFenced, HandleBrokerUnfenced

HandleBrokerFenced(b) ==
    LET new_isr      == MaybeRemoveBrokerFromISR(con_part_state.isr, b)
        new_unfenced == con_unfenced \ {b}
    IN /\ MaybeUpdatePartitionState(new_isr, new_unfenced)
       /\ con_unfenced' = new_unfenced

HandleBrokerUnfenced(b) ==
    LET new_isr      == con_part_state.isr \* unfencing doesn't change the ISR
        new_unfenced == con_unfenced \union {b}
    IN \* if there is no leader the controller can choose one from the ISR.
       /\ IF con_part_state.leader = NoLeader 
          THEN MaybeUpdatePartitionState(new_isr, new_unfenced)
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
          /\ PartitionState(b).leader_epoch = req_epoch
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
                                   /\ PartitionState(b).leader_epoch > req_epoch
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

\* ==================================================================
\*              ACTIONS
\* ==================================================================

(* ---------------------------------------------------------------
   ACTION: BrokerStart

   A stopped broker starts-up in the STARTING status and sends a 
   new broker registration request to the controller with a new 
   incarnation id.
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
        /\ replica_replica_state' = [replica_replica_state EXCEPT ![b] =
                                        [b1 \in Brokers |-> BlankReplicaState]]
        /\ ResetPendingAlterPartition(b)
        /\ SendBrokerRegistration(b)
        /\ UNCHANGED << con_vars, broker_fetch_session, broker_fetchers, 
                        broker_metadata_log, replica_part_state, replica_part_data,
                        inv_vars, aux_broker_epoch, aux_session >>        

(* ---------------------------------------------------------------
   ACTION: ReceiveBrokerRegRequest

   The controller receives a RegisterBrokerRequest and
   only accepts it if:
   - there is no registration record (not modeled)
   - the broker is FENCED
   - the broker is not FENCED and the incarnation id matches
     the existing registration.
   
   The controller assigns the broker an epoch based on the last 
   offset in the metadata log.
   
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
                /\ con_broker_reg' = [con_broker_reg EXCEPT ![b] =
                                            [status              |-> UNFENCED,
                                             broker_epoch        |-> broker_epoch,
                                             incarnation_id      |-> m.incarnation_id]]
                /\ HandleBrokerUnfenced(b) 
                /\ Reply(m, 
                        [type            |-> RegisterBrokerResponse,
                         broker_epoch    |-> broker_epoch,
                         metadata_offset |-> Len(con_metadata_log), \* spec only field (see ReceiveBrokerRegResponse)
                         dest            |-> b,
                         source          |-> Controller])
                /\ aux_broker_epoch' = aux_broker_epoch + 1 \* used instead of metadata write offset
                /\ UNCHANGED << broker_vars, replica_vars, inv_vars, aux_ctrs, aux_session >>

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
    broker. This is simulated here by catching up to the controller
    metadata log at the time of registration but minus one record. 
    By leaving the last record unreplicated, we leave it to the 
    ReceiveMetadataUpdate action to correctly initialize the replica
    based on the next metadata record and so avoid needing to 
    include that logic in this action.
----------------------------------------------------------------*)

__EnsureMetadataCaughtUp(b, m) ==
    LET log == IF m.metadata_offset <= 1
               THEN <<>>
               ELSE SubSeq(con_metadata_log, 1, m.metadata_offset-1)
    IN /\ broker_metadata_log' = [broker_metadata_log EXCEPT ![b] = log]
       /\ replica_part_state' = [replica_part_state EXCEPT ![b] = 
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
        /\ __EnsureMetadataCaughtUp(m.dest, m)
        /\ Discard(m)
        /\ UNCHANGED << con_vars, broker_fetch_session, broker_fetchers,  
                        replica_status, replica_part_data, replica_replica_state,
                        replica_pending_ap, inv_vars, aux_vars >>

(*--------------------------------------------------------------------
  ACTION: UnfenceBroker

  The controller unfences a fenced broker. In the implementation
  this would happen due to a heartbeat. This spec simply
  allows this to occur at any time to a fenced broker.

  An unfenced broker is not added to an ISR but can be made
  leader of a partition which has no leader and it is the sole
  member of the ISR (as the ISR cannot shrink to empty).
  
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
        /\ UNCHANGED << broker_vars, replica_vars, messages, inv_vars, 
                        aux_vars >>

(*--------------------------------------------------------------------
  ACTION: FenceBroker

  The controller fences an unfenced broker. In the implementation
  this would happen due to a lack of heartbeats. This spec simply
  allows this to occur at any time to an unfenced broker.

  A fenced broker is removed from any leadership. Also it is removed
  from any ISRs though the ISR cannot drop below 1. This means
  we can have leader=NoLeader and ISR have a single member.
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
        /\ UNCHANGED << broker_vars, replica_vars, messages, inv_vars,
                        aux_broker_epoch, aux_session >>

(*-----------------------------------------------------------------------
  ACTION: ReceiveMetadataUpdate

  NOTE! This action contains a lot of logic.

  In this simplified spec, only PartitionChange records are added to the 
  metadata log and brokers receive metadata records one at a time. When a 
  broker receives a PartionChange metadata record it can take various 
  actions:
   - It may have become the partition leader and therefore records the
     start offset for this leader epoch (the LEO on becoming leader).
     It will remove the partition from any fetcher it is added to.
   - It may have become a follower and may perform the following:
        - Fetch sessions are established lazily in this spec. If the replica
          has no fetch session it will estbalish one with the leader. This
          spec models a simplified fetch session where a new session is
          simply manifested on both sides.
        - Adds the partition to the right fetcher and removes the partition
          from any other fetcher if it exists. 
        - The follower does not perform truncation, this spec implements
          the diverging epoch on fetch.
   - There may be no leader, so it simply waits for the next PartionChangeRecord.
   - Uncommitted pending writes may need to be negatively acknowledged:
       - if the replica has lost leadership
       - the ISR has shrunk below minISR.
-----------------------------------------------------------------------*)           

NewSession ==
    [id    |-> aux_session + 1,
     epoch |-> 1]

MaintainCurrentFetchSessions ==
    UNCHANGED << broker_fetch_session, aux_session >>
    
MaybeEstablishFetchSession(source, dest) ==
     IF broker_fetch_session[source][dest].send = Nil
     THEN \* broker_fetch_session is nested map of broker->broker sessions. Any pair of
          \* brokers have two sessions:
          \*    - b1.send -> b2.recv
          \*    - b2.send -> b1.recv 
          \* Rebuild the map, only updating the session of the source->dest broker
          \* which involves creating a new session on the source send and the dest recv:
          /\ broker_fetch_session' = [b \in Brokers |->
                                        \* If this is the leader-side broker, then set the cached
                                        \* session for receipt of expected fetch requests.
                                        CASE b = dest ->
                                                [b1 \in Brokers |->
                                                    [recv |-> IF b1 = source
                                                              THEN NewSession
                                                              ELSE broker_fetch_session[b][b1].recv,
                                                     send |-> broker_fetch_session[b][b1].send]]
                                          \* If this is the fetching broker, then set the new 
                                          \* session needed for sending fetch requests.
                                          [] b = source ->
                                                [b1 \in Brokers |->
                                                    [recv |-> broker_fetch_session[b][b1].recv,
                                                     send |-> IF b1 = dest
                                                              THEN NewSession
                                                              ELSE broker_fetch_session[b][b1].send]]
                                          \* else leave this broker's sessions unchanged
                                          [] OTHER -> broker_fetch_session[b]]
          /\ aux_session' = aux_session + 1 
    ELSE MaintainCurrentFetchSessions
    
\* Add the partition to the fetcher in the case that:
\*    - this is a new leader epoch.
\*    - the partition has not already been added.
\* Adding the partition to one fetcher removes it from another,
\* if it existed on another.
AddPartitionToFetcher(b, leader, leader_epoch) ==
    IF \/ leader_epoch > PartitionState(b).leader_epoch
       \/ broker_fetchers[b][leader].partition = Nil
    THEN LET add_partition == [fetch_offset       |-> LeoOf(b),
                               last_fetched_epoch |-> IF LogOf(b) = <<>> 
                                                      THEN 0
                                                      ELSE Last(LogOf(b)).epoch]
         IN 
            broker_fetchers' = [broker_fetchers EXCEPT ![b] =
                                    [b1 \in Brokers |->
                                        [partition |-> IF b1 = leader THEN add_partition ELSE Nil,
                                         pending_response |-> Fetcher(b, b1).pending_response]]]
    ELSE UNCHANGED << broker_fetchers >>


RemovePartitionFromFetchers(b) ==
    broker_fetchers' = [broker_fetchers EXCEPT ![b] =
                            [b1 \in Brokers |-> 
                                [partition        |-> Nil,
                                 pending_response |-> Fetcher(b, b1).pending_response]]]

NextMetadataRecord(index) ==
    con_metadata_log[index]

\* The replica remains leader, all it must do is conditionally advance the HWM.
RemainLeader(b, new_part_state) ==
    /\ MaybeUpdateHwmOnPartitionChange(b, new_part_state)
    /\ IF new_part_state.partition_epoch >= replica_pending_ap[b].epoch
       THEN ResetPendingAlterPartition(b)
       ELSE UNCHANGED replica_pending_ap
    /\ MaintainCurrentFetchSessions
    /\ UNCHANGED << replica_status, replica_replica_state, 
                    broker_fetchers>>

\* The replica has become a leader in a new leader epoch. This includes
\* a leader being reelected in a new leader epoch. So it must set its
\* Epoch Start Offset, reset any peer replica state and remove the
\* partition from any fetcher if it is added.   
BecomeLeader(b) ==
    /\ replica_status' = [replica_status EXCEPT ![b] = Leader]
    /\ replica_part_data' = [replica_part_data EXCEPT ![b].epoch_start_offset = LeoOf(b)]
    /\ ResetReplicaState(b, TRUE)
    /\ ResetPendingAlterPartition(b)
    /\ MaintainCurrentFetchSessions
    /\ RemovePartitionFromFetchers(b)
    /\ UNCHANGED << inv_vars >>

\* The replica has become a follower and adds the partition to the right fetcher
\* setting its fetch offset to its current LEO. If log truncation is required,
\* it will occur on its first fetch response.        
BecomeFollower(b, new_part_state) ==
    /\ MaybeFailPendingWrites(b, new_part_state)
    /\ replica_status' = [replica_status EXCEPT ![b] = Follower]
    /\ ResetReplicaState(b, FALSE)
    /\ MaybeEstablishFetchSession(b, new_part_state.leader)
    /\ AddPartitionToFetcher(b, new_part_state.leader, new_part_state.leader_epoch)
    /\ ResetPendingAlterPartition(b)
    /\ UNCHANGED << replica_part_data, inv_true_hwm, inv_consumed >>
    
\* The replica learns there is no leader, so waits in limbo until
\* it gets new information.    
WaitForLeaderChange(b, new_part_state) ==
    /\ MaybeFailPendingWrites(b, new_part_state)
    /\ replica_status' = [replica_status EXCEPT ![b] = Nil]
    /\ MaintainCurrentFetchSessions
    /\ RemovePartitionFromFetchers(b)
    /\ ResetPendingAlterPartition(b)
    /\ UNCHANGED << replica_part_data, replica_replica_state, 
                    inv_true_hwm, inv_consumed >>

MetadataNoOp ==
    /\ MaintainCurrentFetchSessions
    /\ UNCHANGED << replica_vars, broker_fetchers, inv_vars >>

ReceiveMetadataUpdate ==
    \E b \in Brokers :
        LET curr_md_offset == Len(broker_metadata_log[b])
            pc_record      == NextMetadataRecord(curr_md_offset + 1)
            new_part_state == [isr             |-> pc_record.isr,
                               maximal_isr     |-> pc_record.isr,
                               leader          |-> pc_record.leader,
                               leader_epoch    |-> pc_record.leader_epoch,
                               partition_epoch |-> pc_record.partition_epoch]
        IN
            \* enabling conditions
            /\ broker_state[b].status \notin {OFFLINE_CLEAN, OFFLINE_DIRTY}
            /\ broker_state[b].registered = TRUE
            /\ curr_md_offset < Len(con_metadata_log) \* there are metadata records to receive
            \* state mutations
            /\ broker_metadata_log' = [broker_metadata_log EXCEPT ![b] = Append(@, pc_record)]
               \* If the last PartitionChangeRecord has a higher partition epoch, then update 
               \* the local partition state and possibly become a leader or follower.
               \* The partition epoch will not be lower if the change is the result of a completed
               \* PartitionChange request and the response was already processed.
            /\ IF new_part_state.partition_epoch > PartitionState(b).partition_epoch
               THEN
                    /\ replica_part_state' = [replica_part_state EXCEPT ![b] = new_part_state]
                    /\ CASE 
                         \* CASE --- Leader reelected -------------------------------
                            /\ PartitionState(b).leader = b
                            /\ pc_record.leader = b -> 
                                IF PartitionState(b).leader_epoch = new_part_state.leader_epoch
                                THEN RemainLeader(b, new_part_state)
                                ELSE BecomeLeader(b)
                         \* CASE --- Follower elected as leader----------------------
                         [] /\ PartitionState(b).leader # b
                            /\ pc_record.leader = b ->
                                BecomeLeader(b)
                         \* CASE --- Chosen as a follower ---------------------------
                         [] /\ pc_record.leader # NoLeader ->
                                BecomeFollower(b, new_part_state)
                         \* CASE --- No leader chosen---- ---------------------------
                         [] OTHER ->
                                WaitForLeaderChange(b, new_part_state)
                         \* END CASE
               ELSE MetadataNoOp
            /\ UNCHANGED << con_vars, broker_state, messages, aux_broker_epoch, aux_ctrs >>

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
  
  The leader eagerly applies the maximal ISR. The maximal ISR is the
  union of the proposed ISR with the current ISR in order to maintain
  the invariant that the leader ISR must be a superset of the controller
  ISR. This invariant is required to avoid data loss where the 
  controller selects a leader outside of the current leader's maximal ISR.
--------------------------------------------------------------------------*)  

\* Create a map of broker id -> broker epoch. Set all current ISR
\* member epochs to 0 (-1 in the implementation), only set the
\* broker epoch of new members and the leader.
IsrAndEpochs(b, proposed_isr, curr_isr) ==
    [b1 \in proposed_isr 
        |-> CASE \* --- CASE member is the leader ------------------------
                 b = b1 -> broker_state[b].broker_epoch
              \* --- CASE member is in the current ISR (i.e. not added) --
              [] b1 \in curr_isr -> 0
              \* --- CASE member is added --------------------------------
              [] OTHER -> replica_replica_state[b][b1].broker_epoch]
              \* END CASE

\* TRUE if we are expecting a response with a higher partition epoch
PendingAlterPartitionResponse(b) ==
    replica_pending_ap[b].epoch > PartitionState(b).partition_epoch

\* For a follower to be caught up:
FollowerIsCaughtUp(b, follower, timed_out_followers) ==
    \* The leader must have received a fetch request from the follower
    /\ replica_replica_state[b][follower].leo # Nil
    \* The follower must have reached the high watermark
    /\ replica_replica_state[b][follower].leo >= HwmOf(b)
    \* The follower must have reached the epoch start offset
    /\ replica_replica_state[b][follower].leo >= PartitionData(b).epoch_start_offset
    \* The follower cannot have timed out
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
            /\ LET curr_isr     == PartitionState(b).isr
                   proposed_isr == { b1 \in Brokers : \/ b1 = b 
                                                      \/ FollowerIsCaughtUp(b, b1, timed_out_followers) }
                   ap_request   == [type            |-> AlterPartitionRequest,
                                    isr             |-> proposed_isr,
                                    isr_and_epochs  |-> IsrAndEpochs(b, proposed_isr, curr_isr),
                                    leader          |-> b,
                                    leader_epoch    |-> PartitionState(b).leader_epoch,
                                    partition_epoch |-> PartitionState(b).partition_epoch,
                                    broker_epoch    |-> broker_state[b].broker_epoch,
                                    source          |-> b,
                                    dest            |-> Controller]
               IN 
                  /\ proposed_isr # curr_isr
                  \* state mutations
                  /\ Send(ap_request)
                  /\ replica_part_state' = [replica_part_state EXCEPT ![b].maximal_isr = 
                                               proposed_isr \union curr_isr]
                  /\ replica_pending_ap' = [replica_pending_ap EXCEPT ![b] = 
                                                    [epoch   |-> PartitionState(b).partition_epoch + 1,
                                                     request |-> ap_request]]
                  /\ aux_ctrs' = [aux_ctrs EXCEPT !.alter_part_ctr = @ + 1]
                  /\ UNCHANGED << con_vars, broker_vars, replica_part_data, 
                                  replica_replica_state, replica_status, inv_vars, 
                                  aux_broker_epoch, aux_session >>

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
---------------------------------------------------------------------------*)

IsEligibleBroker(b, broker_epoch) ==
    /\ con_broker_reg[b].status = UNFENCED
    /\ \/ broker_epoch = 0
       \/ con_broker_reg[b].broker_epoch = broker_epoch
    
EligibleIsr(m) ==
    \A b \in DOMAIN m.isr_and_epochs :
        IsEligibleBroker(b, m.isr_and_epochs[b])    

ValidateRequest(b, m) ==
    IF /\ b = con_part_state.leader
       /\ m.broker_epoch = con_broker_reg[b].broker_epoch
       /\ m.partition_epoch = con_part_state.partition_epoch
       /\ m.leader_epoch = con_part_state.leader_epoch
    THEN IF EligibleIsr(m)
         THEN Nil
         ELSE IneligibleReplica
    ELSE FencedEpoch

ReceiveAlterPartitionRequest ==
    \E m \in DOMAIN messages : 
        \* enabling conditions
        /\ ReceivableMsg(m, AlterPartitionRequest)
        /\ LET b == m.source
               new_ldr_epoch  == con_part_state.leader_epoch \* unchanged
               new_part_epoch == con_part_state.partition_epoch +1
               error          == ValidateRequest(b, m)
           IN
              \* state mutations
              /\ IF error = Nil
                 THEN \* apply the requested partition state change
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
                      /\ UNCHANGED << con_part_state, con_metadata_log>>
        /\ UNCHANGED << con_broker_reg, con_unfenced, broker_vars, 
                        replica_vars, aux_vars, inv_vars >>
              

(*------------------------------------------------------------------------------
  ACTION: ReceiveAlterPartitionResponse

  A broker receives an AlterPartition response. 

  If the response is ignored in the following casesL
    - The response does not match the requested change
    - Has a Nil error code but the partition epoch is not higher.
      This happens when a metadata update for this change was
      processed before receiving the AlterPartition response.
   
  If the response matches the expected requested change, and indicates 
  success then updates its local partition state. If the response 
  indicates an IneligibleReplica or FencedEpoch, it rolls back its 
  eagerly applied partition state change, reverting to the last 
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
    LET last_part_state == [PartitionState(b) EXCEPT !.maximal_isr =   
                                    PartitionState(b).isr]                      
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
              /\ replica_pending_ap[b].request = m.request
              /\ IF m.error = Nil
                 THEN m.partition_epoch > PartitionState(b).partition_epoch
                 ELSE TRUE
              \* state mutations
              /\ IF m.error = Nil 
                 THEN CompletePartitionChange(b, m)
                 ELSE RollbackPartitionChange(b)
              /\ ResetPendingAlterPartition(b)
              /\ Discard(m)
        /\ UNCHANGED << con_vars, broker_vars, replica_replica_state, 
                        replica_status, aux_vars >>

(*-----------------------------------------------------------------------
  ACTION: SendFetchRequest

  A follower sends a fetch request to the partition leader.
  To avoid an infinite cycle of fetch request and responses
  we limit fetch requests to when a request can help the
  cluster make progress.
---------------------------------------------------------------------*)

SendFetchRequest ==
    \E from, to \in Brokers :
        \* enabling conditions
        /\ from # to
        /\ broker_state[from].status = RUNNING         \* The broker is running
        /\ Fetcher(from, to).partition # Nil           \* The fetcher has the partition added
        /\ Fetcher(from, to).pending_response = FALSE  \* The fetcher is not waiting for a response
        /\ PartitionState(from).leader = to            \* This replica believes the destination 
                                                       \* broker hosts the leader replica
        /\ __FetchMakesProgress(from) \* also prevents infinite cycles
        \* state mutations
        /\ Send([type               |-> FetchRequest,
                 broker_epoch       |-> broker_state[from].broker_epoch,
                 fetch_session_id   |-> FollowerFetchSessionId(from, to),
                 fetch_epoch        |-> FollowerFetchEpoch(from, to),
                 partition |-> \* only one partition modeled
                    [leader_epoch       |-> PartitionState(from).leader_epoch,
                     fetch_offset       |-> Fetcher(from, to).partition.fetch_offset,
                     last_fetched_epoch |-> Fetcher(from, to).partition.last_fetched_epoch],
                 dest               |-> to,
                 source             |-> from])
        /\ broker_fetchers' = [broker_fetchers EXCEPT ![from][to].pending_response = TRUE]
        /\ UNCHANGED << con_vars, broker_state, broker_fetch_session, broker_metadata_log, 
                        replica_part_state, replica_part_data, replica_replica_state,
                        replica_status, replica_pending_ap, inv_vars, aux_vars >>
        
(*----------------------------------------------------------------------------
  ACTION: ReceiveFetchRequest
  
  A broker receives a fetch request and responds with a fetch response. The fetch
  request is only accepted if its session id and fetch epoch match what is expected.
  The rest of the validation is specific to the single partition being modeled.
  
  The response is determined by the results of partition validation and a diverging 
  epoch check. One of the following will occur:
  - If the broker does not host the partition leader or the leader epoch does not match
    then reply with an error code.
  - If the fetch_offset and last_fetched_epoch are not consistent with the partition
    log then reply with a diverging epoch.
  - If all matches up then return the next record.
  
  The partition replica may advance the high watermark based on the fetch 
  offset in the fetch request. The broker includes the HWM in fetch response.
  
  This spec only sends one record at a time.
---------------------------------------------------------------------*)  

ReceiveFetchRequest ==
    \E m \in DOMAIN messages :
        \* enabling conditions
        /\ ReceivableMsg(m, FetchRequest)
        /\ LET b          == m.dest
               last_epoch == LastOffsetForEpoch(b, m.partition.last_fetched_epoch, TRUE)
           IN
              /\ broker_state[b].status = RUNNING
              /\ LeaderFetchSessionMatch(b, m.source, m.fetch_session_id, m.fetch_epoch)
              \* state mutations
              /\ CASE \* --- CASE stale leader/not leader/fenced leader epoch ---
                      \/ replica_status[b] # Leader
                      \/ PartitionState(b).leader_epoch # m.partition.leader_epoch ->
                          \* In the case of a stale leader, don't do any state changes,
                          \* wait for the metadata update to bring this stale leader up to date.        
                          /\ Reply(m,
                                    [type             |-> FetchResponse,
                                     fetch_session_id |-> m.fetch_session_id,
                                     partition |-> \* only one partition modeled
                                        [error           |-> CASE replica_status[b] # Leader         -> NotLeaderOrFollower
                                                               [] PartitionState(b).leader_epoch < 
                                                                            m.partition.leader_epoch -> UnknownLeaderEpoch
                                                               [] OTHER                              -> FencedEpoch,
                                         leader_epoch    |-> PartitionState(b).leader_epoch,
                                         fetch_offset    |-> m.partition.fetch_offset,
                                         diverging_epoch |-> Nil,
                                         hwm             |-> HwmOf(b),
                                         records         |-> <<>>],
                                     dest             |-> m.source,
                                     source           |-> m.dest])
                          /\ UNCHANGED << replica_replica_state, replica_part_data, inv_vars >> 
                   \* --- CASE diverging epoch -------------------------
                   [] \/ last_epoch.epoch < m.partition.last_fetched_epoch
                      \/ last_epoch.offset < m.partition.fetch_offset ->
                          /\ Reply(m,
                                    [type             |-> FetchResponse,
                                     fetch_session_id |-> m.fetch_session_id,
                                     partition |-> \* only one partition modeled
                                        [error           |-> Nil,
                                         leader_epoch    |-> PartitionState(b).leader_epoch,
                                         fetch_offset    |-> m.partition.fetch_offset,
                                         diverging_epoch |-> last_epoch,
                                         hwm             |-> HwmOf(b),
                                         records         |-> <<>>],
                                     dest             |-> m.source,
                                     source           |-> m.dest])
                          /\ UNCHANGED << replica_replica_state, replica_part_data, inv_vars >>
                   \* --- CASE OK ---------------------------------------
                   [] OTHER -> 
                          LET updated_rep_state == [replica_replica_state[b] EXCEPT ![m.source] =
                                                        [leo          |-> m.partition.fetch_offset,
                                                         broker_epoch |-> m.broker_epoch]]
                              old_hwm == HwmOf(b)
                              new_hwm == HighestCommitted(b, PartitionState(b).maximal_isr, 
                                                          updated_rep_state) + 1
                          IN
                              /\ MaybeAdvanceHighWatermark(b, old_hwm, new_hwm, TRUE)
                              /\ replica_replica_state' = [replica_replica_state EXCEPT ![b] = updated_rep_state]
                              /\ Reply(m,
                                        [type             |-> FetchResponse,
                                         fetch_session_id |-> m.fetch_session_id,
                                         partition |-> \* only one partition modeled
                                            [type            |-> FetchResponse,
                                             error           |-> Nil,
                                             leader_epoch    |-> PartitionState(b).leader_epoch,
                                             fetch_offset    |-> m.partition.fetch_offset,
                                             diverging_epoch |-> Nil,
                                             hwm             |-> IF new_hwm > old_hwm
                                                                 THEN new_hwm ELSE old_hwm,
                                             records         |-> IF m.partition.fetch_offset < LeoOf(b)
                                                                 THEN <<LogEntry(b, m.partition.fetch_offset)>> \* only send one entry
                                                                 ELSE <<>>], 
                                         dest             |-> m.source,
                                         source           |-> m.dest])
                    \* CASE END ------------------------------------------
              /\ IncrementLeaderFetchEpoch(b, m.source)
              /\ UNCHANGED << con_vars, broker_state, broker_fetchers,
                              broker_metadata_log, replica_part_state, replica_status,
                              replica_pending_ap, aux_vars >>        

(*-------------------------------------------------------------------
  ACTION: ReceiveFetchResponse

  A broker receives a fetch response. The fetch response is only
  accepted if its session id matches the local session id for this
  fetcher. The remaining validation applies only to the single
  partition being modeled.
  
  The following behavior can occur:
  - if the local replica is no longer a leader
        or the last request was invalid                      
        or this fetcher no longer hosts the partition
        or the fetch offset doesn't match
    then this is basically a no-op.
  - if the diverging epoch is set then the follower truncates its log.
  - if all is ok, the follower:
        a. appends the record to its log.
        b. updates the high watermark if the response HWM falls within
           the bounds of the log. This means that the high watermark
           on a follower is not monotonic.
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

ReceiveFetchResponse ==
    \E m \in DOMAIN messages :
        \* enabling conditions
        /\ ReceivableMsg(m, FetchResponse)
        /\ LET b       == m.dest
           IN
              /\ broker_state[b].status = RUNNING
              /\ Fetcher(b, m.source).pending_response = TRUE
              /\ FollowerFetchSessionMatch(b, m.source, m.fetch_session_id)
              \* state mutations
              /\ CASE
                   \* --- CASE NoOp ------------------------------------------
                      \* The last request was invalid, or the local replica is   
                      \* no longer a follower, or this fetcher no longer hosts 
                      \* the partition or the fetch offset doesn't match.
                      \/ m.partition.error # Nil
                      \/ replica_status[b] # Follower
                      \/ broker_fetchers[b][m.source].partition = Nil
                      \/ /\ Fetcher(b, m.source).partition # Nil
                         /\ Fetcher(b, m.source).partition.fetch_offset # 
                                                    m.partition.fetch_offset ->
                          \* state mutations
                          /\ broker_fetchers' = [broker_fetchers EXCEPT 
                                                        ![b][m.source].pending_response = FALSE]
                          /\ UNCHANGED replica_part_data
                   \* --- CASE diverging epoch -----------------------------
                   [] m.partition.diverging_epoch # Nil ->
                          \* the follower log has diverged, truncate the log and update fetch state
                          LET after_trunc        == TruncateToSafePoint(b, m.partition.diverging_epoch)
                              last_fetched_epoch == IF after_trunc.log = <<>>
                                                    THEN 0
                                                    ELSE Last(after_trunc.log).epoch
                          IN  \* state mutations
                              /\ replica_part_data' = [replica_part_data EXCEPT ![b] = after_trunc] 
                              /\ broker_fetchers' = [broker_fetchers EXCEPT ![b][m.source] =  
                                                            [partition |-> [fetch_offset       |-> after_trunc.leo,
                                                                            last_fetched_epoch |-> last_fetched_epoch],
                                                             pending_response |-> FALSE]]
                   \* --- CASE OK ------------------------------------------  
                   [] OTHER ->
                          LET new_leo == Len(LogOf(b)) + Len(m.partition.records) + 1
                              last_fetched_epoch == IF m.partition.records # <<>>
                                                    THEN Last(m.partition.records).epoch
                                                    ELSE Fetcher(b, m.source).partition.last_fetched_epoch
                          IN
                              /\ LeoOf(b) = m.partition.fetch_offset \* double check the fetch offset matches the LEO
                              \* state mutations
                              /\ replica_part_data' = [replica_part_data EXCEPT 
                                                        ![b].log = LogOf(b) \o m.partition.records, \* append the new data
                                                        ![b].leo = new_leo,
                                                        \* just overwrite HWM as long as it falls within bounds of the log
                                                        ![b].hwm = IF m.partition.hwm <= new_leo
                                                                   THEN m.partition.hwm ELSE HwmOf(b)] 
                              /\ broker_fetchers' = [broker_fetchers EXCEPT ![b][m.source] =  
                                                            [partition |-> [fetch_offset       |-> new_leo,
                                                                            last_fetched_epoch |-> last_fetched_epoch],
                                                             pending_response |-> FALSE]]
                  \* CASE END -----------------------------------------
              /\ IncrementFollowerFetchEpoch(b, m.source)
              /\ Discard(m)
              /\ UNCHANGED << con_vars, broker_state, broker_metadata_log, replica_part_state, replica_replica_state,
                              replica_status, replica_pending_ap, inv_vars, aux_vars >> 

(*--------------------------------------------------------------
  ACTION: WriteRecordToLeader

  A leader receives a produce request if the maximal ISR 
  size >= minISR, it writes the value to its local partition log.
---------------------------------------------------------------------*)  

WriteRecordToLeader ==
    \E b \in Brokers, v \in Values :
        \* enabling conditions
        /\ v \notin DOMAIN inv_acked \* this value has not yet been written
        /\ broker_state[b].status = RUNNING
        /\ replica_status[b] = Leader
        /\ Cardinality(PartitionState(b).maximal_isr) >= MinISR
        \* state mutations
        /\ LET new_leo    == LeoOf(b) + 1
               new_record == [epoch  |-> PartitionState(b).leader_epoch,
                              offset |-> LeoOf(b),
                              value  |-> v]
               new_log    == Append(LogOf(b), new_record)
           IN
              /\ replica_part_data' = [replica_part_data EXCEPT ![b] =
                                         [replica_part_data[b] EXCEPT !.leo = new_leo,
                                                                      !.log = new_log]]
              /\ replica_replica_state' = [replica_replica_state EXCEPT ![b][b].leo = new_leo]
              /\ inv_acked' = inv_acked @@ (v :> Nil)
              /\ UNCHANGED << con_vars, broker_vars, replica_part_state, replica_status, 
                              replica_pending_ap, messages, aux_vars, inv_true_hwm, inv_consumed >>

(*-----------------------------------------------------------------------
  ACTION: UncleanShutdown

  A broker shutsdown uncleanly. In this spec, the entire partition log is 
  truncated. Also, in this action, the controller detects the broker 
  is unavailable and fences the broker.
---------------------------------------------------------------------*)  

DropFetchSessions(b) ==
    \* all fetch state is lost
    /\ broker_fetchers' = [broker_fetchers EXCEPT ![b] = 
                                [b1 \in Brokers |-> BlankFetchState]]
    \* all recv and send sessions are lost
    /\ broker_fetch_session' = [broker_fetch_session EXCEPT ![b] = 
                                    [b1 \in Brokers |-> 
                                        [send |-> Nil,
                                         recv |-> Nil]]]

FailPendingWritesIfLeader(b) ==
    IF /\ replica_status[b] = Leader 
       /\ HwmOf(b) < LeoOf(b)
    THEN FailPendingWrites(b)
    ELSE UNCHANGED inv_acked

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
        /\ replica_status' = [replica_status EXCEPT ![b] = Nil]
        /\ replica_part_data' = [replica_part_data EXCEPT ![b] = 
                                        [log |-> <<>>, hwm |-> 1, leo |-> 1,
                                         epoch_start_offset |-> 0]]
        /\ replica_replica_state' = [replica_replica_state EXCEPT ![b] = 
                                        [b1 \in Brokers |-> BlankReplicaState]]
        /\ ResetPendingAlterPartition(b)
        /\ aux_ctrs' = [aux_ctrs EXCEPT !.unclean_shutdown_ctr = @ + 1]
        /\ FailPendingWritesIfLeader(b)
        \* make the controller detect it
        /\ HandleBrokerFenced(b)
        /\ con_broker_reg' = [con_broker_reg EXCEPT ![b].status = FENCED]
        /\ UNCHANGED << replica_part_state, broker_metadata_log, inv_true_hwm,
                        inv_consumed, messages, aux_broker_epoch, aux_session >>
                        
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
        /\ DropFetchSessions(b)
        /\ replica_status' = [replica_status EXCEPT ![b] = Nil]
        /\ replica_replica_state' = [replica_replica_state EXCEPT ![b] = 
                                        [b1 \in Brokers |-> BlankReplicaState]]
        /\ ResetPendingAlterPartition(b)
        /\ aux_ctrs' = [aux_ctrs EXCEPT !.clean_shutdown_ctr = @ + 1]
        /\ FailPendingWritesIfLeader(b)
        \* make the controller detect it
        /\ HandleBrokerFenced(b)
        /\ con_broker_reg' = [con_broker_reg EXCEPT ![b].status = FENCED]
        /\ UNCHANGED << replica_part_state, replica_part_data, broker_metadata_log, 
                        inv_true_hwm, inv_consumed, messages, aux_broker_epoch, aux_session >>

\* ===============================================================
\* INVARIANTS
\* ===============================================================

\* INV: TypeOK
\* Basic type checking
TypeOK ==
    /\ con_unfenced \in SUBSET Brokers
    /\ con_broker_reg \in [Brokers -> ControllerSideBrokerState]
    /\ con_part_state \in ControllerPartitionState
    /\ broker_state \in [Brokers -> BrokerSideState]
    /\ broker_fetch_session \in [Brokers -> [Brokers -> [recv: FetchSession \union {Nil},
                                                         send: FetchSession \union {Nil}]]]
    /\ broker_fetchers \in [Brokers -> [Brokers -> BrokerFetcher]]
    /\ replica_part_state \in [Brokers -> ReplicaPartitionState]
    /\ replica_replica_state \in [Brokers -> [Brokers -> ReplicaState]]
    /\ aux_ctrs \in StateSpaceLimitCtrs
    /\ replica_status \in [Brokers -> {Leader, Follower, Nil}]

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
        /\ replica_part_data[b].leo = Len(replica_part_data[b].log) + 1
        /\ \A offset \in 1..replica_part_data[b].leo-1 :
                replica_part_data[b].log[offset].offset = offset

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
        \* and followers do have a fetcher with the partition added
        /\ CASE replica_status[b] = Leader ->
                    ~\E b1 \in Brokers :
                        /\ b # b1
                        /\ broker_fetchers[b][b1].partition # Nil
             [] replica_status[b] = Follower ->
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
    /\ IF Cardinality(con_part_state.isr) > 1
       THEN ~\E b \in Brokers :
               /\ con_broker_reg[b].status = FENCED
               /\ b \in con_part_state.isr
       ELSE TRUE
    \* The ISR cannot be empty
    /\ con_part_state.isr # {} 
    
\* INV: ValidLeaderMaximalISR
\* The maximal ISR is critical for safety. The invariant here is that
\* the maximal ISR on the (non-stale) leader must be a superset of
\* the controller ISR. Else we can lose data.
\* (Triggers soon than invariant LeaderHasCompleteCommittedLog). 
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

\* INV: ControllerIsrHasUpToTrueHWM
\* The true HWM is tracked by the spec (not the brokers)
\* and if any replica in the ISR has an LEO < the true
\* HWM, then that is an illegal state which can lead
\* to data loss. 
\* (Triggers soon than invariant LeaderHasCompleteCommittedLog).
ControllerIsrHasUpToTrueHWM ==
    \* No member of the ISR is missing committed records
    \* and is RUNNING 
    /\ ~\E b \in con_part_state.isr :
        /\ replica_part_data[b].leo < inv_true_hwm
        /\ broker_state[b].status = RUNNING

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
            /\ replica_part_data[b1].leo > offset
            /\ replica_part_data[b2].leo > offset
            /\ replica_part_data[b1].hwm > offset
            /\ replica_part_data[b2].hwm > offset
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
               \E offset \in LogOffsets(b) :
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
                /\ offset \in LogOffsets(b)
                /\ replica_part_data[b].log[offset] = inv_consumed[offset]
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
        replica_pending_ap[b].epoch > 0 ~> 
            \/ replica_pending_ap[b].epoch = replica_part_state[b].partition_epoch
            \/ replica_pending_ap[b].epoch = 0)

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
        (/\ v \in DOMAIN inv_acked
         /\ inv_acked[v] = TRUE) ~>
                (\A b \in Brokers : 
                    \E offset \in LogOffsets(b) :
                        replica_part_data[b].log[offset].value = v)


\* ==================================================================
\*              INIT and NEXT
\* ==================================================================

\* The cluster starts in an already established state.
\* When InitIsrSize < ReplicationFactor then a subset of broker start outside 
\* of the ISR with a stale partiion_epoch. This allows us to explore
\* more state space.

Init ==
    LET init_isr   == CHOOSE isr \in SUBSET Brokers :
                        /\ 1 \in isr \* we always start with broker 1 as the leader
                        /\ Cardinality(isr) = InitIsrSize
        \* if the inital ISR is < RF then we make the partition_epoch = 2 
        \* to simulate a change having already occurred.
        part_epoch  == IF init_isr = Brokers THEN 1 ELSE 2
        metadata_log  == <<>>
        metadata_log1 == Append(metadata_log, 
                                  [type            |-> PartitionChangeRecord,
                                   leader          |-> 1,
                                   isr             |-> init_isr,
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
        /\ con_part_state = 
                [isr             |-> init_isr,
                 leader          |-> 1, \* broker 1
                 leader_epoch    |-> 1,
                 partition_epoch |-> part_epoch] 
        /\ broker_state = [b \in Brokers |-> 
                [status            |-> RUNNING,
                 broker_epoch      |-> b,
                 incarnation_id    |-> b,
                 registered        |-> TRUE]]
        /\ broker_fetch_session = [b \in Brokers |-> 
                                        [b1 \in Brokers |->
                                            [recv |-> [id |-> 1, epoch |-> 1],
                                             send |-> [id |-> 1, epoch |-> 1]]]]
        /\ broker_fetchers = [b \in Brokers |->
                                    [b1 \in Brokers |->
                                        IF b # 1 /\ b1 = 1
                                        THEN [partition        |-> [fetch_offset       |-> 1,
                                                                    last_fetched_epoch |-> 0],
                                              pending_response |-> FALSE]
                                        ELSE BlankFetchState]]
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
                                     leader_epoch |-> 1,
                                     \* if the "initial ISR = Brokers" then all brokers
                                     \* have the same partition_epoch, else, the brokers in the
                                     \* ISR have the up-to-date epoch and the rest have a stale one.
                                     partition_epoch |-> CASE init_isr = Brokers -> 1 
                                                           [] b \in init_isr -> 2
                                                           [] OTHER -> 1]]
        \* the partition log on each replica starts empty
        /\ replica_part_data = [b \in Brokers |->
                                    [log                |-> <<>>,
                                     hwm                |-> 1,
                                     leo                |-> 1,
                                     epoch_start_offset |-> 0]]
        /\ replica_replica_state = [b \in Brokers |->
                                        [b1 \in Brokers |-> BlankReplicaState]]
        /\ replica_pending_ap = [b \in Brokers |-> [epoch |-> 0, request |-> Nil]]
        /\ aux_broker_epoch = ReplicationFactor
        /\ aux_session = 1
        /\ aux_ctrs = [incarn_ctr           |-> ReplicationFactor + 1,
                       clean_shutdown_ctr   |-> 0,
                       unclean_shutdown_ctr |-> 0,
                       fence_broker_ctr     |-> 0,
                       alter_part_ctr       |-> 0]
        /\ inv_acked = <<>>
        /\ inv_true_hwm = 1
        /\ inv_consumed = <<>>
        /\ messages = <<>>

Next ==
    \* broker actions
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
    
Liveness ==
    WF_vars(Next)

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Liveness    
=============================================================================
