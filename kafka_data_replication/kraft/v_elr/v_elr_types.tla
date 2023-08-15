--------------------------- MODULE v_elr_types ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC

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
          AlterPartitionLimit,      \* limits the number of AlterPartition requests that can be sent
          LimitFetchesOnLeaderEpoch \* limits the state space by reducing the number of FencedLeaderEpoch and
                                    \* UnknownLeaderEpochs errors from fetch requests

\* Controller-side broker statuses
CONSTANTS FENCED,           
          UNFENCED

\* Broker-side statuses
CONSTANTS STARTING,
          RUNNING,
          OFFLINE_CLEAN,\* not really an actual state, used by the spec to say it is offline due to a clean shutdown
          OFFLINE_DIRTY \* not really an actual state, used by the spec to say it is offline due to an unclean shutdown

\* Replica role
CONSTANTS Leader,       
          Follower

\* Requests and responses
CONSTANTS RegisterBrokerRequest,
          RegisterBrokerResponse,
          AlterPartitionRequest,
          AlterPartitionResponse,
          FetchRequest,
          FetchResponse

\* errors
CONSTANTS IneligibleReplica,   \* An AlterPartition error code - a proposed ISR member is invalid.
          FencedLeaderEpoch,   \* An AlterPartition/Fetch error code - epoch of a request was stale.
          UnknownLeaderEpoch,  \* A fetch error code - when a stale leader receives a fetch.
          NotLeaderOrFollower  \* A fetch error code - when a non-leader receives a fetch.

\* other
CONSTANTS Controller,        \* used to denote the destination or source of a message is the controller
          NoLeader,          \* a constant value to represent the partition has no leader
          Nil                \* a constant used to denote 'nothing' or 'not set'

\* metadata log entry types
CONSTANTS PartitionChangeRecord

ASSUME InitIsrSize <= ReplicationFactor
ASSUME MinISR <= ReplicationFactor
ASSUME CleanShutdownLimit \in Nat
ASSUME UncleanShutdownLimit \in Nat
ASSUME FenceBrokerLimit \in Nat
ASSUME AlterPartitionLimit \in Nat

\* Controller state
VARIABLES con_unfenced,           \* the set of brokers which are in the state UNFENCED.
          con_broker_reg,         \* a map of broker id to broker registration on the controller.
          con_partition_metadata, \* the current state of the partition (leader, leader_epoch, isr).
          con_metadata_log        \* the KRaft metadata log.
          
\* Broker state not concerned with partitions.
\* Each variable is a map of [broker_id -> some state of that broker].          
VARIABLES broker_state,         \* state of each broker, such as status (RUNNING, STARTING etc)
          broker_fetchers,      \* the fetchers of each broker
          broker_metadata_log   \* the strongly eventually consistent copy of the 
                                \* KRaft metadata log on each broker.

\* Broker-side partition state
\* Each variable is a map of [broker_id -> partition related state].          
VARIABLES partition_status,         \* the role (leader, follower) and replication mode.
          partition_metadata,       \* the partition metadata state on each replica.
          partition_data,           \* the actual partition data, including HWM.
          partition_replica_state,  \* a map (used by the leader) to track the state of follower replicas.
          partition_pending_ap      \* info related to a pending AlterPartition request.

\* Auxilliary variables (not part of the protocol)           
VARIABLES aux_broker_epoch, \* Because we omit some metadata records, broker epochs cannot be based on metadata offsets.
          aux_ctrs          \* Some counters used to limit the number of times certain actions can occur, to limit the state space.

\* Auxilliary variables for verifying invariants (not part of the protocol)
VARIABLES inv_sent,      \* The values sent and written to a leader
          inv_pos_acked, \* The values that got positively acknowledged
          inv_neg_acked, \* The values that got negatively acknowledged
          inv_true_hwm,  \* Tracks the true HWM
          inv_consumed   \* Tracks the records consumed to detect divergence.

\* Variable lists
con_broker_vars == << con_unfenced, con_broker_reg >>
con_vars == << con_metadata_log,  con_broker_vars, con_partition_metadata >>
broker_vars == << broker_state, broker_fetchers, broker_metadata_log >>
part_vars == << partition_status, partition_metadata, partition_data,
                partition_replica_state, partition_pending_ap >>
inv_vars == << inv_sent, inv_pos_acked, inv_neg_acked, inv_true_hwm, inv_consumed >>
aux_vars == << aux_broker_epoch, aux_ctrs >>    

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

PartitionFetchState ==
    [fetch_offset: Nat,
     last_fetched_epoch: Nat,
     delayed: BOOLEAN]

BrokerFetcher ==
    [\* the partition that should be fetched for (only modeling one partition)
     partition: PartitionFetchState \union {Nil},
     \* TRUE when the fetcher is waiting for a fetch resonse
     pending_response: BOOLEAN]

PeerReplicaState ==
    [leo: Nat \union {Nil}, 
     broker_epoch: Nat]     
     
ControllerPartitionMetadata ==
    [isr: SUBSET Brokers,
     elr: SUBSET Brokers,
     leader: Brokers \union {NoLeader},
     leader_epoch: Nat,
     partition_epoch: Nat]
     
ReplicaPartitionMetadata ==
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
     broker_epoch: Nat,
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
     error: {FencedLeaderEpoch, IneligibleReplica},   
     request: {AlterPartitionRequestType},
     dest: {Controller},
     source: Brokers]     

FetchRequestType ==
    [type: {FetchRequest},
     broker_epoch: Nat,
     \* only one partition modeled
     partition: [leader_epoch: Nat,
                 fetch_offset: Nat,
                 last_fetched_epoch: Nat],
     dest: Brokers,
     source: Brokers]
     
FetchResponseType ==
    [type: {FetchResponse},
     \* only one partition modeled
     partition: [error: {Nil, NotLeaderOrFollower, UnknownLeaderEpoch, FencedLeaderEpoch},
                 leader_epoch: Nat,
                 fetch_offset: Nat,
                 hwm: Nat,
                 diverging_epoch: [epoch: Nat,
                                   end_offset: Nat] \union {Nil},
                 records: PartitionRecord],
     dest: Brokers,
     source: Brokers]  
    
=============================================================================    