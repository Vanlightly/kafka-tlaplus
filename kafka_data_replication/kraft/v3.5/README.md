# Kafka replication TLA+ specification and prose description

This directory contains:

1. A [TLA+ specification](kafka_replication_v3_5.tla) of the Kafka replication protocol as of version 3.5.
2. A [protocol description](description/0_kafka_replication_protocol.md) written in English prose with diagrams.

It is recommended to read the protocol description before delving into the TLA+.

## Protocol description

The protocol description should be complete enough to understand the logical design of the replication protocol.

## TLA+ specification

Be warned, this is a large specification which covers almost the entire protocol design rather than a highly abstracted version.

### The files

Due to the nature of the design of Kafka, the TLA+ specification is large and complex. It is split up into following files:

- `kafka_replication_v3.5.tla`: The main TLA+ file which contains all actions.
- `v3_5_types.tla`: Contains all variables, constants and type definitions.
- `v3_5_functions.tla`: The reusable formulae that are called from multiple actions.
- `v3_5_properties.tla`: The safety and liveness properties.
- `message_passing.tla`: The TLA+ required for the sending and receiving of messages.

### What is modeled

This specification models the Kafka replication protocol which consists of the distributed KRaft controller RSM which works in consort with each partition. Each partition is comprised a leader replica and multiple follower replicas.

The controller is responsible for:

- Broker registration
- Failure detection (fencing/unfencing)
- Leader election.
- Co-management of the ISR of each partition.
- Serving metadata records to the brokers.
- Reassignment

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

Fetch sessions have also been simplified. Rather than model fetch
sessions explicitly, the spec guarantees that stale fetch requests
and responses cannot be processed.

Some notes about the specification:

- Offsets are 1-based, not 0-based like in the implementation. This is due to
  TLA+ sequences being 1-based.
- The Log End Offset (LEO) and High Watermark (HWM) are exclusive. For example,
  if the last offset in the log is 5, then the LEO is 6. If the highest committed
  offset is 3 then the HWM is 4. Because offsets are 1-based, an empty log will have 
  an LEO and HWM of 1.  
- Only models acks=all requests.
- Only models a single partition.
- This spec does not model the controller as a distributed Raft based RSM as it
  would add a lot of complexity. There is a separate TLA+ specification for
  the KRaft implementation of Raft, therefore we abstract the internals of the 
  RSM for this specification. 
- All inter-node communication is modeled as message passing. However, metadata 
  replication does not model fetch/response, instead log records eventually arrive
  at brokers, in order. This reduces the state space.
- The word "broker" refers to broker state (not concerned with partitions).
  The word "replica" refers to one instance of a partition on a broker. One
  broker can host multiple partitions and therefore replicas.
- The state space would be infinite as epochs are continually increasing, therefore
  the state space is limited by constants which limit the number of times
  certain actions can happen.
- Liveness checks can be impacted by fetch request/response cycles so some
  anti-cycle checks are used (ugly but unfortunately necessary for liveness checking).
- Some formula are purely for the spec and should be ignored when using
  the spec to understand the design. These formulas are prefixed with
  __, such as __IgnoreThis.

### Notes on invariants and liveness

Safety properties (for discussion of these properties see the acompanying [protocol description](description/0_kafka_replication_protocol.md)):

- Leader completeness
- Log matching
- Leader candidate completeness
- Replication quorum superset
- Metadata log matching
- Read consistency
- No global loss of committed data (Leader Completeness is not enough to detect a sitation where no electable leaders exist and no replica hosts the complete committed log).

Liveness checks (assuming any failures are transitory):
- STARTING brokers eventually reach RUNNING
- FENCED brokers eventually become UNFENCED.
- Eventually, all brokers converge on controller metadata state.
- Eventually a write will be acknowledged (positively or negatively).
- Eventually a positively acknowledged write will be fully replicated.
- Eventually a reassignment completes

This version of the protocol has the Last Replica Standing issue which is addressed by [KIP-966](https://cwiki.apache.org/confluence/display/KAFKA/KIP-966%3A+Eligible+Leader+Replicas). The constant `AvoidLastReplicaStanding` when set to TRUE, does not allow the model checker to follow actions that result in the LRS issue occuring. This is helpful when checking behaviour of unclean shutdowns without the model checker hitting the LRS issue.

The comment `CHECK` can be found in places and these exist to confirm that the model checker finds data loss counterexamples when certain necessary checks are commented out.

### State space

The state space is extremely large and brute-force modeling checking is only practical on tiny models. Simulation mode is required for most cases.

The state space is large with Kafka because it explicitly curates the replication and election quorum (the ISR). Where Raft quorums are implicit (in how requests are sent and received and how the data is distributed), with the Kafka replication protocol, changes to quorums are registered and must be replicated from the controller to brokers. This greatly amplifies the number of states as each quorum change involves multiple messages being exchanged.

The state space is limited via the use of constants.

Some constants control the number of brokers, replicas and the number of record which can be written:

- `BrokerCount`
- `InitReplicationFactor` (the initial replication factor, which can change due to reassignments)
- `Values` (all the values that can ever be written)
  
Other constants limit the number perturbations which can occur: 

- `CleanShutdownLimit` (limits the number of clean shutdowns)
- `UncleanShutdownLimit` (limits the number of unclean shutdowns)
- `FenceBrokerLimit` (limits the number of times the controller arbitrarily fences a broker)
- `LeaderShrinkIsrLimit` (limits the number of AlterPartition requests that shrink the ISR)
- `ReassignmentLimit` (limits the number of partition reassignments)

Note that healing actions are never limited. For example, we limit the number of times brokers can get fenced, but never limit unfencing. We limit the number of ISR shrinks, but do not limit ISR expansions (we always let the partition heal).




