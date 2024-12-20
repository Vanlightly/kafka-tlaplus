# Kafka transactions - phase 2 - AddPartitionsToTxnRequest

## Transaction coordinator clarification

Before explaining the changes, it's worth clarifying what the term Transaction Coordinator (TC) means, and its relationship to txn log partitions:

- There is one TC per broker.
- There are one or more txn log partitions spread across the cluster. Any given broker will host zero or more txn log partition replicas. A replica is one copy of the partition. With an RF=3, a partition will have 3 replicas.
- A TC that hosts a txn log partition, will act as either the replica leader or a replica follower. Any given TC therefore may have following status with regard to three disjoint subsets of the txn log partitions:
  - act as the leader of a subset of partitions
  - act as a follower on a subset of partitions
  - not host a subset of partitions
- All txn related requests must go to the txn log partition leader.

I will refer to the TC that is acting as the leader for a given txn log partition, as the "active TC" of that partition.

NOTE! In this early version, every broker hosts every txn log partition implicitly. This may change.

## What's new in this version of the spec

This version of the spec gets the AddPartitionsToTxnRequest and AddPartitionsToTxnResponse. 

Also added:
1. Txn log partition leader elections, i.e, leadership of a txn log partition can move between TCs.
2. The FindCoordinator request is now partially modeled, as a simpler atomic lookup. It can still be stale as a txn log partition election can move the active TC can move from one broker to another at any time. It is assumed that the Brokers constant includes all replicas of the txn log partitions.
3. Producer fencing with the accompanying txn abort. However, the txn markers are not yet implemented.

It does not include writing records to topic partitions, the LSO or txn markers yet.

Limitations:
1. Does not implement KIP-360 that allows a producer to send an InitPidRequest with an existing pid and epoch.
2. Does not implement KIP-890.
               
Running: 
1. Use the VS Code TLA+ extension.
2. Configure the model parameters in the cfg file.
3. Choose either liveness checking or not by commenting and uncommenting sections in the cfg.See the cfg file.
4. You must use the -deadlock parameter as clients eventually stop doing further work, which TLC will interpret as a deadlock.

Example: `-workers 4 -deadlock -fpmem 0.75`

Says 4 dedicated threads, 75% of available memory, and a "deadlock" will not trigger a counterexample.

## Abstractions discussion

The Kafka replication protocol and the KRaft controller are abstracted. Each has its own detailed TLA+ specification, so we can rely on the properties proven by those specifications.

### Txn log partition replication

The Kafka replication protocol is grossly simplified in this spec. We simply rely on the properties proven by the Kafka replication protocol TLA+ specification. However, it is currently simplified to the point that potentially some edge cases in the TCs may not occur.

This spec is not concerned with ISR, replication factor, min.insync.replicas. It is only concerned with the high watermark (HWM) which dictates whether a log entry is committed or not. Each txn log partition is modeled as a log (and high watermark) per broker. Replication and HWM propagation is atomic, where one entry is replicated from the leader (the active TC) replica to all follower replicas. When a leader is demoted to follower, it simply truncates its log to the HWM. This is safe due to the simplified replication logic.

The cluster of brokers are all assumed to host all txn log partitions (which is ok as this spec does not concern itself with RF, ISR or MinISR).

### KRaft controller

The controller is not modeled as an explicit actor in the system. Instead:
1. The metadata for the leader and epoch of each txn log partition is modeled as a map. No replication.
2. Leader elections simply happen. Given this spec does not include aspects of the replication protocol such as the ISR, and replication is atomic, any follower can simply be elected as the leader at anytime without data loss.