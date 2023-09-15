# The Kafka Replication Protocol with KIP-966

BASED ON A DRAFT KIP! DETAILS MAY CHANGE.

This document is a description of the Kafka replication protocol with [KIP-966](https://cwiki.apache.org/confluence/display/KAFKA/KIP-966%3A+Eligible+Leader+Replicas). The objective is to provide a description that is similar to the descriptions of other protocols such as [Raft](https://raft.github.io/raft.pdf), [Multi-Paxos](https://dada.cs.washington.edu/research/tr/2009/09/UW-CSE-09-09-02.PDF) and [Viewstamped Replication Revisited](https://pmg.csail.mit.edu/papers/vr-revisited.pdf). This is not a research paper, there are no novel approaches proposed - it is simply a description of how the Apache Kafka replication protocol works. Everything you read here is the product of an open-source community of engineers that has evolved Apache Kafka since its inception.

## KIP-966

This KIP was introduced for the following reasons:

1. Fixes the Last Replica Standing issue, documented in the 3.5 protocol description (coming soon).
2. Strengthens the role of `min.insync.replicas` to make it the minimum replication factor of committed log records (bar broker failures).
3. Improves durability when clean elections are not possible by introducing a more sophisticated recovery mechanism.

A high level description of KIP-966 and why it is needed is also written [here](https://jack-vanlightly.com/blog/2023/8/17/kafka-kip-966-fixing-the-last-replica-standing-issue).

## Separating protocol from implementation

This protocol description tries to separate implementation from protocol logic as far as possible. However, due to the nature of how Kafka has evolved over many years, some of the behaviors, checks and conditions are somewhat married to the implementation. But as far as possible, this description aims to describe the replication protocol from a logical perspective free from implementation details.

## Contents

1. [Introduction](1_introduction.md)
2. [The replication algorithm](2_replication_algorithm.md)
3. [Log divergence](3_log_divergence.md)
4. [Partition reassignment (reconfiguration)](4_reassignment.md)
5. [Recovery as a strategy](5_recovery.md)
6. [Replication correctness](6_replication_correctness.md)
7. [Availability over consistency](7_availability.md)
8. [Broker lifecycle](8_broker_lifecycle.md)
9. [Formal verification](9_formal_verification.md)
10. [Conclusions](10_conclusions.md)
11. [Future work](11_future_work.md)

## Glossary

Terms and acronyms used in this description:

- ISR: In-Sync Replicas.
- ELR: Eligible Leader Replicas.
- HWM: High watermark.
- LEO: Log End Offset.
- LESO: Leader Epoch Start Offset.
- Offset: The position of a record in the log.
- Complete replica: A replica that hosts the complete committed log.
- Unclean shutdown: An abrupt termination or one such that the full shutdown sequence could not execute.
- Unclean replica/broker: A broker (and its replicas) which has restarted after an unclean shutdown.
- MinISR: min.insync.replicas.