# 7. Configuring for availability over consistency

So far the focus has been on acks=all produce requests but Kafka can also be configured for availability over consistency. There are a number of tunable knobs available to the administrator and developer.

## 7.1 Produce requests with acks=1

The producer configuration `acks` simply allows the partition leader to positively acknowledge a produce request no matter the size of the ISR (even if Min ISR is set). This improves write latency and write availability. 

Read availability is not impacted by the acks config though `acks=1` requests do benefit from the fact that HWM advancement is already geared more towards availability. The HWM advances based on the fetch positions of all followers in the ISR. If the ISR has three replicas then HWM advances to an offset when the fetch position has reached that offset in all ISR followers. But if the ISR has shrunk to the leader then the leader is free to advance the HWM based solely on itself. The result is that when using acks=1, the clients get end-to-end availability even when only the leader is functioning.

Note that `acks=1` records can be lost after leader elections as the producer is usually sent a positive acknowledgement while the record is still uncommitted. Uncommitted records have no guarantees of durability.

## 7.2 acks=all + min.insync.replicas=1 (Min ISR)

An alternative to `acks=1` is to use `acks=all + Min ISR=1`. This allows for the same write availability as `acks=1` but does not benefit from the write latency improvement. The reason for this is that `acks=1` allows the leader to acknowledge early, whereas `acks=all + Min ISR=1` allows the leader to accept writes when the size of the ISR is 1. If the ISR is of size 3, then the write must be replicated to all three before an acknowledgement is sent, whereas with `acks=1`, the leader would have sent the acknowledgement as soon as it had written it to its log.

`acks=all` requests survive leader elections<sup>*</sup> so we get an improvement to safety without compromising on availability. The operator can boost availability further by timing cluster rolls to when no partitions have degraded ISRs. If the cluster roll is initiated when all partitions have full ISRs then partitions have leader candidates to fail-over to during the rolls.

<sup>*</sup> note that safety is still impaired compared to `Min ISR=2` as the safety tolerance for lost brokers is `Min ISR - 1` (but this section is focused on availability over consistency).

## 7.3 Unclean leader elections

If a partition gets itself into a Last Replica Standing situation and this last replica (the leader) goes offline the partition remains unavailable until that specific replica becomes functional again. To avoid this unavailability the topic can be configured to allow unclean elections which allows a functional replica outside of the ISR to be elected. This can result in data loss but keeps the partition available.

Unclean elections have consequences such as:

- True HWM is no longer monotonic.
- Log divergence truncation may need to go through several rounds before the divergence is resolved. However, eventually, logs will still converge.
- Consumers may need to reset their offsets (because the True HWM may have gone backwards).

There may be additional logic in the replicas that has been missed by this protocol description that is required to handle the impacts of unclean leader elections. This is future work.

<br/>
<br/>

- [Back - 6. Replication correctness](6_replication_correctness.md)
- [Next - 8. Broker lifecycle](8_broker_lifecycle.md)