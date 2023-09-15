# 9. Formal verification

The replication protocol is modeled in a TLA+ specification in this repository.

It includes verification of the safety properties:

- Leader Completeness
- Log Matching
- Leader Candidate Completeness
- Replication Quorum Superset
- Metadata Log Matching
- Read consistency
- No global loss of committed data (Leader Completeness is not enough to detect a sitation where no electable leaders exist and no replica hosts the complete committed log).

It includes verification of the liveness properties:
- Brokers eventually complete start-up.
- Fenced brokers eventually become unfenced.
- AlterPartition requests eventually complete (accepted or rejected).
- Broker metadata log eventually converges on controller metadata log.
- A write is eventually positively or negatively acknowledged.
- A positively acknowledged write is eventually fully replicated.
- A reassignment eventually completes.

The liveness properties are based on scenarios where clusters may experience failures but are allowed to recover and so should eventually allow stuck operations to complete.

See the TLA+ [readme](../README.md) for more details.

<br/>
<br/>

- [Back - 8. Broker lifecycle](8_broker_lifecycle.md)
- [Next - 10. Conclusions](10_conclusions.md)