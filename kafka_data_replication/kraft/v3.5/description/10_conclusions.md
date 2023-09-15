# 10. Conclusions

Thie protocol description has described the Kafka replication protocol with the modifications of KIP-966.

While it is now typical to see majority-quorum based systems that must be sized according to the `2f + 1` formula, Kafka offers a flexible set of configurations which allow the user to optimize for safety (based on the formula `f = MinISR - 1`) or to optimize for availability via a number of approaches.

Kafka is able to support a higher performance asynchronous storage engine through the application of recovery and verifiable trust which make it somewhat unique in the field of replicated data systems. With KIP-966 the recovery process is further strengthened to eliminate the known issue of the Last Replica Standing as well improve reassignments.

If you notice any errors in this protocol description, please open an issue for discussion.

<br/>
<br/>

- [Back - 9. Formal verification](9_formal_verification.md)
- [Next - 11. Future work](11_future_work.md)