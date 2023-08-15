# Eligible Leader Replicas TLA+ spec

https://cwiki.apache.org/confluence/display/KAFKA/KIP-966%3A+Eligible+Leader+Replicas

## Model checking mode

This spec has a very large state space, primarily because of the metadata log, but the ELR itself increases the state space size because it adds more state and also adds more eligible leaders which translates to more states.

Model checking mode is possible on small models if you have reasonably sized hardware. For example,
the following model constants (which control state space size) took 35 hours and 350GB of disk space in model checking mode with 28 dedicated CPU threads and 100 GB dedicated RAM:

```
ReplicationFactor = 3
Values = { A }
MinISR = 2
InitIsrSize = 2
CleanShutdownLimit = 0
UncleanShutdownLimit = 1
FenceBrokerLimit = 1
AlterPartitionLimit = 1
```

## Simulation mode

Most checking requires simulation given the very large state space of this specification.