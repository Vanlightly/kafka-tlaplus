# KIP 996 - KRaft pre-vote

Find the KIP here: https://cwiki.apache.org/confluence/display/KAFKA/KIP-996%3A+Pre-Vote

## Basic mechanics of pre-vote

TODO: Do a prose write-up as I did for the Kafka Replication Protocol.

See the KIP for how it works.

## Safety and liveness

### Safety

The following invariants are specified, as per the Raft paper:
- **LogMatching**: If two logs contain a record with the same offset and epoch, then the logs are identical in all records up through the given offset.
- **ElectionSafety**: At most one server can be elected leader in one epoch.
- **LeaderCompleteness**: A leader will host all committed records.

Additionally, we have the invariants:
- **Durability**: All committed records will exist on at least one voter.
- **ValidRolesAndStates**: Checks for inconsistencies in per server state.

### Liveness

In order to test liveness under different network partition topologies, this spec models network connectivity between servers and includes an action for changing the connectivity.

#### Properties

The following liveness properties are implemented:
- **ValuesEventuallyAcked**: Every value that can be written, will eventually be written and either a positive or a negative acknowledgement sent. This detects stuck values.
- **ReconfigurationNotStuck**: A reconfiguration command (AddVoter/RemoveVoter) eventually gets committed or is removed from all logs (due to a leader change).
- **EventuallyLeaderElected**: If the cluster has no functional leader, then eventually a functional leader will get elected.
- **NotStuckInProspective**: If a server transitions to Prospective, it will eventually transition to a different state.

#### Making the spec work with liveness properties

Liveness is typically hard to support. Making it work in this spec has caused some additional complexity. The strategy to support liveness in this spec is to **limit the number of perturbation actions but not actions that lead to recovery**. For example, a counter is used to count the number of times a pre-vote is initiated without an explicit trigger, such as a network partition or a leader crashing or resigning. Such pre-votes are disruptive to a stable cluster. However, once a pre-vote has initiated, it is allowed to run its course without limitation. The implication of this is that the state space is infinite as every election can end up a draw, requiring a new election. Therefore, when testing liveness, **you can only use simulation mode** because the state space is infinite. There is no good way around this limitation.

When testing liveness, set the constant `TestLiveness = TRUE`. This changes the specifications behavior to proactively prevents cycles that would cause liveness properties to fail. It does this by:
- Adding an pre-vote counter to ensure the state space changes on each pre-vote initiation. Because the epoch does not get bumped, TLC will see cycles without this counter.
- Add additional conditions to actions such as sending fetch requests, to avoid cycles.
- Prevent AddVoter and RemoveVoter commands from causing a cluster to get stuck when a cluster is already in a severely degraded state.
- Only allowing network connectivity changes that maintains a functioning majority of connected servers.
- Only allowing a server to crash if a functioning majority is remaining afterward.

Many of these extra conditions are placed in the kraft_kip_996_liveness.tla module to not pollute the main spec. When `TestLiveness = FALSE`, none of the above behavior changes are employed.

## Running TLC

This specification includes both pre-vote and reconfiguration which means that is large, with a large number possible actions that can happen at any moment. Due to this, the state space is huge and I recommend only using simulation mode.

There are two cfg files:
- `kraft_kip_996.cfg` configured for testing safety properties only.
- `model_liveness.cfg` configured for safety and liveness.

Note that when testing liveness, the state space is infinite (as elections may be needed for progress, causing infinite elections). When using simulation by default it will stop a trace at 100 steps. You can increase that using the `-depth` argument.

Note that simulation mode is single-threaded when testing liveness. To use all cores, run multiple instances of TLC with each writing its output to a file.

## Reading the specification

The specification is split into the following files:

- `kraft_kip_996.tla`: The main spec with the actions, init and next.
- `network.tla`: Message passing and connectivity.
- `kraft_kip_996_types.tla`: The constants and variables.
- `kraft_kip_996_functions.tla`: Common functions and helper functions.
- `kraft_kip_996_properties.tla`: Invariants and liveness properties.
- `kraft_kip_996_liveness.tla`: Extra conditions to avoid cycles when testing liveness.

You may which to start at the Next state formula section which will show you each possible action that can occur.