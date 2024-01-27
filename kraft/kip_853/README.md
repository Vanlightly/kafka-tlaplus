# KIP 853

This spec makes some effort to reuse some of the functions of the implementation in order to ensure it is accurately modelling the behaviour. 

Note the following messages are not modelled:

- BeginQuorumResponse as this is only required by the implementation for liveness. If the leader doesn't receive a response it resends the BeginQuorumRequest. However, in the specification, message retries are implicit and so explicit retries are not required.
- EndQuorumRequest/Response as this exists as an optimization for a leader that gracefully shutsdown or has been removed from the configuration. It is not needed for correctness and so is not included.
- FetchSnapshotRequest/Response. This is a straight forward optimization and so has not been explicitly modelled. 

The KRaft implementation uses a cache object as an index for epochs and their start offsets which is required for leaders to be able to give followers the information they need to truncate their logs. This specification does not model this cache but simply looks up this information from the log itself.

## Roles and Transitions

A KRaft server is either a Voter or an Observer. Voters are full Raft partipants whereas observers can only fetch and not change voter state.

A server is a Voter if it is contained in the member set of the last configuration command in its log.

A server is an observer when it starts up from blank state or if it is not contained in the member set of the last configuration command in its log.

Transition from observer -> voter and voter -> observer can only happen via configuration commands added to a server's log.

Observers are able to keep fetching from the leader after leader elections because when leadership changes, fetches received by non-leaders are rejected reject and the response 
includes the current leader. If an observer doesn't know who the leader is then it chooses voters at random to fetch from until a voter can tell it who the leader is.

State transitions (taken from https://github.com/apache/kafka/blob/trunk/raft/src/main/java/org/apache/kafka/raft/QuorumState.java):
```
* Unattached|Resigned transitions to:
 *    Unattached: After learning of a new election with a higher epoch
 *    Voted: After granting a vote to a candidate
 *    Candidate: After expiration of the election timeout
 *    Follower: After discovering a leader with an equal or larger epoch
 *
 * Voted transitions to:
 *    Unattached: After learning of a new election with a higher epoch
 *    Candidate: After expiration of the election timeout
 *
 * Candidate transitions to:
 *    Unattached: After learning of a new election with a higher epoch
 *    Candidate: After expiration of the election timeout
 *    Leader: After receiving a majority of votes
 *
 * Leader transitions to:
 *    Unattached: After learning of a new election with a higher epoch
 *    Resigned: When shutting down gracefully
 *
 * Follower transitions to:
 *    Unattached: After learning of a new election with a higher epoch
 *    Candidate: After expiration of the fetch timeout
 *    Follower: After discovering a leader with a larger epoch
```

This specification may perform more than one transition in
one action. 
 
## Server identity - targeted for a future version

A server's identity is a composite of the host and a randomly generated disk id. The purpose of this randomly generated component is to avoid a server from participating in the cluster after being restarted without its state such as after a disk failure or volume mount misconfiguration.

When a server starts without state it generates a fresh identity. If it previously had state and a prior identity, this new identity will not match and so the peer servers will not consider it the same server and will not accept requests from it.

The only way to add a server with a new identity to the cluster is via reconfiguration.

This specification uses a global counter to produce diskIds but an implementation would use a UUID. 

Each server uses a record like the following as its identity: `[host |-> s1, diskId |-> 7]`

## Reconfiguration - targeted for a future version

KRaft implements the one-at-a-time add or remove member reconfiguration algorithm instead of the Joint Consensus algorithm. This restricts reconfiguration operations to one-at-a-time.

Please review the Raft thesis (not the paper) for a detailed description of the nuances of this reconfiguration protocol: https://web.stanford.edu/~ouster/cgi-bin/papers/OngaroPhD.pdf

Also note this bug in this thesis: https://groups.google.com/g/raft-dev/c/t4xj6dJTP6E?spm=a2c65.11461447.0.0.72ff5798NIE11G. This bug is fixed by the leader only adding reconfiguration commands once it has committed an entry in the current epoch.

Reconfigurations are performed by adding commands to the log. As soon as a server sees a reconfiguration command they immediately assume the new configuration. A reconfiguration is complete once the command gets committed. This means that a server can assume a new configuration but later revert back to the prior configuration in the case of truncating their log after a leader election.

### Adding a member

In order to avoid liveness issues, the Raft thesis recommends that new members be non-voting until they catch-up. However, this specification reverses the order by making a joinee catch-up first as an observer and then once it has done so, send a JoinRequest to the leader (an admin could do this) who will add an AddServerCommand to its log. This makes for a simpler design.

```
Admin    Joinee                            Leader
  |         |                                 |
(admin tells server to start as observer)     |
  |         |                                 |
  |         |---Fetch as an observer -------->|
  ...

(Admin sends join request)
  |---JoinRequest          ------------------>|
  |                                     (append AddServerCommand to log)
  |<---JoinResponse{ok}-----------------------|
  ...

  |         |---Fetch as an observer -------->|
  ...                                         |
  |         (receives the AddServerCommand and switches to this configuration as a voter)
  |         |---Fetch as voter -------------->|
  |                                           |
```

To be valid a JoinRequest the following conditions are required:

- request received by a leader (NotLeader error)
- the joining node cannot already be a member (AlreadyMember error)
- the leader have no in-progress reconfiguration (ReconfigInProgress error)
- the leader must have committed an offset in the current epoch. (LeaderNotReady error)

The JoinResponse is sent immediately (does not wait for the command to be committed) and is either a success response as the request met the conditions or an rejection.

In the case of a success response the joinee will continue fetching as an observer until it receives the AddServerCommand. Once received it immediately assumes the configuration, becoming a Voter follower.

If the joinee doesn't receive the command after a timeout time period it can resend the join request.

In the case of a reject response, it depends on the error:
- NotLeader: If the response contains the real leader the joinee then sends a JoinRequest to that server. If the response contains no leader id then the joinee will revert to Unattached and start fetching from voters at random until it discovers the real leader and can then send it a join request.
- AlreadyMember: treats it as a success response.
- LeaderNotReady: waits a while and retries the join request
- ReconfigInProgress: waits a while and retries the join request

### Removing a member

An administrator can send a RemoveRequest to the current leader, including the identity of the server to be removed.

```
Admin                                       Leader
   |                                          |
   |---RemoveRequest------------------------->|
   |                            (add RemoveServerCommand to log)
   |<---RemoveResponse------------------------|                                       
```

To be valid a RemoveRequest the following conditions are required:

- request received by a leader (NotLeader error)
- the leaving node must be a member of the current configuration (NotMember error).
- the leader have no in-progress reconfiguration (ReconfigInProgress error).
- the leader must have committed an offset in the current epoch. (LeaderNotReady error).

The RemoveResponse is sent immediately (does not wait for the command to be committed) and is either a success response as the request met the conditions or a rejection. In the case of a success response the administrator will need to somehow track progress of the operation. There is no guarantee it will get added as a leader election or not enough servers being up might prevent it. In the case of a rejection the Administrator can decide whether to wait or issue the command again. 

A leader may have appended a RemoveServerCommand to its log where it is the server being removed. The leader switches immediately to this new configuration where it is no longer a voter and:

- becomes an observer
- continues to be leader in order to commit the command.

While it is a non-voter leader it does not include itself in the quorum for advancing the high watermark. As soon as the command is committed the server resigns from leadership - becomes a regular observer.

Also very importantly, a voter follower that switches to the new configuration where the leader is no longer a member will still continue to send fetch requests to the leader. This is required in order for the leader to commit the command. Once the leader resigns it will reject further fetch requests. Either an election timeout will occur or a follower will receive an EndQuorumRequest from the resigned leader.

This means that removing leaders puts us in a weird situation where we have:

- an observer leader.
- voter followers fetching from an observer.
 
But as counterintuitive as this seems, it satisfies both safety and liveness properties.

In the case that the server that was removed from the configuration is not the leader, we also have a slightly counterintuitive situation in that we allow fetches from followers that consider themselves voters but which are not in the the current configuration of the leader. This can happen because the follower has still not reached the reconfiguration command that removes it. Once the follower does receive it, it will switch to being an observer. Critically, this follower may be required in order to commit the command, so if the leader did reject fetches from this follower then it might block further progress completely, resulting in a stuck cluster. This specification can demonstrate this liveness property violation if you tweak the logic to reject fetches from voters who are not in the leader's current configuration.

### Additional reconfiguration nuance

- A server can transition from observer to voter by either:
  - receiving an AddServerCommand in its log
  - truncating its log and reverting to the prior configuration where it was a member.
- A server can only start an election if it believes itself to be a voter. It can only be a voter if it is a member of the current configuration, else it would be an observer.
- A server can still do the following, even if it believes it is only an observer: 
  - participate in elections, this is because it may have switched to a new configuration where it isn't a voter but that configuration doesn't ultimately get committed. So it may in fact still be required for the cluster to make progress.
- A server cannot do the following if it is not a voter:
  - Accept a BeginQuorumRequest, it must wait until it has joined the configuration by either else it could become a leader and yet not be a member. 
- Because servers immediately switch to new configurations, they must always be prepared to revert back to the prior configuration if the command of the current configuration gets removed during a log truncation.
- How to track progress of a reconfiguration is not included in this specification but should be simple enough by querying the leader about the state of its current configuration.

## Reading the specification

The specification is split into the following files:

- network.tla: message passing and connectivity.
- kraft_kip_853_types.tla: the constants and variables.
- kraft_kip_853_functions.tla: helper functions.
- kraft_kip_853_properties.tla: invariants and liveness properties.
- kraft_kip_853.tla: actions, init and next.

You may which to start at the Next state formula section which will show you each possible action that can occur.