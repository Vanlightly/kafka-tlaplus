# KIP 996 - KRaft pre-vote

This specification is based on (but does not directly use) the spec of KIP-853.

Find the KIP here: https://cwiki.apache.org/confluence/display/KAFKA/KIP-996%3A+Pre-Vote
The spec may differ from the KIP as during the early work phase, this spec has uncovered issues with the KIP and the KIP may not yet be updated to reflect the current understanding.

## Basic mechanics

When a fetch or election timeout occurs, a server transitions to the Prospective state but does not increment the epoch. The Prospective sends out a pre-vote RequestVote request to its peers in the current configuration. It also votes for itself.

On receiving a pre-vote request, a server will grant a pre-vote if:
a) It is not a follower.
b) Or, it is a follower but has not made a successful fetch since becoming a follower.

When a follower grants a pre-vote, it sets the leaderId field in the response to Nil. This enables the MaybeHandleCommonResponse to remain unchanged.

When a prospective receives a positive pre-vote response, with a matching epoch, it adds the vote to its received votes. When it has received a majority vote, it increments its epoch and transitions to Candidate, and follows the regular election process from that point.

When a prospective receives a negative pre-vote, that includes a non-Nil leaderId that is not itself, it immediately transtions to a follower of that leader. If the leaderId is Nil, or indicates itself, it remains in Prospective. If it does not receive enough votes, it will start another pre=vote after an election timeout.

A prospective that has fallen behind its peers will be unable to win a pre-vote. In the case that the leader is fine and the other followers are still connected to it, the Prospective will need to give up on a pre-vote and become a regular follower. Constantly starting new pre-votes which will be rejected would leave it stuck as a Prospective. This is why the prospective will transition to follower if a peer rejects its pre-vote and knows who the leader is.

In the case that the leader is unreachable by its followers, a pre-vote will only be successful once a majority of the servers have transitioned to Prospective, or have transitioned back to Follower from Prospective but been unable to fetch. This majority will lead to an eventual successful pre-vote and an election.

The reason why a Follower which has not yet made a successful fetch can grant a pre-vote, is that otherwise, two servers could keep rejecting each others pre-votes and switching between follower and Prospective in a comedic cycle (violating liveness). Despite the leader (r1) being down, when Follower (r2) tells Prospective (r3) it knows that the leader is (r1) in a pre-vote response, the Prospective r2 transitions to Follower and resets its fetch timeout timer. Then when r2 has a fetch timeout and becomes a Prospective, r3 rejects the pre-vote saying the leader is r1. This cycle is avoided by tracking whether the follower has ever made a successful fetch since becoming a follower, if it hasn't then despite it being a follower, it will grant the pre-vote.

## Safety and liveness

This specification uses different behavior when checking safety only, and when checking both safety and liveness. When checking safety, actions such as fetch timeouts, election timeouts and check quorum resignations can occur at any time. However, when checking liveness, constant elections or resignations can actually cause liveness checks to fail as the cluster never reaches stability where replication can occur. Likewise, sometimes a resignation or election is actually required for the cluster to make progress. Therefore, when checking liveness, events such as elections and resignations only occur when there is reason for the occurrence, such as loss of connectivity or inability to receive a successful fetch response.

This liveness behavior strategy adds some complexity to the specification but has also been able to detect numerous liveness issues during the KIP design phase. Therefore, while the additional complexity is undesirable, it has become valuable enough to be worth it.

## Reading the specification

The specification is split into the following files:

- network.tla: message passing and connectivity.
- kraft_kip_996_types.tla: the constants and variables.
- kraft_kip_996_functions.tla: common functions and helper functions.
- kraft_kip_996_properties.tla: invariants and liveness properties.
- kraft_kip_996.tla: actions, init and next.

You may which to start at the Next state formula section which will show you each possible action that can occur.