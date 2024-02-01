--------------------------- MODULE kraft_kip_996_types ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC,
        network

\*================================================
\* Constants and variables
\*================================================

\* The initial cluster size (the size can change over time 
\* due to reconfigurations)
CONSTANTS InitClusterSize, 
          MinClusterSize,   \* reconfigs are limited to cluster sizes >= this value
          MaxClusterSize    \* reconfigs are limited to cluster sizes <= this value

\* The set of hosts that KRaft servers are deployed on.
\* Not super important as server ids have composite ids based on
\* host and a disk id. The spec expects a value to correspond to
\* the InitClusterSize. For example, InitClusterSize=3 and
\* Hosts={h1, h2, h3}
CONSTANTS Hosts             

\* The set of values that can go be written to the log
CONSTANTS Value

\* Server roles. 
CONSTANTS Voter,   \* A full Raft participant
          Observer \* Non-voting server that can only maintain
                   \* a log replica.

\* Server states.
CONSTANTS Unattached,  \* Voter or observer, but leader unknown.
          Follower,    \* Voter or observer, leader known.
          Prospective, \* Election timeout has occurred.
          Candidate,   \* Has won a pre-vote, starts an election
          Leader,      \* Won an election
          Voted,       \* Voted in an election but does not yet know the result
          Resigned,    \* Has abdicated as leader.
          DeadNoState  \* Has died, losing all state

\* Commands
CONSTANTS AppendCommand,        \* contains a client value
          InitClusterCommand,   \* contains the initial configuration
          AddVoterCommand,      \* reconfiguration command to add a voter
          RemoveVoterCommand    \* reconfiguration command to remove a voter

\* A reserved value.
CONSTANTS Nil

\* Response codes          
CONSTANTS Ok, NotOk, Diverging

\* Errors
CONSTANTS UnknownMember, AlreadyMember, ReconfigInProgress, LeaderNotReady,
          FencedLeaderEpoch, NotLeader, UnknownLeader

\* Message types:
CONSTANTS RequestVoteRequest,
          RequestVoteResponse,
          BeginQuorumRequest,
          FetchRequest,
          FetchResponse

\* Used for filtering messages under different circumstances
CONSTANTS AnyEpoch, EqualEpoch

\* Special state that indicates a server has entered an illegal state
CONSTANTS IllegalState       

\* Limiting state space when model checking           
CONSTANTS MaxEpoch,              \* Limits the number of elections when not testing liveness.
          MaxValuesPerEpoch,     \* Limits the number of log entries per epoch.
          MaxCrashes,            \* Limits the number of crashes with loss of state.
          MaxRestarts,           \* Limits the number of restarts without loss of state
          MaxAddReconfigs,       \* Limits the number of add voter reconfigurations
          MaxRemoveReconfigs,    \* Limits the number of remove voter reconfigurations
          MaxSpawnedServers      \* Limits the number of servers ever started. 
                                 \* See readme for more details.

CONSTANTS TestLiveness  \* See the Liveness section in the readme for more details.

ASSUME MaxEpoch \in Nat
ASSUME InitClusterSize \in Nat
ASSUME MinClusterSize \in Nat
ASSUME MaxClusterSize \in Nat
ASSUME MinClusterSize <= MaxClusterSize
ASSUME InitClusterSize >= MinClusterSize
ASSUME InitClusterSize <= MaxClusterSize
ASSUME Cardinality(Hosts) >= InitClusterSize

----
\* Global variables

\* A map of numeric server id to the composite server identity.
\* The composite id is more verbose, so the spec uses 
\* numeric ids to refer to specific servers, but these numeric
\* ids correspond to the actual composite (server, disk) 
\* identities stored in this map. 
VARIABLE server_ids

----
\* Per server variables (maps whos keys are the numeric server ids).
\* These variables consitute the server-side state of the KRaft protocol.

VARIABLES config,         \* The current configuration
          current_epoch,  \* The server's epoch number (the Raft term).
          role,           \* The server's role (Voter or Observer)
          state,          \* The server's state (Follower, Candidate, Observer etc)
          voted_for,      \* The candidate the server voted for in its current epoch.
          leader,         \* The peer that the server believes is the current leader
          pending_fetch,  \* Tracks the currently pending fetch request of a follower
          pending_ack,    \* The log entries pending an ack to the client
          log,            \* A sequence of log entries that makes the Raft log.
          hwm,            \* The offset of the latest entry in the log the state machine may apply.
          votes_granted,  \* The set of servers from which the candidate has received a vote in its
                          \* current_epoch.
          flwr_end_offset \* The latest entry that each follower has acknowledged is the same as the
                          \* leader's. This is used to calculate high watermark on the leader.

\* Invariant variables. These variable are used to by the spec for invariants.
VARIABLES inv_sent,      \* The values sent and written to a leader
          inv_pos_acked, \* The values that got positively acknowledged
          inv_neg_acked  \* The values that got negatively acknowledged

\* Auxilliary variables. Used for state-space control, not part of the protocol itself.
VARIABLES aux_ctrs,       \* A set of counters used for state-space control.
          aux_disk_id_gen \* A counter used to generate a unique disk id.

\* variable groupings (useful for UNCHANGED)
logVars == <<log, hwm>>
serverVars == <<config, current_epoch, role, state, voted_for, leader, pending_fetch, pending_ack>>
candidateVars == <<votes_granted>>
leaderVars == <<flwr_end_offset>>
invVars == <<inv_sent, inv_pos_acked, inv_neg_acked >>
auxVars == <<aux_ctrs, aux_disk_id_gen>>
vars == <<server_ids, NetworkVars, serverVars, candidateVars, leaderVars, logVars,
          invVars, auxVars>>
view == <<server_ids, NetworkView, serverVars, candidateVars, leaderVars, logVars, invVars>>
livenessView == <<server_ids, NetworkView, serverVars, candidateVars,
                  leaderVars, logVars, invVars, auxVars>>

\* defines the symmetry sets
symmHosts == Permutations(Hosts)
symmHostsAndValues == Permutations(Hosts) \union Permutations(Value)

\* The sets of all possible server ids, or only those that started
AllServers == 1..MaxSpawnedServers
StartedServers == DOMAIN server_ids \* started includes ever started ie. includes dead

(* 
    The counters of aux_ctrs:
    - election_ctr         : the number of elections that have occurred.
    - value_ctr            : function of the number of values added per epoch.
    - crash_ctr            : the number of server crashes that have occurred.
    - restart_ctr          : the number of server restarts that have occurred.
    - add_reconfig_ctr     : the number of add server reconfigurations that
                             have been initiated.
    - remove_reconfig_ctr  : the number of remove server reconfigurations
                             that have been initiated.
*)

================================================