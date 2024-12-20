------------------------- MODULE kafka_transactions -------------------------

EXTENDS Sequences, network

(*  
    Stage 2 - The AddPartitionsToTxnRequest and response.
    
    See README.md for commentary.
*)

\* Model parameters
CONSTANTS TxnLogPartitions,
          TopicPartitions, \* not used yet
          Brokers,
          Clients,
          TransactionIds,
          MaxTxnLogLeaderElections
          
\* Message types
CONSTANTS InitPidRequest,
          InitPidResponse,
          AddPartitionsToTxnRequest,
          AddPartitionsToTxnResponse
          
\* Client states (not part of the protocol but used to control client behavior)
CONSTANTS Ready, 
          SentInitPidRequest,
          HasPid,
          BegunTxn,
          Terminated \* See readme for discussion on this.

\* TxnStates
CONSTANT Empty, PrepareCommit, PrepareAbort,
         CompleteAbort, CompleteCommit, Ongoing, 
         PrepareEpochFence, Dead

\* TxnResults         
CONSTANTS Abort, Commit

\* Errors (not all are used yet)
CONSTANTS IllegalState, OK, NotCoordinator, 
          ConcurrentTransactions, ProducerFenced, 
          InvalidTransition, NotSupportedYet,
          InvalidProducerIdMapping  

\* Other constants
CONSTANTS None

\* Client state. A map of client_id -> client state.
VARIABLES client 

\* Transaction coordinator state, each is a map of broker_id -> some state         
VARIABLES tc_tid_metadata,   \* per TID txn state
          tc_tid_transition, \* per TID txn transition state
          tc_log,            \* txn log partition_id -> the partition data
          tc_log_metadata,   \* txn log partition_id -> the partition metadata
          tc_log_hwm         \* txn log partition_id -> high watermark

\* Regular topic partitions (not used yet)
VARIABLES topic_partitions

\* KRaft controller metadata state
VARIABLES txn_log_leader,    \* a map of txn log partition_id -> the leader aka the TC
          txn_log_epoch      \* a map of txn log partition_id -> the partition epoch,
                             \* also known as coordinator epoch.

\* Auxilliary variables          
VARIABLES aux_coord_ctr,     \* counts the number of coordinator changes
          pid_source,        \* a unique source of PIDs
          t_to_p_mapping     \* a mapping of TID to partition (static in this version)
                             \* i.e. partition leadership is static.

tc_tid_vars == <<tc_tid_metadata, tc_tid_transition>>
tc_log_vars == << tc_log, tc_log_hwm, tc_log_metadata >>
txn_log_vars == << txn_log_leader, txn_log_epoch >>
aux_vars == <<pid_source, t_to_p_mapping, aux_coord_ctr>>
topic_vars == <<topic_partitions>>
vars == <<client, tc_tid_vars, tc_log_vars, txn_log_vars, topic_vars, aux_vars, net_vars>>

View == <<client, tc_tid_vars, tc_log_vars, txn_log_vars, topic_vars, pid_source, t_to_p_mapping, NetworkView>>
SymmetryClients == Permutations(Clients)
SymmetryBrokers == Permutations(Brokers)
SymmetryPartitions == Permutations(TxnLogPartitions)
SymmetryTids == Permutations(TransactionIds)
Symmetry == SymmetryClients 
                \union SymmetryBrokers 
                \union SymmetryPartitions
                \union SymmetryTids

\* ----------------------------------------------
\* Types and state machine transitions
\* ----------------------------------------------

\* Valid previous txn states
ValidPrevTxnStates(state) ==
    CASE state = Empty             -> {None, Empty, CompleteCommit, CompleteAbort}
      [] state = Ongoing           -> {Ongoing, Empty, CompleteCommit, CompleteAbort}
      [] state = PrepareCommit     -> {Ongoing}
      [] state = PrepareAbort      -> {Ongoing, PrepareEpochFence}
      [] state = CompleteCommit    -> {PrepareCommit}
      [] state = CompleteAbort     -> {PrepareAbort}
      [] state = Dead              -> {Empty, CompleteCommit, CompleteAbort}
      [] state = PrepareEpochFence -> {Ongoing}
      [] OTHER -> {InvalidTransition}

InitPidRequestType ==
    [type: {InitPidRequest},
     tid: TransactionIds,
     dest: Brokers,
     source: Clients]
     
InitPidResponseType ==
    [type: {InitPidResponse},
     code: {OK, ConcurrentTransactions, NotCoordinator},
     pid: Nat \union {-1},
     pepoch: Nat \union {-1},
     dest: Clients,
     source: Brokers]

AddPartitionsToTxnRequestType ==
    [type: {AddPartitionsToTxnRequest},
     tid: TransactionIds,
     pid: Nat,
     pepoch: Nat,
     partitions: SUBSET TopicPartitions,
     dest: Brokers,
     source: Clients]
     
AddPartitionsToTxnResponseType ==
    [type: {AddPartitionsToTxnResponse},
     code: {OK, ConcurrentTransactions, NotCoordinator, 
            ProducerFenced, InvalidProducerIdMapping},
     partitions: SUBSET TopicPartitions,
     dest: Clients,
     source: Brokers]
     
MessageType ==
    InitPidRequestType \union InitPidResponseType
    \union AddPartitionsToTxnRequestType
    \union AddPartitionsToTxnResponseType   

\* Common helpers start --------------------

\* Will trip the invariant that checks for an IllegalState message
SetIllegalState ==
    Send([code |-> IllegalState])
    
CurrentTC(p) == txn_log_leader[p]

\* Common helpers end --------------------

\* ----------------------------------------------
\* The client
\* ----------------------------------------------

\* Client helpers start --------------------

\* This is an atomic FindCoordinatorRequest implementation.
FindCoordinator(tid) ==
    LET p == t_to_p_mapping[tid]
    IN CurrentTC(p)

\* Client helpers end --------------------

(* ---------------------------------------------------------------
   ACTION: SendInitPidRequest
   WHO: A client
   
   A client sends an InitPidRequest to the current TC of the partition
   that this TID is associated with.
   
   If the client has to TransactionId (tid) then one is non-deterministically
   chosen, else its existing one is reused.
*)

SendInitPidRequest(c) ==
    (* Enabling conditions *)
    /\ client[c].state = Ready
    /\ \E tid \in TransactionIds :
        \* If this is a retry, then reuse the same tid, else use whichever.
        /\ IF client[c].tid # None THEN tid = client[c].tid ELSE TRUE
        (* State mutations *)
        /\ Send([type |-> InitPidRequest,
                 tid  |-> tid,
                 dest |-> FindCoordinator(tid),
                 source |-> c])
        /\ client' = [client EXCEPT ![c].tid = tid,
                                    ![c].state = SentInitPidRequest]
    /\ UNCHANGED << tc_tid_vars, tc_log_vars, txn_log_vars, topic_vars, aux_vars >>

(* ---------------------------------------------------------------
   ACTION: ReceiveInitPidResponse
   WHO: A client
   
   A client receives an InitPidResponse. If it is an OK response,
   then it updates its PID and epoch, and transitions to the HasPid state.
   These states are not part of the protocol, but used for implementing
   the client as a state machine.
   
   If the response is an error, then the client reverts back to Ready, where
   it can retry the InitPidRequest.
*)

ReceiveInitPidResponse(c, b) ==
    (* Enabling conditions *)
    /\ client[c].state = SentInitPidRequest
    /\ \E msg \in messages : 
        /\ msg.dest = c
        /\ msg.source = b
        /\ msg.type = InitPidResponse
        (* State mutations *)
        /\ IF msg.code = OK
           THEN client' = [client EXCEPT ![c].state = HasPid,
                                         ![c].tc = msg.source,
                                         ![c].pid = msg.pid,
                                         ![c].epoch = msg.pepoch]
           ELSE \* go back to Ready state to try again
                client' = [client EXCEPT ![c].state = Ready,
                                         ![c].last_state = client[c].state,
                                         ![c].last_error = msg.code]
        /\ Discard(msg)
    /\ UNCHANGED << tc_tid_vars, tc_log_vars, txn_log_vars, topic_vars, aux_vars >>


(* ---------------------------------------------------------------
   ACTION: SendAddPartitionsToTxnRequest
   WHO: A client
   
   A client that has obtained a PID intends to produce to a 
   topic partition first adds the topic partition to the 
   transaction by sending an AddPartitionsToTxnRequest to 
   the transaction controller.
*)

SendAddPartitionsToTxnRequest(c) ==
    (* Enabling conditions *)
    /\ client[c].state \in { HasPid, BegunTxn }
    /\ client[c].pending_partitions = {}
    /\ \E p \in TopicPartitions :
        /\ p \notin client[c].partitions
        (* State mutations *)
        /\ Send([type       |-> AddPartitionsToTxnRequest,
                 tid        |-> client[c].tid,
                 pid        |-> client[c].pid,
                 pepoch     |-> client[c].epoch,
                 partitions |-> {p}, \* one partition for now
                 dest       |-> client[c].tc,
                 source     |-> c])
        /\ client' = [client EXCEPT ![c].pending_partitions = {p},
                                    ![c].state = BegunTxn]
    /\ UNCHANGED << tc_tid_vars, tc_log_vars, txn_log_vars, topic_vars, aux_vars >>


(* ---------------------------------------------------------------
   ACTION: ReceiveAddPartitionsToTxnResponse
   WHO: A client
   
   A client receives a AddPartitionsToTxnResponse.
   
   On a success response, the client adds the partition to
   the set of partitions added to the txn.
   
   On a retriable error response (ConcurrentTransactions, NotCoordinator),
   the client remains in the same state so it can try again. If the error
   was NotCoordinator, it performs a FindCoordinator request to learn of
   the current coordinator.
   
   On any other error the client shutsdown and does not attempt any further
   interactions. This is in order to prevent an infinite state space and 
   support liveness properties. The alternative is to limit the producer epoch
   but this can actually result in failed liveness as a new epoch may be required
   in order for certain liveness properties to be fulfilled. This is the
   "Control the stones (perturbations), not the ripples (recovery)" principle
   I wrote about: https://jack-vanlightly.com/blog/2023/10/10/the-importance-of-liveness-properties-part-2
*)

ReceiveAddPartitionsToTxnResponse(c, b) ==
    (* Enabling conditions *)
    /\ client[c].state = BegunTxn
    /\ \E msg \in messages : 
        /\ msg.dest = c
        /\ msg.source = b
        /\ msg.type = AddPartitionsToTxnResponse
        (* State mutations *)
        /\ CASE msg.code = OK ->
                    client' = [client EXCEPT ![c].pending_partitions = @ \ msg.partitions,
                                             ![c].partitions = @ \union msg.partitions]
             [] msg.code \in {ConcurrentTransactions, NotCoordinator} ->
                    \* Retriable error, so may be try again
                    client' = [client EXCEPT ![c].pending_partitions = {},
                                             ![c].last_state = client[c].state,
                                             ![c].last_error = msg.code,
                                             ![c].tc = IF msg.code = NotCoordinator
                                                       THEN FindCoordinator(client[c].tid)
                                                       ELSE client[c].tc]
             [] OTHER ->
                    \* Some non-retriable error such as ProducerFenced. Go to the
                    \* Terminated state to prevent an infinite battle (and infinite
                    \* state space) with another client.  
                    client' = [client EXCEPT ![c].state = Terminated,
                                             ![c].last_state = client[c].state,
                                             ![c].last_error = msg.code,
                                             ![c].pending_partitions = {},
                                             ![c].partitions = {}]
        /\ Discard(msg)
    /\ UNCHANGED << tc_tid_vars, tc_log_vars, txn_log_vars, topic_vars, aux_vars >>

\* ----------------------------------------------
\* The transaction coordinator actions
\* ----------------------------------------------

\* COMMON HELPERS START --------------------------------------

PartitionFor(tid) == t_to_p_mapping[tid]
PartitionMetadataOf(b, partition) == tc_log_metadata[b][partition]
PartitionMetadataOfTid(b, tid) == PartitionMetadataOf(b, PartitionFor(tid))

CurrentTransition(b, tid) ==
    tc_tid_transition[b][tid]

IsPartitionLeader(b, p) ==
    b = tc_log_metadata[b][p].leader

\* Return any cached metadata of the transaction of this TID.
\* If not the active TC, return NotCoordinator, else if there is a
\* cached metadata return it, else generate new metadata.
GetTxnMetadata(b, tid) ==
    CASE ~IsPartitionLeader(b, PartitionFor(tid)) -> 
            [code |-> NotCoordinator] 
      [] tc_tid_metadata[b][tid] = None -> 
            [code |-> None]
      [] OTHER->
            [code         |-> OK,
             txn_metadata |-> tc_tid_metadata[b][tid],
             cepoch       |-> PartitionMetadataOfTid(b, tid).cepoch]

\* Generate new txn metadata for this transition, but check it is a valid transition.
GenTransition(b, curr_transition, curr_state, new_state, pid, 
              new_pepoch, new_last_pepoch, new_partitions) ==
    CASE 
      \* CASE 1 - Reject because an existing transition is currently being committed.
         curr_transition # None ->
            [code |-> ConcurrentTransactions]
      \* CASE 2 - Accept as this is a valid transition
      [] curr_state \in ValidPrevTxnStates(new_state) ->
             \* Create a modified txn metadata transitioned to the new state
            [code        |-> OK,
             transition  |-> [pid         |-> pid, 
                              pepoch      |-> new_pepoch, 
                              last_pepoch |-> new_last_pepoch,
                              state       |-> new_state,
                              partitions  |-> new_partitions]]
      \* CASE 3 - This shouldn't happen. 
      [] OTHER -> 
            \* Shouldn't get here
            [code |-> InvalidTransition]

\* Generate the metadata for transitioning to the CompleteAbort or CompleteCommit state.
GenCompleteTransition(b, tid, txn_metadata) ==
    LET next_state == IF txn_metadata.state = PrepareCommit 
                      THEN CompleteCommit ELSE CompleteAbort
    IN GenTransition(b, None, \* clear the current pending transition to avoid an error 
                      txn_metadata.state,      \* current state
                      next_state,              \* transition to CompleteAbort or CompleteCommit
                      txn_metadata.pid,        \* same pid (no exhaustion)
                      txn_metadata.pepoch,      
                      txn_metadata.last_pepoch,      
                      txn_metadata.partitions) \* no partitions change

ClearTransition(b, tid) ==
    tc_tid_transition' = [tc_tid_transition EXCEPT ![b][tid] = None]

\* Append a txn log entry to the local leader's log and set the pending transition.
LocalTxnLogEntryAppend(b, p, tid, log, transition, callback) ==
    /\ tc_log' = [log EXCEPT ![b][p] = 
                        Append(@, [tid        |-> tid,
                                   transition |-> transition,
                                   callback   |-> callback])]
    /\ tc_tid_transition' = [tc_tid_transition EXCEPT ![b][tid] = transition]

\* COMMON HELPERS END --------------------------------------

(* ---------------------------------------------------------------
   ACTION: ElectLeader
   WHO: Transaction controller
   
   A TC that acts as the log partition follower gets promoted to 
   leader by the KRaft controller, with a bumped coordinator
   epoch (for that partition).
   
   It must materialize all txn metadata based on the txn log partition.
*)

\* You would materialize txn state based on the log, but
\* that is quite ugly code, instead the simpler equivalent
\* is to copy the state of the current TC for the partition
\* (that is getting demoted).
MaterializeState(tid) ==
    LET p  == PartitionFor(tid)
        b == CurrentTC(p) \* TC in current state is the original
    IN tc_tid_metadata[b][tid]

ElectLeader(b, p) ==
    (* Enabling conditions *)
    /\ aux_coord_ctr < MaxTxnLogLeaderElections
    /\ b # tc_log_metadata[b][p].leader
    (* State mutations *)
    \* Bump the coordinator epoch of the partition leadership that is moving to
    \* to this TC.
    /\ LET cepoch == txn_log_epoch[p] + 1
       IN
          \* Controller elects the new leader and bump the txn log partition epoch
          /\ txn_log_leader' = [txn_log_leader EXCEPT ![p] = b]
          /\ txn_log_epoch' = [txn_log_epoch EXCEPT ![p] = cepoch]
          \* The new leader updates its txn log partition metadata with the new epoch.
          /\ tc_log_metadata' = [tc_log_metadata EXCEPT ![b][p] =
                                        [cepoch |-> cepoch,
                                         leader |-> b]]
          \* Materialize the txn metadata stored by this txn log partition
          /\ tc_tid_metadata' = [tc_tid_metadata EXCEPT ![b] =
                                    [tid \in TransactionIds |->
                                        IF PartitionFor(tid) = p
                                        THEN MaterializeState(tid)
                                        ELSE None]]
          /\ aux_coord_ctr' = aux_coord_ctr + 1
          /\ UNCHANGED <<tc_tid_transition, tc_log, tc_log_hwm, client,
                         topic_vars, pid_source, t_to_p_mapping, net_vars>>

(* ---------------------------------------------------------------
   ACTION: CompletePartialTxn
   WHO: Transaction controller
   
   After becoming the active TC for a partition, there may be TIDs that
   had a committed PrepareAbort/Commit, but no CompleteAbort/Commit
   (as the process was interrupted).
   
   This is identified in this spec by seeing that the materialized
   txn metadata is in the Prepare phase, but there is no transition
   in progress (this can only happen after being made leader/active TC).
   
   This action ensures that the complete phase gets kicked off.
*)

CompletePartialTxn(b, tid) ==
    LET p            == PartitionFor(tid)
        txn_metadata == tc_tid_metadata[b][tid]
        trans_result == GenCompleteTransition(b, tid, txn_metadata)
        callback     == [type     |-> trans_result.transition.state,
                         response |-> None, 
                         err      |-> None]
    IN 
        (* Enabling conditions *)
        /\ IsPartitionLeader(b, p)
        /\ txn_metadata # None 
        /\ txn_metadata.state \in {PrepareAbort, PrepareCommit} \* Prepare in-progress
        /\ tc_tid_transition[b][tid] = None \* but no current transition
        /\ trans_result.code = OK
        (* State mutations *)
        /\ LocalTxnLogEntryAppend(b, p, tid, tc_log, 
                                  trans_result.transition, 
                                  callback)
        /\ UNCHANGED <<tc_tid_metadata, tc_log_hwm, tc_log_metadata, 
                       txn_log_vars, topic_vars, client, aux_vars, net_vars>>
    
(* ---------------------------------------------------------------
   ACTION: BecomeFollower
   WHO: Transaction controller
   
   A transaction coordinator gets demoted to a follower by the KRaft
   Controller (that just elected a different TC as replica leader).
   
   The callbacks of any pending transitions must get executed using
   the stored error response. The pending transitions are those that
   are in the uncommitted txn log entries.
   
   As per the Kafka replication protocol, this replica ensures that its
   log is truncated to match the leader (if it was ahead).
*)

MaybeTruncateLog(b, p) ==
    [offset \in 1..tc_log_hwm[b][p] |-> tc_log[b][p][offset]]

RemoveNoneResponses(responses) ==
    { r \in responses : r # None }

StaleLeader(b, p) ==
    /\ tc_log_metadata[b][p].cepoch < txn_log_epoch[p]
    /\ b = tc_log_metadata[b][p].leader
    /\ b # txn_log_leader[p]
    
BecomeFollower(b, p) ==
    (* Enabling conditions *)
    /\ StaleLeader(b, p)
    (* State mutations *)
    /\ LET first_uncommitted_offset == tc_log_hwm[b][p]+1
           uncommitted_offsets == first_uncommitted_offset..Len(tc_log[b][p])
           uncommitted_entries == { tc_log[b][p][offset] : offset \in uncommitted_offsets } 
           err_responses == { entry.callback.err : entry \in uncommitted_entries }
       IN
          \* Update local log state (truncates the log to match the leader)
          /\ tc_log_metadata' = [tc_log_metadata EXCEPT ![b][p] =
                                        [cepoch |-> txn_log_epoch[p],
                                         leader |-> txn_log_leader[p]]]
          /\ tc_log' = [tc_log EXCEPT ![b][p] = MaybeTruncateLog(b, p)]
          /\ UNCHANGED tc_log_hwm
          \* Clear out txn state of the affected tids
          /\ tc_tid_metadata' = [tc_tid_metadata EXCEPT ![b] =
                                        [tid \in TransactionIds |->
                                            IF PartitionFor(tid) = p
                                            THEN None
                                            ELSE tc_tid_metadata[b][tid]]]
          \* Clear out txn pending transitions of the affected tids
          /\ tc_tid_transition' = [tc_tid_transition EXCEPT ![b] =
                                        [tid \in TransactionIds |->
                                            IF PartitionFor(tid) = p
                                            THEN None
                                            ELSE tc_tid_transition[b][tid]]]
          
          \* Send error responses for pending ops
          /\ SendAll(RemoveNoneResponses(err_responses))
          /\ UNCHANGED << tc_log_hwm, txn_log_vars, topic_vars, client, aux_vars>>
    
(* ---------------------------------------------------------------
   ACTION: ReceiveInitPidRequest
   WHO: Transaction controller
   
   A TC receives an InitPidRequest.
   
   The TC returns an error response immediately if:
    - This TC is not the leader of the txn log partition (NotCoordinator).
    - A txn metadata transition is in progress (ConcurrentTransactions).
   
   If there is no existing metadata for this TID, then it generates 
   new metadata, with a unique ProducerId (PID) and a Producer Epoch 
   (pepoch) of -1.
        
   It generates a metadata transition to Empty state, with an incremented
   pepoch. If the metadata was just created, this increments it from -1 to 0. 
   
   It writes the transition metadata, as well as callback data, to the
   txn log partition. This callback data will later be used to send a response
   to the client. 
*)

GetOrCreateTxnMetadata(b, tid) ==
    LET cached_md == GetTxnMetadata(b, tid)
    IN
        IF cached_md.code = None 
        THEN \* Generate new metadata.
             [code         |-> OK,
              txn_metadata |-> [pid           |-> pid_source + 1, 
                                last_pid      |-> -1,
                                pepoch        |-> -1, 
                                last_pepoch   |-> -1,
                                state         |-> Empty, 
                                partitions    |-> {}],
              cepoch       |-> PartitionMetadataOfTid(b, tid).cepoch]
        ELSE cached_md

\* Generate txn metadata for the transition to Empty
GenInitPidTransition(b, tid, txn_metadata) ==
    CASE 
      \* CASE 1 - There is no ongoing txn, so generate a transition to Empty.
         txn_metadata.state \in { CompleteAbort, CompleteCommit, Empty } ->
            GenTransition(b, CurrentTransition(b, tid), 
                          txn_metadata.state,   \* current state
                          Empty,                \* transition to Empty
                          txn_metadata.pid,     \* the pid (no exhaustion modeled)
                          txn_metadata.pepoch + 1, \* new pepoch (incremented) 
                          txn_metadata.pepoch,     \* last pepoch
                          {}) \* no partitions yet
      \* CASE 2 - There is an ongoing transaction. Abort the ongoing transaction
      \*          first, by fencing the producer. Once the producer has been fenced, a
      \*          response to this request can be sent and the txn abort carried out
      \*          asynchronously.
      [] txn_metadata.state = Ongoing ->
            GenTransition(b, CurrentTransition(b, tid), 
                          txn_metadata.state,   \* current state
                          PrepareEpochFence,    \* transition to PrepareEpochFence
                          txn_metadata.pid,     \* same pid (no exhaustion)
                          txn_metadata.pepoch + 1, \* bump the pepoch 
                          -1, \* don't know why yet     
                          txn_metadata.partitions) \* no partitions change
      \* CASE 3 - The current txn is getting aborted or committed, so return a retriable error
      \*          so that the producer can try again soon.
      [] txn_metadata.state \in { PrepareAbort, PrepareCommit } ->
            [code |-> ConcurrentTransactions]
      \* CASE 4 - Not implemented yet.
      [] OTHER -> 
            \* Shouldn't get here
            [code |-> IllegalState]
            
MakePidResponse(b, c, code, pid, pepoch) ==
    [type   |-> InitPidResponse,
     code   |-> code,
     pid    |-> pid,
     pepoch |-> pepoch,
     dest   |-> c,
     source |-> b]
     
MakeErrorPidResponse(b, c, code) ==
    MakePidResponse(b, c, code, -1, -1)

\* Generate txn metadata for a transition to PrepareAbort or PrepareCommit
GenPrepareAbortOrCommitTransition(b, tid, curr_metadata, new_metadata, next_state) ==
    GenTransition(b, CurrentTransition(b, tid), 
                  curr_metadata.state,     \* current state
                  next_state,              \* transition to PrepareAbort or PrepareCommit
                  new_metadata.pid,        \* same pid (no exhaustion)
                  new_metadata.pepoch,     \* TODO: client support for bump pepoch? 
                  new_metadata.last_pepoch,      
                  curr_metadata.partitions) \* no partitions change

\* Transition to PrepareCommit or PrepareAbort
EndTransaction(msg, b, c, curr_metadata, new_metadata, 
               partition, txn_result, is_from_client) ==
    CASE 
      \* CASE 1 - Bad epoch (currently modeled spec can't reach this yet)  
         \/ (is_from_client /\ new_metadata.pepoch # curr_metadata.pepoch)
         \/ new_metadata.pepoch < curr_metadata.pepoch ->
            /\ Reply(msg, MakeErrorPidResponse(b, c, ProducerFenced))
            /\ UNCHANGED << tc_tid_transition >>
      \* CASE 2 - The txn is ongoing, so kick-off the complete phase.
      [] curr_metadata.state = Ongoing ->
            LET next_state   == IF txn_result = Abort THEN PrepareAbort ELSE PrepareCommit
                trans_result == IF next_state = PrepareAbort /\ new_metadata.state = PrepareEpochFence
                                THEN GenPrepareAbortOrCommitTransition(b, msg.tid, curr_metadata, 
                                                                       new_metadata, next_state)
                                ELSE None
                callback     == [type     |-> next_state,
                                 response |-> MakePidResponse(b, c, ConcurrentTransactions, -1, -1),
                                 err      |-> MakeErrorPidResponse(b, c, NotCoordinator)]
            IN  /\ Discard(msg) \* We'll reply once the transition is complete
                /\ LocalTxnLogEntryAppend(b, partition, msg.tid, tc_log, 
                                          trans_result.transition, callback)
      \* CASE 3 - Not implemented yet
      [] OTHER -> 
            \* Shouldn't get here
            /\ Reply(msg, MakeErrorPidResponse(b, c, IllegalState))
            /\ UNCHANGED << tc_tid_transition, tc_log >>
                 
\* The action
ReceiveInitPidRequest(b, c) ==
    (* Enabling conditions *)
    \E msg \in messages :
        /\ msg.dest = b
        /\ msg.source = c
        /\ msg.type = InitPidRequest
        (* State mutations *)
        /\ LET md_result    == GetOrCreateTxnMetadata(b, msg.tid)
               new_pid      == IF md_result.code = OK THEN md_result.txn_metadata.pid ELSE pid_source \* else no change
               txn_metadata == IF md_result.code = OK THEN md_result.txn_metadata ELSE tc_tid_metadata[b][msg.tid] \* else no change
               trans_result == GenInitPidTransition(b, msg.tid, md_result.txn_metadata)
               partition    == PartitionFor(msg.tid)
               callback     == [type     |-> InitPidRequest,
                                response |-> MakePidResponse(b, c, OK,
                                                             trans_result.transition.pid,
                                                             trans_result.transition.pepoch), 
                                err      |-> MakeErrorPidResponse(b, c, NotCoordinator)]
           IN 
                /\ pid_source' = new_pid \* no change in case of error
                /\ tc_tid_metadata' = [tc_tid_metadata EXCEPT ![b][msg.tid] = txn_metadata] \* no change in case of error
                /\ CASE 
                     \* CASE 1 - Error retrieving txn metadata   
                        md_result.code # OK ->
                            /\ Reply(msg, MakeErrorPidResponse(b, c, md_result.code))
                            /\ UNCHANGED <<tc_tid_transition, tc_log>>
                     \* CASE 2 - Error generating the transition
                     [] trans_result.code # OK ->
                            /\ Reply(msg, MakeErrorPidResponse(b, c, trans_result.code))
                            /\ UNCHANGED << tc_tid_transition, tc_log >>
                     \* CASE 3 - Need to fence the current producer and abort its txn
                     [] trans_result.transition.state = PrepareEpochFence ->
                            EndTransaction(msg, b, c, 
                                           md_result.txn_metadata, 
                                           trans_result.transition, 
                                           partition,
                                           Abort, FALSE)
                     \* CASE 4 - All ok, write the transition to the local txn log partition
                     [] OTHER ->    
                            /\ Discard(msg) \* We'll reply once the transition is complete
                            /\ LocalTxnLogEntryAppend(b, partition, msg.tid, tc_log,
                                                      trans_result.transition,
                                                      callback)
        /\ UNCHANGED << client, tc_log_hwm, tc_log_metadata, txn_log_vars,
                        topic_vars, t_to_p_mapping, aux_coord_ctr >>

(* ---------------------------------------------------------------
   ACTION: ReceiveAddPartitionsToTxnRequest
   WHO: Transaction controller
   
   The transaction coordinator receives an AddPartitionsToTxnRequest.
   
   If all checks pass, then write a log entry to the txn log partition,
   with the transition to Ongoing with the added partitions.
*)

MakeAddPartsResponse(b, c, code, partitions) ==
    [type       |-> AddPartitionsToTxnResponse,
     code       |-> code,
     partitions |-> partitions,
     dest       |-> c,
     source     |-> b]

ReplyWithError(msg, b, c, error) ==
    /\ Reply(msg, MakeAddPartsResponse(b, c, error, {}))
    /\ UNCHANGED << tc_tid_transition, tc_log >>
                
\* Generate txn metadata for a transition to Ongoing with the
\* added topic partition.                 
GenAddPartitionsTransition(b, tid, txn_metadata, add_partitions) ==
    GenTransition(b, CurrentTransition(b, tid), 
                  txn_metadata.state, \* the current state 
                  Ongoing,            \* transition to ONGOING
                  txn_metadata.pid,
                  txn_metadata.pepoch, 
                  txn_metadata.last_pepoch, 
                  txn_metadata.partitions \union add_partitions)

ReceiveAddPartitionsToTxnRequest(b, c) ==
    (* Enabling conditions *)
    \E msg \in messages :
        /\ msg.dest = b
        /\ msg.source = c
        /\ msg.type = AddPartitionsToTxnRequest
        (* State mutations *)
        /\ LET md_result    == GetTxnMetadata(b, msg.tid)
               trans_result == GenAddPartitionsTransition(b, msg.tid,
                                                          md_result.txn_metadata,
                                                          msg.partitions)
               partition    == PartitionFor(msg.tid)
               callback     == [type     |-> AddPartitionsToTxnRequest,
                                response |-> MakeAddPartsResponse(b, c, OK, trans_result.transition.partitions),
                                err      |-> MakeAddPartsResponse(b, c, NotCoordinator, {})]
           IN
              CASE md_result.code = None ->
                        ReplyWithError(msg, b, c, InvalidProducerIdMapping)
                [] md_result.code = NotCoordinator ->
                        ReplyWithError(msg, b, c, NotCoordinator)
                [] msg.pid # md_result.txn_metadata.pid ->
                        ReplyWithError(msg, b, c, InvalidProducerIdMapping)
                [] msg.pepoch # md_result.txn_metadata.pepoch -> 
                        ReplyWithError(msg, b, c, ProducerFenced)
                [] tc_tid_transition[b][msg.tid] # None ->
                        ReplyWithError(msg, b, c, ConcurrentTransactions)
                [] md_result.txn_metadata.state \in {PrepareCommit, PrepareAbort} ->
                        ReplyWithError(msg, b, c, ConcurrentTransactions)
                [] trans_result.code # OK ->
                        ReplyWithError(msg, b, c, trans_result.code)
                [] OTHER ->
                        /\ Discard(msg) \* We'll reply once the transition is complete
                        /\ LocalTxnLogEntryAppend(b, partition, msg.tid, tc_log,
                                                  trans_result.transition, callback)
        /\ UNCHANGED <<tc_tid_metadata, tc_log_hwm, tc_log_metadata, txn_log_vars, 
                       topic_vars, client, aux_vars>>
                
(* ---------------------------------------------------------------
   ACTION: TxnLogAppendCommits
   WHO: Transaction controller
   
   This action performs two things:
     1. The next uncommitted txn log entry of the txn log partition 
        gets replicated and committed. 
     2. The associated callback is executed.
   
   TLA+ cannot do asynchronous callbacks like a programming language. 
   Therefore, in this spec, the callback data is stored in the log entry  
   and a set of handlers execute the required callback functionality.
      
   Note that the NotCoordinator logic of callbacks is handled in 
   the BecomeFollower action.
*)

\* (1) Replication ---------

\* The HWM advances on all txn log partition replicas.
AdvanceLogHwm(b, p, offset) ==
    tc_log_hwm'   = [bb \in Brokers |->
                        [tc_log_hwm[bb] EXCEPT ![p] = offset]]

\* TRUE/FALSE, the log entry *can* get replicated and committed. The Kafka 
\* replication protocol is grossly simplified here. If the broker is still 
\* the TC and all replicas are on the same partition epoch (aka coordinator
\* epoch) then return true. 
CanCommit(b, p) ==
    /\ b = CurrentTC(p)
    /\ \A bb \in Brokers :
        tc_log_metadata[bb][p].cepoch = tc_log_metadata[b][p].cepoch 

\* In this gross Kafka replication protocol simplification, the log entry,
\* so far only written to the TC's local log, gets replicated to all followers.
LogAfterReplication(b, p, entry) ==
    [bb \in Brokers |->
        IF bb # b 
        THEN [tc_log[bb] EXCEPT ![p] = Append(@, entry)]
        ELSE tc_log[b]]
        
\* (2) Callback handlers ---------

\* Callback code of the commit of a PrepareAbort or PrepareCommit log entry
HandlePrepareAbortOrCommit(b, p, log_after_rep, entry) ==
    \* TODO: Check validations in TransactionMetadata.scala completeTransitionTo
    \* Start a new transition to complete the commit/abort.
    LET result   == GenCompleteTransition(b, entry.tid, entry.transition)
        callback == [type     |-> result.transition.state,
                     response |-> None, 
                     err      |-> None]
    IN IF result.code = OK
        \* The *new* transition is ok so append it and send the response now.
        \* Note we don't store a response for the new transition, as we already respond now. 
       THEN /\ LocalTxnLogEntryAppend(b, p, entry.tid, log_after_rep, 
                                      result.transition,
                                      callback)
            /\ Send(entry.callback.response)
       \* The *new* transition is not ok so don't append it, and send the response with the updated error code
       ELSE LET response == [entry.callback.response EXCEPT !.code = result.code]
            IN /\ tc_log' = log_after_rep
               /\ ClearTransition(b, entry.tid)
               /\ Send(response)

\* Callback code of the commit of a CompleteAbort or CompleteCommit log entry
HandleCompleteAbortOrCommit(b, log_after_rep, entry) ==
    \* TODO: Check validations in TransactionMetadata.scala completeTransitionTo
    \* TODO: Advance the LSO (not modeled yet)
    \* TODO: Write txn markers (not modeled yet)
    /\ tc_log' = log_after_rep
    /\ ClearTransition(b, entry.tid)
    /\ UNCHANGED <<messages, messages_discard>>

\* Callback code of the commit of an Empty transition log entry
HandleInitPid(b, log_after_rep, entry) ==
    \* TODO: Check validations in TransactionMetadata.scala completeTransitionTo
    /\ tc_log' = log_after_rep
    /\ ClearTransition(b, entry.tid)
    /\ Send(entry.callback.response)

\* Callback code of the commit of an Ongoing (add parts) transition log entry    
HandleAddPartitions(b, p, log_after_rep, entry) ==
    \* TODO: Check validations in TransactionMetadata.scala completeTransitionTo
    /\ tc_log' = log_after_rep
    /\ ClearTransition(b, entry.tid)
    /\ Send(entry.callback.response)

SetTxnMetadata(b, tid, transition) ==
    tc_tid_metadata' = [tc_tid_metadata EXCEPT ![b][tid] = transition]

\* The action
CommitTxnLogAppend(b, p) ==
    (* Enabling conditions *)
    \* There is an uncommitted log entry 
    /\ tc_log_hwm[b][p] < Len(tc_log[b][p])
    /\ CanCommit(b, p)
    (* State mutations *)
    /\ LET next_offset   == tc_log_hwm[b][p] + 1 
           entry         == tc_log[b][p][next_offset]
           log_after_rep == LogAfterReplication(b, p, entry)
       IN 
          /\ AdvanceLogHwm(b, p, next_offset)
          /\ SetTxnMetadata(b, entry.tid, entry.transition)
          /\ CASE entry.callback.type \in {PrepareAbort, PrepareCommit } ->
                      HandlePrepareAbortOrCommit(b, p, log_after_rep, entry)
               [] entry.callback.type \in {CompleteAbort, CompleteCommit } ->
                      HandleCompleteAbortOrCommit(b, log_after_rep, entry)
               [] entry.callback.type = InitPidRequest ->
                      HandleInitPid(b, log_after_rep, entry)
               [] entry.callback.type = AddPartitionsToTxnRequest ->
                      HandleAddPartitions(b, p, log_after_rep, entry)
               [] OTHER -> SetIllegalState
    /\ UNCHANGED << client, txn_log_vars, tc_log_metadata, topic_vars, aux_vars >>
                
\* ----------------------------------------------
\* Invariants
\* ----------------------------------------------

\* Currently only checks that messages are valid.
TypeOK ==
    /\ \A m \in messages :
        m \in MessageType

\* Catch any IllegalState or InvalidTransition
NoBadStateResponse ==
    ~\E msg \in messages :
        \/ /\ msg.type = InitPidResponse
           /\ msg.code \in {IllegalState, InvalidTransition}

\* It is illegal for two clients to be given the same PID with the same
\* producer epoch
ClientsHaveDifferentProducerEpochs ==
    ~\E ct1, ct2 \in Clients :
        /\ ct1 # ct2
        /\ client[ct1].pid # -1
        /\ client[ct1].pid = client[ct2].pid 
        /\ client[ct1].epoch = client[ct2].epoch

\* It is illegal for two transaction coordinators to believe they
\* are the leader of the same epoch.        
TCsHaveDifferentEpochs ==
    \A p \in TxnLogPartitions :
        ~\E br1, br2 \in Brokers :
            /\ br1 # br2
            /\ tc_log_metadata[br1][p].leader = br1
            /\ tc_log_metadata[br2][p].leader = br2
            /\ tc_log_metadata[br1][p].cepoch = tc_log_metadata[br2][p].cepoch

\* Used for debugging
TestInv ==
    TRUE
\*    ~\E m \in messages :
\*        /\ m.type = AddPartitionsToTxnResponse
\*        /\ m.code = ProducerFenced

\* ----------------------------------------------
\* Liveness properties
\* ----------------------------------------------

\* Eventually all clients will receive a pid, even if there
\* are multiple clients and one tid. This is because:
\* 1. When a client receives an error InitPidResponse, it always sends
\*    a new request. The fairness states that ultimately, it will send
\*    a request to the right broker, eventually.
\* 2. When a client receives a success InitPidResponse, it does nothing
\*    further.
\* Given multiple clients, multiple brokers, and one tid, in the end, 
\* we expect the pepoch of that tid to reach the number of clients. 
EventuallyAllClientsGetPid ==
    <>[](\A c \in Clients : client[c].pid > -1)

\* Eventually, at least one client will have begun a txn and 
\* successfully added partitions. Not all clients will necessarily
\* reach this state, as clients can get fenced then stop.
EventuallyOneClientAddsAllPartitions ==
    <>[](\E c \in Clients : /\ client[c].state = BegunTxn
                            /\ \A tp \in TopicPartitions :
                                    tp \in client[c].partitions)

\* ----------------------------------------------
\* Init and Next
\* ----------------------------------------------

Next ==
    \/ \E c \in Clients :
        \* InitPidRequest
        \/ SendInitPidRequest(c)
        \/ \E b \in Brokers : 
            \/ ReceiveInitPidRequest(b, c)
            \/ ReceiveInitPidResponse(c, b)
        \* AddPartitionsToTxnRequest
        \/ SendAddPartitionsToTxnRequest(c)
        \/ \E b \in Brokers : 
            \/ ReceiveAddPartitionsToTxnRequest(b, c)
            \/ ReceiveAddPartitionsToTxnResponse(c, b)
    \/ \E b \in Brokers, p \in TxnLogPartitions:
        \/ CommitTxnLogAppend(b, p)
        \/ ElectLeader(b, p)
        \/ BecomeFollower(b, p)
    \/ \E b \in Brokers, tid \in TransactionIds :
        CompletePartialTxn(b, tid)

EmptyMap == [x \in {} |-> None]
EmptyTxnState == [tid \in TransactionIds |-> None]

BalancedTidToPartSpread(mapping) ==
    \* Ensure the tid -> txn log partition mapping is evenly distributed.
    \A p1, p2 \in TxnLogPartitions :
        Quantify(DOMAIN mapping, LAMBDA tid : mapping[tid] = p1)
            - Quantify(DOMAIN mapping, LAMBDA tid : mapping[tid] = p2) \in {-1, 0, 1}
            
BalancedPartitionLeadership(part_leader) ==
    \A br1, br2 \in Brokers :
        LET br1_parts == {p \in TxnLogPartitions : part_leader[p] = br1}
            br2_parts == {p \in TxnLogPartitions : part_leader[p] = br2}
        IN Cardinality(br1_parts) - Cardinality(br2_parts) \in {-1, 0, 1}

Init ==
    LET tid_to_part_mapping == CHOOSE mapping \in [TransactionIds -> TxnLogPartitions] :
                                            BalancedTidToPartSpread(mapping) 
        log_part_leader     == CHOOSE mapping \in [TxnLogPartitions -> Brokers] :
                                            BalancedPartitionLeadership(mapping)
    IN
        /\ client = [c \in Clients |-> 
                        [state      |-> Ready,
                         tc         |-> None,
                         tid        |-> None,
                         pid        |-> -1,
                         epoch      |-> -1,
                         last_state |-> None,
                         last_error |-> None,
                         pending_partitions |-> {},
                         partitions |-> {}]]
        /\ tc_tid_metadata = [b \in Brokers |-> [tid \in TransactionIds |-> None]]
        /\ tc_tid_transition = [b \in Brokers |-> [tid \in TransactionIds |-> None]]
        /\ tc_log     = [b \in Brokers |->
                            [p \in TxnLogPartitions |-> <<>>]]
        /\ tc_log_hwm = [b \in Brokers |->
                            [p \in TxnLogPartitions |-> 0]]
        /\ tc_log_metadata = [b \in Brokers |-> 
                                [p \in TxnLogPartitions |-> 
                                    [cepoch |-> 1,
                                     leader |-> log_part_leader[p]]]]
        /\ txn_log_epoch = [p \in TxnLogPartitions |-> 1]
        /\ txn_log_leader = [p \in TxnLogPartitions |-> log_part_leader[p]]
        /\ topic_partitions = [tp \in TopicPartitions |-> <<>>]
        /\ t_to_p_mapping = tid_to_part_mapping
        /\ pid_source = 0
        /\ aux_coord_ctr = 0
        /\ NetworkInit

\* Note that:
\* 1. SendInitPidRequest requires strong fairness because
\*    sending to another broker will disable the action. So we need
\*    fairness that applies to a state that is enabled infinitely often.
\* 2. SendAddPartitionsToTxnRequest is strongly fair right now, but I 
\*    may change that. More of a reminder to self.
\* 3. ElectLeader is not fair, but BecomeFollower is (as it is needed for progress).
Fairness ==
    /\ \A c \in Clients :
        /\ SF_vars(SendInitPidRequest(c))
        /\ \A b \in Brokers :
            /\ WF_vars(ReceiveInitPidRequest(b, c))
            /\ WF_vars(ReceiveInitPidResponse(c, b))
        /\ SF_vars(SendAddPartitionsToTxnRequest(c))
        /\ \A b \in Brokers :
            /\ WF_vars(ReceiveAddPartitionsToTxnResponse(c, b))
            /\ WF_vars(ReceiveAddPartitionsToTxnRequest(b, c))
    /\ \A b \in Brokers, p \in TxnLogPartitions:
        /\ WF_vars(CommitTxnLogAppend(b, p))
        /\ WF_vars(BecomeFollower(b, p))
    /\ \A b \in Brokers, tid \in TransactionIds :
        WF_vars(CompletePartialTxn(b, tid))
          
Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness 

=============================================================================
