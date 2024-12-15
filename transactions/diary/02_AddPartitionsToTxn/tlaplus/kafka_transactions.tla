------------------------- MODULE kafka_transactions -------------------------

EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC, TLCExt,
        network

(*  
    Stage 2 - The AddPartitionsToTxnRequest and response.
    
    Also added:
        1. The transaction coordinator of a partition can now move around.
        2. The FindCoordinator request is now partially modeled, as a simpler
           atomic lookup. It can still be stale as the TC can move from one
           broker to another at any time.

    Limitations:
        1. Does not implement KIP-360 that allows a producer to send an InitPidRequest
           with an existing pid and epoch.
        3. Does not implement KIP-890.
               
    Running: 
        1. Use the VS Code TLA+ extension.
        2. Configure the model parameters in the cfg file.
        3. Choose either liveness checking or not by commenting and uncommenting
           sections in the cfg. See the cfg file.
        4. You must use the -deadlock parameter as clients stop doing anything once 
           they have a PID, which TLC will interpret as a deadlock.
           Example: -workers 4 -deadlock -fpmem 0.75
           Says 4 dedicated threads, 75% of available memory, and a "deadlock" will not
           trigger a counterexample.
*)


\* Model parameters
CONSTANTS TxnLogPartitions,
          TopicPartitions,
          Brokers,
          Clients,
          TransactionIds,
          MaxCoordinatorChanges
          
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

\* TxnStates (only Empty used so far)
CONSTANT Empty, Begin, PrepareCommit, PrepareAbort,
         CompleteAbort, CompleteCommit, Ongoing, 
         PrepareEpochFence, Dead

\* TxnResults         
CONSTANTS Abort, Commit

\* Errors (not all are used yet)
CONSTANTS IllegalState, OK, NotCoordinator, 
          ConcurrentTransactions, ProducerFenced, InvalidTxnTransition,
          InvalidTransition, NotSupportedYet,
          InvalidProducerIdMapping  

\* Other constants
CONSTANTS None

VARIABLES client,               \* a map of client_id -> client state
          tc_txn_metadata,      \* a map of broker_id -> per TID txn state
          tc_txn_transition,    \* a map of broker_id -> per TID txn transition state
          tc_part_metadata,     \* a map of broker_id -> per txn log partition state
          tc_pending_entries,   \* a map of broker_id -> pending txn log entries
          txn_log,              \* a map of txn log partition_id -> the partition data
          txn_log_epoch,        \* a map of txn log partition_id -> the epoch (also known as coordinator epoch)
          pid_source,           \* a unique source of PIDs
          t_to_p_mapping,       \* a mapping of TID to partition (static in this version)
                                \* i.e. partition leadership is static.
          aux_coord_ctr         \* counts the number of coordinator changes

tc_vars == <<tc_txn_metadata, tc_txn_transition, tc_part_metadata, tc_pending_entries>>
log_vars == << txn_log, txn_log_epoch >>
aux_vars == <<pid_source, t_to_p_mapping, aux_coord_ctr>>
vars == <<client, tc_vars, log_vars, aux_vars, net_vars>>

View == <<client, tc_vars, log_vars, pid_source, t_to_p_mapping, NetworkView>>
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
      [] OTHER -> {InvalidTxnTransition}

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

\* ----------------------------------------------
\* The client
\* ----------------------------------------------

\* Some client helpers start --------------------

\* This is an atomic FindCoordinatorRequest implementation.
FindCoordinator(tid) ==
    LET p == t_to_p_mapping[tid]
    IN CHOOSE b \in Brokers :
            /\ p \in DOMAIN tc_part_metadata[b] 
            /\ ~\E b1 \in Brokers :
                /\ b # b1
                /\ p \in DOMAIN tc_part_metadata[b1]
                /\ tc_part_metadata[b1][p].cepoch > tc_part_metadata[b][p].cepoch

\* Some client helpers end --------------------

(* ---------------------------------------------------------------
   ACTION: SendInitPidRequest
   WHO: A client
   
   A client sends an InitPidRequest to a broker. This spec does not
   model the FindCoordinator request, it simply allows a client to
   send an InitPidRequest to any broker. Given that the find coordinator
   step can result in the wrong answer, this seems like a good shortcut
   for keeping the specification as small as possible.
   
   If the client has to TransactionId (tid) then one is non-deterministically
   chosen, else its existing one is reused.
*)

SendInitPidRequest(c) ==
    /\ client[c].state = Ready
    /\ \E tid \in TransactionIds :
        \* If this is a retry, then reuse the same tid, else use whichever.
        /\ IF client[c].tid # None THEN tid = client[c].tid ELSE TRUE
        /\ Send([type |-> InitPidRequest,
                 tid  |-> tid,
                 dest |-> FindCoordinator(tid),
                 source |-> c])
        /\ client' = [client EXCEPT ![c].tid = tid,
                                    ![c].state = SentInitPidRequest]
    /\ UNCHANGED << tc_vars, log_vars, aux_vars >>

(* ---------------------------------------------------------------
   ACTION: ReceiveInitPidResponse
   WHO: A client
   
   A client receives an InitPidResponse. If it is an OK response,
   then it updates its pid and epoch, and transitions to the HasPid state.
   These states are not part of the protocol, but used for implementing
   the client as a state machine.
   
   If the response is an error, then the client reverts back to Ready, where
   it can retry the InitPidRequest.
*)

ReceiveInitPidResponse(c, b) ==
    /\ client[c].state = SentInitPidRequest
    /\ \E msg \in messages : 
        /\ msg.dest = c
        /\ msg.source = b
        /\ msg.type = InitPidResponse
        /\ IF msg.code = OK
           THEN client' = [client EXCEPT ![c].state = HasPid,
                                         ![c].tc = msg.source,
                                         ![c].pid = msg.pid,
                                         ![c].epoch = msg.pepoch]
           ELSE client' = [client EXCEPT ![c].state = Ready,
                                         ![c].last_state = client[c].state,
                                         ![c].last_error = msg.code]
        /\ Discard(msg)
    /\ UNCHANGED << tc_vars, log_vars, aux_vars >>


(* ---------------------------------------------------------------
   ACTION: SendAddPartitionsToTxnRequest
   WHO: A client
   
   TODO
*)

SendAddPartitionsToTxnRequest(c) ==
    /\ client[c].state \in { HasPid, BegunTxn }
    /\ client[c].pending_partitions = {}
    /\ \E p \in TopicPartitions :
        /\ p \notin client[c].partitions
        /\ Send([type       |-> AddPartitionsToTxnRequest,
                 tid        |-> client[c].tid,
                 pid        |-> client[c].pid,
                 pepoch     |-> client[c].epoch,
                 partitions |-> {p}, \* one partition for now
                 dest       |-> client[c].tc,
                 source     |-> c])
        /\ client' = [client EXCEPT ![c].pending_partitions = {p},
                                    ![c].state = BegunTxn]
    /\ UNCHANGED << tc_vars, log_vars, aux_vars >>


(* ---------------------------------------------------------------
   ACTION: ReceiveAddPartitionsToTxnResponse
   WHO: A client
   
   TODO
*)

ReceiveAddPartitionsToTxnResponse(c, b) ==
    /\ client[c].state = BegunTxn
    /\ \E msg \in messages : 
        /\ msg.dest = c
        /\ msg.source = b
        /\ msg.type = AddPartitionsToTxnResponse
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
    /\ UNCHANGED << tc_vars, log_vars, aux_vars >>

\* ----------------------------------------------
\* The transaction coordinator actions
\* ----------------------------------------------

\* COMMON HELPERS START --------------------------------------

PartitionFor(tid) == t_to_p_mapping[tid]
PartitionMetadataOf(b, partition) == tc_part_metadata[b][partition]
PartitionMetadataOfTid(b, tid) == PartitionMetadataOf(b, PartitionFor(tid))

CurrentTransition(b, tid) ==
    tc_txn_transition[b][tid]

HasPartitionMetadata(b, p) ==
    p \in DOMAIN tc_part_metadata[b]

IsTxnLogPartitionLeader(b, p) ==
    /\ p \in DOMAIN tc_part_metadata[b]
    /\ txn_log_epoch[p] = tc_part_metadata[b][p].cepoch    
    
GetTxnMetadata(b, tid) ==
    CASE ~HasPartitionMetadata(b, PartitionFor(tid)) -> 
            [code |-> NotCoordinator] 
      [] tc_txn_metadata[b][tid] = None -> 
            None
      [] OTHER->
            [code         |-> OK,
             txn_metadata |-> tc_txn_metadata[b][tid],
             cepoch       |-> PartitionMetadataOfTid(b, tid).cepoch]

GetTransition(b, curr_transition, curr_state, new_state, pid, 
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

GetCompleteTransition(b, tid, txn_metadata) ==
    LET next_state == IF txn_metadata.state = PrepareCommit 
                      THEN CompleteCommit ELSE CompleteAbort
    IN GetTransition(b, None, \* clear the current pending transition to avoid an error 
                      txn_metadata.state,     \* current state
                      next_state,              \* transition to CompleteAbort or CompleteCommit
                      txn_metadata.pid,        \* same pid (no exhaustion)
                      txn_metadata.pepoch,     \* TODO: epoch bumping? 
                      txn_metadata.last_pepoch,      
                      txn_metadata.partitions) \* no partitions change

AppendCompleteOrAbort(b, p, tid, transition, pending_entries) ==
    /\ tc_pending_entries' = [tc_pending_entries EXCEPT ![b][p] = 
                                Append(pending_entries,
                                       [tid          |-> tid,
                                        transition   |-> transition,
                                        response     |-> None, 
                                        err_response |-> None])]
    /\ tc_txn_transition' = [tc_txn_transition EXCEPT ![b][tid] = transition]

\* COMMON HELPERS END --------------------------------------

(* ---------------------------------------------------------------
   ACTION: BecomeLeader
   WHO: Transaction controller
   
   TODO
*)

\* You would materialize txn state based on the log, but
\* that is quite ugly code, instead the simpler equivalent
\* is to copy the state of the original TC.
MaterializeState(tid) ==
    LET p  == PartitionFor(tid)
        b == CHOOSE b \in Brokers : IsTxnLogPartitionLeader(b, p)
    IN tc_txn_metadata[b][tid]

PartitionsWith(b, p) ==
    DOMAIN tc_part_metadata[b] \union {p}

BecomeLeader(b, p) ==
    /\ aux_coord_ctr < MaxCoordinatorChanges
    /\ p \notin DOMAIN tc_part_metadata[b]
    \* Bump the coordinator epoch of the partition leadership that is moving to
    \* to this broker.
    /\ LET cepoch == txn_log_epoch[p] + 1
       IN
          \* Updates this brokers partition metadata with the new epoch.
          /\ tc_part_metadata' = [tc_part_metadata EXCEPT ![b] =
                                        [p1 \in PartitionsWith(b, p)
                                            |-> IF p1 = p
                                                THEN [cepoch |-> cepoch]
                                                ELSE tc_part_metadata[b][p1]]]
          \* Bump the txn log partition epoch (which is the same thing as the cepoch)
          /\ txn_log_epoch' = [txn_log_epoch EXCEPT ![p] = cepoch]
          \* Materialize the txn metadata stored by this txn log partition
          /\ tc_txn_metadata' = [tc_txn_metadata EXCEPT ![b] =
                                    [tid \in TransactionIds |->
                                        IF PartitionFor(tid) = p
                                        THEN MaterializeState(tid)
                                        ELSE None]]
          /\ aux_coord_ctr' = aux_coord_ctr + 1
          /\ UNCHANGED <<tc_txn_transition, tc_pending_entries, txn_log, client,
                         pid_source, t_to_p_mapping, net_vars>>

(* ---------------------------------------------------------------
   ACTION: CompletePartialTxn
   WHO: Transaction controller
   
   After becoming the TC for a partition, there may be tids that
   had a committed PrepareAbort/Commit, but no CompleteAbort/Commit.
   This action ensures that are initiated prepare phase gets completed.
*)

CompletePartialTxn(b, tid) ==
    LET p            == PartitionFor(tid)
        txn_metadata == tc_txn_metadata[b][tid]
        trans_result == GetCompleteTransition(b, tid, txn_metadata)
    IN 
        /\ HasPartitionMetadata(b, p)
        /\ txn_metadata # None
        /\ txn_metadata.state \in {PrepareAbort, PrepareCommit}
        /\ tc_txn_transition[b][tid] = None
        /\ trans_result.code = OK
        /\ AppendCompleteOrAbort(b, p, tid, trans_result.transition, <<>>)
        /\ UNCHANGED <<tc_part_metadata, tc_txn_metadata, txn_log,
                       txn_log_epoch, client, aux_vars, net_vars>>
    
    
(* ---------------------------------------------------------------
   ACTION: BecomeFollower
   WHO: Transaction controller
   
   TODO
*)

PartitionsWithout(b, p) ==
    DOMAIN tc_part_metadata[b] \ {p}

RemoveNoneResponses(responses) ==
    { r \in responses : r # None }

BecomeFollower(b, p) ==
    /\ p \in DOMAIN tc_part_metadata[b]
    /\ tc_part_metadata[b][p].cepoch < txn_log_epoch[p]
    /\ LET err_responses == { entry.err_response : entry \in ToSet(tc_pending_entries[b][p]) }
       IN
          /\ tc_part_metadata' = [tc_part_metadata EXCEPT ![b] =
                                        [p1 \in PartitionsWithout(b, p) |->
                                            tc_part_metadata[b][p1]]]
          \* Clear out txn state of the affected tids
          /\ tc_txn_metadata' = [tc_txn_metadata EXCEPT ![b] =
                                        [tid \in TransactionIds |->
                                            IF PartitionFor(tid) = p
                                            THEN None
                                            ELSE tc_txn_metadata[b][tid]]]
          \* Clear out txn pending transitions of the affected tids
          /\ tc_txn_transition' = [tc_txn_transition EXCEPT ![b] =
                                        [tid \in TransactionIds |->
                                            IF PartitionFor(tid) = p
                                            THEN None
                                            ELSE tc_txn_transition[b][tid]]]
          \* Clear out all pending log entries
          /\ tc_pending_entries' = [tc_pending_entries EXCEPT ![b][p] = <<>>]
          /\ SendAll(RemoveNoneResponses(err_responses))
          /\ UNCHANGED << txn_log, txn_log_epoch, client, aux_vars>>
    
(* ---------------------------------------------------------------
   ACTION: ReceiveInitPidRequest
   WHO: Transaction controller
   
   A TC receives an InitPidRequest.
   - If the txn log partition for this tid does not belong to this TC
     then it sends an InitPidResponse with the error NotCoordinatorForTransactionalId.
   - If there is no existing metadata for a txn with this tid, 
        - Then new, empty metadata is created. When creating new metadata, 
          a unique ProducerId (pid) is generated with a producer epoch of -1.
        - Else the existing txn metadata is used.
   - If there is an in-progress transition (a prior transition was appended
     to the txn log but it hasn't committed yet)
        - Then the TC sends an InitPidResponse with the error ConcurrentTransactions. 
        - Else, a new transition is generated with:
            - the Empty state
            - the pid and incremented epoch
          The TC appends this transition metadata to the txn log partition.
   - Once the transition is committed to the txn log, the TC sends the
     InitPidResponse to the client with the pid and incremented epoch.
*)

GetOrCreateTxnMetadata(b, tid) ==
    LET cached_md == GetTxnMetadata(b, tid)
    IN
        IF cached_md = None THEN
            \* Generate new metadata.
            [code         |-> OK,
             txn_metadata |-> [pid           |-> pid_source + 1, 
                               last_pid      |-> -1,
                               pepoch        |-> -1, 
                               last_pepoch   |-> -1,
                               state         |-> Empty, 
                               partitions    |-> {}],
             cepoch       |-> PartitionMetadataOfTid(b, tid).cepoch]
        ELSE cached_md

GetInitPidTransition(b, tid, txn_metadata) ==
    \* This is simple now, but lots more logic will get added here.
    CASE txn_metadata.state \in { CompleteAbort, CompleteCommit, Empty } ->
            GetTransition(b, CurrentTransition(b, tid), 
                          txn_metadata.state,   \* current state
                          Empty,                \* transition to Empty
                          txn_metadata.pid,     \* the pid (no exhaustion modeled)
                          txn_metadata.pepoch + 1, \* new pepoch (incremented) 
                          txn_metadata.pepoch,     \* last pepoch
                          {}) \* no partitions yet
      [] txn_metadata.state = Ongoing ->
            \* Abort the ongoing transaction first, by fencing the producer
            GetTransition(b, CurrentTransition(b, tid), 
                          txn_metadata.state,   \* current state
                          PrepareEpochFence,    \* transition to PrepareEpochFence
                          txn_metadata.pid,     \* same pid (no exhaustion)
                          txn_metadata.pepoch + 1, \* bump the pepoch 
                          -1, \* don't know why yet     
                          txn_metadata.partitions) \* no partitions change
      [] txn_metadata.state \in { PrepareAbort, PrepareCommit } ->
            [code |-> ConcurrentTransactions]
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

GetPrepareAbortOrCommitTransition(b, tid, curr_metadata, new_metadata, next_state) ==
    GetTransition(b, CurrentTransition(b, tid), 
                  curr_metadata.state,     \* current state
                  next_state,              \* transition to PrepareAbort or PrepareCommit
                  new_metadata.pid,        \* same pid (no exhaustion)
                  new_metadata.pepoch,     \* TODO: client support for bump pepoch? 
                  new_metadata.last_pepoch,      
                  curr_metadata.partitions) \* no partitions change

\* Transition to PrepareCommit or PrepareAbort
EndTransaction(msg, b, c, curr_metadata, new_metadata, 
               partition, txn_result, is_from_client) ==
    CASE \/ (is_from_client /\ new_metadata.pepoch # curr_metadata.pepoch)
         \/ new_metadata.pepoch < curr_metadata.pepoch ->
            /\ Reply(msg, MakeErrorPidResponse(b, c, ProducerFenced))
            /\ UNCHANGED << tc_txn_transition, tc_pending_entries >>
      [] curr_metadata.state = Ongoing ->
            LET next_state   == IF txn_result = Abort THEN PrepareAbort ELSE PrepareCommit
                trans_result == IF next_state = PrepareAbort /\ new_metadata.state = PrepareEpochFence
                                THEN GetPrepareAbortOrCommitTransition(b, msg.tid, curr_metadata, 
                                                                       new_metadata, next_state)
                                ELSE None 
            IN  /\ Discard(msg) \* We'll reply once the transition is complete
                /\ tc_txn_transition' = [tc_txn_transition EXCEPT ![b][msg.tid] = trans_result.transition]
                /\ tc_pending_entries' = [tc_pending_entries EXCEPT ![b][partition] = 
                                                Append(@, [client_id  |-> msg.source,
                                                           tid        |-> msg.tid,
                                                           transition |-> trans_result.transition,
                                                           response   |-> MakePidResponse(
                                                                                b, c, ConcurrentTransactions,
                                                                                -1, -1),
                                                           err_response |-> MakeErrorPidResponse(b, c, NotCoordinator)])]
      [] OTHER -> 
            /\ Reply(msg, MakeErrorPidResponse(b, c, IllegalState))
            /\ UNCHANGED << tc_txn_transition, tc_pending_entries >>
                 
    

ReceiveInitPidRequest(b, c) ==
    \E msg \in messages :
        /\ msg.dest = b
        /\ msg.source = c
        /\ msg.type = InitPidRequest
        /\ LET md_result    == GetOrCreateTxnMetadata(b, msg.tid)
               trans_result == GetInitPidTransition(b, msg.tid,
                                                    md_result.txn_metadata)
               partition    == PartitionFor(msg.tid)
               is_leader    == IsTxnLogPartitionLeader(b, partition)
           IN 
              IF md_result.code # OK
              THEN /\ Reply(msg, MakeErrorPidResponse(b, c, md_result.code))
                   /\ UNCHANGED <<pid_source, tc_vars, txn_log>>
              ELSE /\ pid_source' = md_result.txn_metadata.pid
                   /\ tc_txn_metadata' = [tc_txn_metadata EXCEPT ![b][msg.tid] = md_result.txn_metadata]
                   /\ CASE 
                        \* CASE 1 - Can't make a transition right now.
                           trans_result.code # OK ->
                                /\ Reply(msg, MakeErrorPidResponse(b, c, trans_result.code))
                                /\ UNCHANGED << tc_txn_transition, tc_pending_entries, txn_log >>
                        \* CASE 2 - Need to fence the current producer and abort its txn
                        [] trans_result.transition.state = PrepareEpochFence ->
                            EndTransaction(msg, b, c, 
                                           md_result.txn_metadata, 
                                           trans_result.transition, 
                                           partition,
                                           Abort, FALSE)
                        \* CASE 3 - All ok, write the transition to the txn log (pending entries)
                        [] OTHER ->    
                            /\ Discard(msg) \* We'll reply once the transition is complete
                            /\ tc_txn_transition' = [tc_txn_transition EXCEPT ![b][msg.tid] = trans_result.transition]
                            /\ tc_pending_entries' = [tc_pending_entries EXCEPT ![b][partition] = 
                                                            Append(@, [tid        |-> msg.tid,
                                                                       transition |-> trans_result.transition,
                                                                       response   |-> MakePidResponse(
                                                                                            b, c, OK,
                                                                                            trans_result.transition.pid,
                                                                                            trans_result.transition.pepoch),
                                                                       err_response |-> MakeErrorPidResponse(b, c, NotCoordinator)])]
        /\ UNCHANGED << client, log_vars, tc_part_metadata, t_to_p_mapping, aux_coord_ctr >>

(* ---------------------------------------------------------------
   ACTION: TxnLogAppendCommits
   WHO: Transaction controller
   
   A pending write to the txn log commits.   
*)

CommitTransition(b, p, entry) ==
    /\ tc_pending_entries' = [tc_pending_entries EXCEPT ![b][p] = Tail(@)]
    /\ tc_txn_transition' = [tc_txn_transition EXCEPT ![b][entry.tid] = None]

CommitTxnLogAppend(b, p) ==
    /\ tc_pending_entries[b][p] # <<>>
    /\ LET entry == Head(tc_pending_entries[b][p])
       IN /\ IsTxnLogPartitionLeader(b, p)
          /\ txn_log' = [txn_log EXCEPT ![p] = Append(@, [tid      |-> entry.tid,
                                                          metadata |-> entry.transition])]
          /\ tc_txn_metadata' = [tc_txn_metadata EXCEPT ![b][entry.tid] = entry.transition]
          /\ CASE
                \* CASE 1 - Committed a PrepareAbort or PrepareCommit
                \*          Start a new transition to complete the commit/abort.
                  entry.transition.state \in {PrepareAbort, PrepareCommit } ->
                      LET new_trans_result == GetCompleteTransition(b, entry.tid, entry.transition)
                      IN IF new_trans_result.code = OK
                         \* The *new* transition is ok so append it and send the response now.
                         \* Note we don't store a response for the new transition, as we already respond now. 
                         THEN /\ AppendCompleteOrAbort(b, p, entry.tid, new_trans_result.transition,
                                                       Tail(tc_pending_entries[b][p]))
\*                              /\ tc_pending_entries' = [tc_pending_entries EXCEPT ![b][p] = 
\*                                                            Append(Tail(@),
\*                                                                   [tid          |-> entry.tid,
\*                                                                    transition   |-> new_trans_result.transition,
\*                                                                    response     |-> None, 
\*                                                                    err_response |-> None])]
\*                              /\ tc_txn_transition' = [tc_txn_transition EXCEPT ![b][entry.tid] = new_trans_result.transition]
                              /\ Send(entry.response)
                         \* The *new* transition is not ok so don't append it, and send the response with the updated error code
                         ELSE LET response == [entry.response EXCEPT !.code = new_trans_result.code]
                              IN /\ CommitTransition(b, p, entry) 
                                 /\ Send(response)
                                          
                \* CASE 2 - An entry got committed that requires no response
                [] entry.response = None ->
                      /\ CommitTransition(b, p, entry)
                      /\ UNCHANGED <<messages, messages_discard>>
                \* CASE 3 - An entry got committed that requires a response to the client
                [] OTHER ->
                      /\ CommitTransition(b, p, entry)
                      /\ Send(entry.response)
    /\ UNCHANGED << client, txn_log_epoch, tc_part_metadata, aux_vars >>

(* ---------------------------------------------------------------
   ACTION: ReceiveAddPartitionsToTxnRequest
   WHO: Transaction controller
   
   TODO   
*)

MakeAddPartsResponse(b, c, code, partitions) ==
    [type       |-> AddPartitionsToTxnResponse,
     code       |-> code,
     partitions |-> partitions,
     dest       |-> c,
     source     |-> b]

ReplyWithError(msg, b, c, error) ==
    /\ Reply(msg, MakeAddPartsResponse(b, c, error, {}))
    /\ UNCHANGED << tc_txn_transition, tc_pending_entries, txn_log >>
                
GetAddPartitionsTransition(b, tid, txn_metadata, add_partitions) ==
    GetTransition(b, CurrentTransition(b, tid), 
                  txn_metadata.state, \* the current state 
                  Ongoing,            \* transition to ONGOING
                  txn_metadata.pid,
                  txn_metadata.pepoch, 
                  txn_metadata.last_pepoch, 
                  txn_metadata.partitions \union add_partitions)

ReceiveAddPartitionsToTxnRequest(b, c) ==
    \E msg \in messages :
        /\ msg.dest = b
        /\ msg.source = c
        /\ msg.type = AddPartitionsToTxnRequest
        /\ LET md_result    == GetTxnMetadata(b, msg.tid)
               trans_result == GetAddPartitionsTransition(b, msg.tid,
                                                          md_result.txn_metadata,
                                                          msg.partitions)
               partition    == PartitionFor(msg.tid)
           IN
              CASE md_result = None ->
                        ReplyWithError(msg, b, c, InvalidProducerIdMapping)
                [] md_result.code = NotCoordinator ->
                        ReplyWithError(msg, b, c, NotCoordinator)
                [] msg.pid # md_result.txn_metadata.pid ->
                        ReplyWithError(msg, b, c, InvalidProducerIdMapping)
                [] msg.pepoch # md_result.txn_metadata.pepoch -> 
                        ReplyWithError(msg, b, c, ProducerFenced)
                [] tc_txn_transition[b][msg.tid] # None ->
                        ReplyWithError(msg, b, c, ConcurrentTransactions)
                [] md_result.txn_metadata.state \in {PrepareCommit, PrepareAbort} ->
                        ReplyWithError(msg, b, c, ConcurrentTransactions)
                [] trans_result.code # OK ->
                        ReplyWithError(msg, b, c, trans_result.code)
                [] OTHER ->
                        /\ Discard(msg) \* We'll reply once the transition is complete
                        /\ tc_txn_transition' = [tc_txn_transition EXCEPT ![b][msg.tid] = trans_result.transition]
                        /\ tc_pending_entries' = [tc_pending_entries EXCEPT ![b][partition] = 
                                                      Append(@, [tid          |-> msg.tid,
                                                                 transition   |-> trans_result.transition,
                                                                 response     |-> MakeAddPartsResponse(b, c, OK, trans_result.transition.partitions),
                                                                 err_response |-> MakeAddPartsResponse(b, c, NotCoordinator, {})])] 
        /\ UNCHANGED <<tc_txn_metadata, log_vars, tc_part_metadata, client, aux_vars>>
                
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
        \/ BecomeLeader(b, p)
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
            
BalancedBrokerToPartLeadership(mapping) ==
    \* Ensure that each partition has a leader.
    /\ \A p \in TxnLogPartitions : \E b \in Brokers : p \in mapping[b]
    \* Ensure that each broker is the leader of disjoint subsets of txn log partitions
    /\ ~\E b1, b2 \in Brokers : 
        /\ b1 # b2
        /\ (mapping[b1] \intersect mapping[b2]) # {}
        \* And that the partitions are evenly spread
        /\ Cardinality(mapping[b1]) - Cardinality(mapping[b2]) \in {-1, 0, 1}

Init ==
    LET tid_to_part_mapping == CHOOSE mapping \in [TransactionIds -> TxnLogPartitions] :
                                            BalancedTidToPartSpread(mapping) 
        b_partitions        == CHOOSE mapping \in [Brokers -> SUBSET TxnLogPartitions] :
                                            BalancedBrokerToPartLeadership(mapping)
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
        /\ tc_txn_metadata = [b \in Brokers |-> [tid \in TransactionIds |-> None]]
        /\ tc_txn_transition = [b \in Brokers |-> [tid \in TransactionIds |-> None]]
        /\ tc_part_metadata = [b \in Brokers |-> 
                                [p \in b_partitions[b] |-> 
                                    [cepoch |-> 1]]]
        /\ tc_pending_entries = [b \in Brokers |-> 
                                    [p \in TxnLogPartitions |-> <<>>]]
        /\ txn_log = [p \in TxnLogPartitions |-> <<>>]
        /\ txn_log_epoch = [p \in TxnLogPartitions |-> 1]
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
