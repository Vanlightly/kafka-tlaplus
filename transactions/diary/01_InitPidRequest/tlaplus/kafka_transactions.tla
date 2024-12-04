------------------------- MODULE kafka_transactions -------------------------

EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC,
        network

(*  
    Stage 1 - The InitPidRequest and response.

    Limitations:
        1. The FindCoordinator request is not modeled, instead the spec allows
           any client to send an InitPidRequest to any broker. Given that the 
           find coordinator step can result in the wrong answer, this seems like
           a good shortcut for keeping the specification as small as possible.
        2. Does not implement KIP-360 that allows a producer to send an InitPidRequest
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
          Brokers,
          Clients,
          TransactionIds
          
\* Message types
CONSTANTS InitPidRequest,
          InitPidResponse
          
\* Client states (not part of the protocol but used to control client behavior)
CONSTANTS Ready, 
          SentInitPidRequest,
          HasPid

\* TxnStates (only Empty used so far)
CONSTANT Empty, Begin, PrepareCommit, PrepareAbort,
         CompleteAbort, CompleteCommit, Ongoing, 
         PrepareEpochFence, Dead

\* TxnResults         
CONSTANTS Abort, Commit

\* Errors (not all are used yet)
CONSTANTS IllegalState, OK, NotCoordinatorForTransactionalId, 
          ConcurrentTransactions, ProducerFenced, InvalidTxnState,
          InvalidTransition, NotSupportedYet  

\* Other constants
CONSTANTS None

VARIABLES client,               \* a map of client_id -> client state
          tc_txn_metadata,      \* a map of broker_id -> per TID txn state
          tc_txn_transition,    \* a map of broker_id -> per TID txn transition state
          tc_part_metadata,     \* a map of broker_id -> per txn log partition state
          txn_log,              \* a map of partition_id -> the partition data
          txn_log_hwm,          \* a map of partition_id -> the HWM
          pid_source,           \* a unique source of PIDs
          t_to_p_mapping        \* a mapping of TID to partition (static in this version)
                                \* i.e. partition leadership is static.

tc_vars == <<tc_txn_metadata, tc_txn_transition, tc_part_metadata>>
log_vars == << txn_log, txn_log_hwm >>
aux_vars == <<pid_source, t_to_p_mapping>>
vars == <<client, tc_vars, log_vars, aux_vars, net_vars>>

View == <<client, tc_vars, log_vars, aux_vars, NetworkView>>
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
      [] OTHER -> {IllegalState}

InitPidRequestType ==
    [type: {InitPidRequest},
     tid: TransactionIds,
     dest: Brokers,
     source: Clients]
     
InitPidResponseType ==
    [type: {InitPidResponse},
     code: {OK, ConcurrentTransactions, NotCoordinatorForTransactionalId, IllegalState},
     pid: Nat \union {-1},
     pepoch: Nat \union {-1},
     dest: Clients,
     source: Brokers]
     
MessageType ==
    InitPidRequestType \union InitPidResponseType     

\* ----------------------------------------------
\* The client
\* ----------------------------------------------

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

SendInitPidRequest(c, b) ==
    /\ client[c].state = Ready
    /\ \E tid \in TransactionIds :
        \* If this is a retry, then reuse the same tid, else use whichever.
        /\ IF client[c].tid # None THEN tid = client[c].tid ELSE TRUE
        /\ Send([type |-> InitPidRequest,
                 tid  |-> tid,
                 dest |-> b,
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

ReceiveInitPidResponse(c) ==
    /\ client[c].state = SentInitPidRequest
    /\ \E msg \in messages : 
        /\ msg.dest = c
        /\ msg.type = InitPidResponse
        /\ IF msg.code = OK
           THEN client' = [client EXCEPT ![c].state = HasPid,
                                         ![c].pid = msg.pid,
                                         ![c].epoch = msg.pepoch]
           ELSE client' = [client EXCEPT ![c].state = Ready,
                                         ![c].last_state = client[c].state,
                                         ![c].last_error = msg.code]
        /\ Discard(msg)
    /\ UNCHANGED << tc_vars, log_vars, aux_vars >>
            

\* ----------------------------------------------
\* The transaction coordinator actions
\* ----------------------------------------------

\* HELPERS --------------------------------------

PartitionFor(tid) == t_to_p_mapping[tid]
PartitionMetadataOf(b, partition) == tc_part_metadata[b][partition]
PartitionMetadataOfTid(b, tid) == PartitionMetadataOf(b, PartitionFor(tid))

IsNextCommittedLogEntry(b, p, match_state) ==
    /\ p \in DOMAIN tc_part_metadata[b]
    /\ Len(txn_log[p]) > txn_log_hwm[p]
    /\ LET next == txn_log_hwm[p] + 1
           entry == txn_log[p][next]
       IN entry.transition.state = match_state
       
NextCommittedLogEntry(b, p) ==
    LET next == txn_log_hwm[p] + 1
    IN txn_log[p][next]  

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

GetTxnMetadata(b, tid) ==
    CASE \* CASE 1 - Txn metadata exists already, just return what is cached.
         tc_txn_metadata[b][tid] # None ->
            [code         |-> OK,
             txn_metadata |-> tc_txn_metadata[b][tid],
             cepoch       |-> PartitionMetadataOfTid(b, tid).cepoch]
      \* CASE 2  - Check this is the right TC for the Transaction Id (tid).
      \*           Then generate new metadata.
      [] PartitionFor(tid) \in DOMAIN tc_part_metadata[b] ->
            [code         |-> OK,
             txn_metadata |-> [pid           |-> pid_source + 1, 
                               last_pid      |-> -1,
                               pepoch        |-> -1, 
                               last_pepoch   |-> -1,
                               state         |-> Empty, 
                               partitions    |-> {}],
             cepoch       |-> PartitionMetadataOfTid(b, tid).cepoch]
      \* CASE 3 - This TC is not the one for this tid
      [] OTHER -> [code |-> NotCoordinatorForTransactionalId]

GetTransition(b, tid, curr_state, new_state, curr_pid, new_pid, 
              new_pepoch, new_last_pepoch, new_partitions) ==
    CASE \* CASE 1 - Reject because an existing transition is currently being committed.
         tc_txn_transition[b][tid] # None ->
            [code |-> ConcurrentTransactions]
      \* CASE 2 - Accept as this is a valid transition
      [] curr_state \in ValidPrevTxnStates(new_state) ->
             \* Create a modified txn metadata transitioned to the new state
            [code        |-> OK,
             transition  |-> [pid         |-> new_pid, 
                              last_pid    |-> curr_pid,
                              pepoch      |-> new_pepoch, 
                              last_pepoch |-> new_last_pepoch,
                              state       |-> new_state,
                              partitions  |-> new_partitions]]
      \* CASE 3 - This shouldn't happen. 
      [] OTHER -> 
            \* Shouldn't get here
            [code |-> InvalidTransition]
            
GetInitPidTransition(b, tid, cepoch, txn_metadata) ==
    \* This is simple now, but lots more logic will get added here.
    CASE txn_metadata.state = Empty ->
            GetTransition(b, tid, 
                          txn_metadata.state, Empty, \* transition to EMPTY
                          txn_metadata.pid, txn_metadata.pid, \* pid exhaustion not implemented
                          txn_metadata.pepoch + 1, \* Increment the producer epoch 
                          txn_metadata.pepoch, {})
    [] OTHER -> 
            \* Shouldn't get here
            [code |-> IllegalState]
         
ReceiveInitPidRequest(b, c) ==
    \E msg \in messages :
        /\ msg.dest = b
        /\ msg.source = c
        /\ msg.type = InitPidRequest
        /\ LET md_result    == GetTxnMetadata(b, msg.tid)
               trans_result == GetInitPidTransition(b, msg.tid,
                                                    md_result.cepoch,
                                                    md_result.txn_metadata)
               partition    == PartitionFor(msg.tid)
           IN 
              IF md_result.code # OK
              THEN /\ Reply(msg, [type   |-> InitPidResponse,
                                  code   |-> md_result.code,
                                  pid    |-> -1,
                                  pepoch |-> -1,
                                  dest   |-> msg.source,
                                  source |-> b])
                   /\ UNCHANGED <<pid_source, tc_vars, txn_log>>
              ELSE /\ pid_source' = md_result.txn_metadata.pid
                   /\ tc_txn_metadata' = [tc_txn_metadata EXCEPT ![b][msg.tid] = md_result.txn_metadata]
                   /\ IF trans_result.code # OK
                      THEN /\ Reply(msg, [type   |-> InitPidResponse,
                                          code   |-> trans_result.code,
                                          pid    |-> -1,
                                          pepoch |-> -1,
                                          dest   |-> msg.source,
                                          source |-> b])
                           /\ UNCHANGED << tc_txn_transition, txn_log >>
                      ELSE /\ Discard(msg) \* We'll reply once the transition is complete
                           /\ tc_txn_transition' = [tc_txn_metadata EXCEPT ![b][msg.tid] = trans_result.transition]
                           /\ txn_log' = [txn_log EXCEPT ![partition] = Append(@, [client_id  |-> msg.source,
                                                                                   tid        |-> msg.tid,
                                                                                   transition |-> trans_result.transition])]
        /\ UNCHANGED << client, txn_log_hwm, tc_part_metadata, t_to_p_mapping >>

(* ---------------------------------------------------------------
   ACTION: CompleteInitPidRequest
   WHO: Transaction controller
   
   A pending transition of an InitPidRequest gets committed to the txn log, 
   and the TC sends an InitPidResponse to the client.   
*)

CompleteInitPidRequest(b, p) ==
    /\ IsNextCommittedLogEntry(b, p, Empty)
    /\ LET entry == NextCommittedLogEntry(b, p)
       IN /\ tc_txn_metadata' = [tc_txn_metadata EXCEPT ![b][entry.tid] = entry.transition]
          /\ tc_txn_transition' = [tc_txn_transition EXCEPT ![b][entry.tid] = None]
          /\ txn_log_hwm' = [txn_log_hwm EXCEPT ![p] = @ + 1] \* increment HWM
          /\ Send([type   |-> InitPidResponse,
                   code   |-> OK,
                   pid    |-> entry.transition.pid,
                   pepoch |-> entry.transition.pepoch,
                   dest   |-> entry.client_id,
                   source |-> b])
          /\ UNCHANGED <<client, tc_part_metadata, txn_log, aux_vars>>
               

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
    <>[](\A c \in Clients : client[c].state = HasPid)

\* ----------------------------------------------
\* Init and Next
\* ----------------------------------------------

Next ==
    \/ \E c \in Clients :
        \/ ReceiveInitPidResponse(c)
        \/ \E b \in Brokers :
            \/ SendInitPidRequest(c, b)
            \/ ReceiveInitPidRequest(b, c)
    \/ \E b \in Brokers, p \in TxnLogPartitions:
        \/ CompleteInitPidRequest(b, p)

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
                         tid        |-> None,
                         pid        |-> -1,
                         epoch      |-> -1,
                         last_state |-> None,
                         last_error |-> None]]
        /\ tc_txn_metadata = [b \in Brokers |-> [tid \in TransactionIds |-> None]]
        /\ tc_txn_transition = [b \in Brokers |-> [tid \in TransactionIds |-> None]]
        /\ tc_part_metadata = [b \in Brokers |-> 
                                [p \in b_partitions[b] |-> 
                                    [cepoch |-> 1]]]
        /\ txn_log = [p \in TxnLogPartitions |-> <<>>]
        /\ txn_log_hwm = [p \in TxnLogPartitions |-> 0] \* inclusive
        /\ t_to_p_mapping = tid_to_part_mapping
        /\ pid_source = 0
        /\ NetworkInit

\* Note that SendInitPidRequest requires strong fairness because
\* sending to another broker will disable the action. So we need
\* fairness that applies to a state that is enabled infinitely often. 
Fairness ==
    /\ \A c \in Clients :
        /\ WF_vars(ReceiveInitPidResponse(c))
    /\ \A b \in Brokers, c \in Clients :
        /\ SF_vars(SendInitPidRequest(c, b))
        /\ WF_vars(ReceiveInitPidRequest(b, c))
    /\ \A b \in Brokers, p \in TxnLogPartitions:
        /\ WF_vars(CompleteInitPidRequest(b, p))
          
Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness 

=============================================================================
