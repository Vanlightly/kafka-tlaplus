------------------- MODULE consumer_group_protocol_kip_848 -------------------

EXTENDS Integers, Naturals, Functions, FiniteSets, FiniteSetsExt, SequencesExt, Sequences, TLC,
        message_passing

(* ############################################
   Kafka Consumer Group Protocol KIP-848
   ############################################

See the readme for a general discussion of this specification.

Notes: 
- To disambiguate the word "state", commonly used in TLA+,
this spec uses the word "status" for enum-style states such 
as STABLE. "State" refers to the information of an entity as a whole.
- Actions are enabled when their enabling conditions are true,
  the model checker will only execute enabled actions.
*)


\* Model parameters, see readme for descriptions
CONSTANTS Clients,                  \* a set of the clients
          TopicCount,               \* the number of possible topics
          PartitionsPerTopic,       \* the number of partitions per topic
          MaxFencings               \* the maximum number of fencings to explore

ASSUME TopicCount \in Nat
ASSUME PartitionsPerTopic \in Nat
ASSUME MaxFencings \in Nat

\* Model values
CONSTANTS UNACKED_ASSIGNMENT,
          UNREL_PARTITIONS,
          UNJOINED,
          RECONCILING,
          STABLE,
          FENCED,
          FAILED,
          UNSUBSCRIBED,
          JOINING,
          ACKNOWLEDGING,
          PREPARE_LEAVING,  
          LEAVING,
          FATAL,            \* not used
          EMPTY,
          ASSIGNING,
          ILLEGAL_STATE,
          FENCED_MEMBER_EPOCH,
          UNKNOWN_MEMBER_ID,
          Nil

\* Group coordinator state
VARIABLES group_members,            \* the current group members   
          group_member_state,       \* the state of each group member
          group_epoch,              \* the current group epoch
          group_status,             \* the group status, such as RECONCILING or STABLE
          group_target_assignment,  \* the group's target assignment
          group_partition_epoch     \* the epoch of each partition in the group subscription

\* Client-side state
VARIABLES client_state,             \* the client-side member and hb state of each client
          client_recon_proc,        \* any ongoing reconciliation process of each client
          client_leave_proc         \* any ongoing leave process of each client

\* Auxilliary variables (not part of the protocol)
VARIABLES aux_member_id,            \* used to generate unique member ids
          aux_conn_id,              \* used to generate unique connections
          aux_fencing_ctr           \* used to count the number of fencings

\* variable groupings
group_vars == << group_members,
                 group_member_state,
                 group_epoch,
                 group_status,
                 group_target_assignment,
                 group_partition_epoch >>
client_vars == << client_state, client_recon_proc, client_leave_proc >>
aux_vars == <<aux_member_id, aux_conn_id, aux_fencing_ctr>>
vars == << group_vars, client_vars, messages, aux_vars >>

symmClients == Permutations(Clients)

\* The set of topics and topic partitions (fixed)
Topics == 1..TopicCount
TopicPartitions == (1..TopicCount) \X (1..PartitionsPerTopic)

GroupStatuses == {EMPTY, STABLE, ASSIGNING, RECONCILING }
ClientStatuses == {RECONCILING, STABLE, FENCED, UNSUBSCRIBED,
                   JOINING, ACKNOWLEDGING, PREPARE_LEAVING,
                   LEAVING, FATAL}
MemberStatuses == {STABLE, UNACKED_ASSIGNMENT, UNREL_PARTITIONS}
Errors == {FENCED_MEMBER_EPOCH, UNKNOWN_MEMBER_ID}

\* TRUE when the algorithm has converged on the target assignment
Converged ==
    /\ group_status = STABLE
    /\ \A c \in Clients :
        LET mid == client_state[c].member_id
        IN
           \* the client-side member state is stable
           /\ client_state[c].status = STABLE
           /\ client_state[c].member_epoch = group_epoch
           \* the server-side member state is stable
           /\ mid \in group_members
           /\ group_member_state[mid].status = STABLE
           /\ group_member_state[mid].member_epoch = group_epoch
    \* we repeat the server-side check as there may be group members which 
    /\ \A mid \in group_members :
        /\ group_member_state[mid].status = STABLE
        /\ group_member_state[mid].member_epoch = group_epoch

(* ------------------------------------------
   TYPES
   -----------------------------------------*)

GroupMemberState ==
    [host: Clients,
     member_id: Nat,
     member_epoch: Nat,
     prev_member_epoch: Nat,
     subscribed: SUBSET Topics,
     status: MemberStatuses,
     assigned_partitions: SUBSET TopicPartitions,
     revoked_partitions: SUBSET TopicPartitions]

JOIN_GROUP_MEMBER_EPOCH == 0
LEAVE_GROUP_MEMBER_EPOCH == -1

ClientState ==
    [host: Clients,
     connection_id: Nat,
     member_id: Nat,
     member_epoch: Nat \union {-1},
     status: ClientStatuses,
     subscribed: SUBSET Topics,
     curr_assignment: SUBSET TopicPartitions,
     last_sent_partitions: SUBSET TopicPartitions \union {Nil},
     assignment_to_reconcile: SUBSET TopicPartitions,
     has_inflight: BOOLEAN]
     
ReconcileProcess ==
    [epoch_on_start: Nat,
     assignment: SUBSET TopicPartitions]
     
LeaveProcess ==
    [assignment: SUBSET TopicPartitions]

HeartbeatRequest ==
    [type: {HeartbeatRequestMsg},
     member_id: Nat,
     member_epoch: Nat,
     subscribed: SUBSET Topics,
     topic_partitions: SUBSET TopicPartitions,
     connection_id: Nat,
     source: Clients]

HeartbeatResponse ==
    [type: {HeartbeatResponseMsg},
     error: Errors \union {Nil},
     member_epoch: Nat,
     member_id: Nat,
     assignment: SUBSET TopicPartitions \union {Nil},
     connection_id: Nat,
     dest: Clients]

(* ----------------------------------------------
     CLIENT ACTIONS 
   ----------------------------------------------*)

\* **********************************
\* Helpers

UpdateClientState(c, cs) ==
    \* Updates the state of client c.
    client_state' = [client_state EXCEPT ![c] = cs]

TransitionTo(prev, next) ==
    \* Illegal transitions return a sequence with the previous status,
    \* the proposed next status and the ILLEGAL_STATE constant. 
    \* This will violate the TypeOK invariant and allow you to view
    \* the illegal transition in the error trace.
    CASE prev = next ->
            next
      [] next = STABLE ->
            IF prev \in {JOINING, ACKNOWLEDGING, RECONCILING}
            THEN next ELSE <<prev, next, ILLEGAL_STATE>>
            
      [] next = RECONCILING ->
            IF prev \in {STABLE, JOINING, ACKNOWLEDGING}
            THEN next ELSE <<prev, next, ILLEGAL_STATE>>
            
      [] next = ACKNOWLEDGING ->
            IF prev = RECONCILING
            THEN next ELSE <<prev, next, ILLEGAL_STATE>>
            
      [] next = FATAL ->
            IF prev \in {JOINING, STABLE, RECONCILING, ACKNOWLEDGING,
                         PREPARE_LEAVING, LEAVING, UNSUBSCRIBED}
            THEN next ELSE <<prev, next, ILLEGAL_STATE>>
            
      [] next = FENCED ->
            IF prev \in {JOINING, STABLE, RECONCILING, ACKNOWLEDGING,
                         PREPARE_LEAVING, LEAVING}
            THEN next ELSE <<prev, next, ILLEGAL_STATE>>
            
      [] next = JOINING ->
            IF prev \in {FENCED, UNSUBSCRIBED}
            THEN next ELSE <<prev, next, ILLEGAL_STATE>>
            
      [] next = PREPARE_LEAVING ->
            IF prev \in {JOINING, STABLE, RECONCILING,
                         ACKNOWLEDGING, UNSUBSCRIBED, FENCED}
            THEN next ELSE <<prev, next, ILLEGAL_STATE>>
            
      [] next = LEAVING ->
            IF prev = PREPARE_LEAVING
            THEN next ELSE <<prev, next, ILLEGAL_STATE>>
            
      [] next = UNSUBSCRIBED ->
            IF prev \in {FENCED, LEAVING}
            THEN next ELSE <<prev, next, ILLEGAL_STATE>>
            
      [] OTHER -> <<prev, next, ILLEGAL_STATE>>

IsValidTransition(prev, next) ==
    TransitionTo(prev, next) \in ClientStatuses

NextClientStatus(cs) ==
    \* Selects the next client state on sending a heartbeat.
    CASE cs.status = UNSUBSCRIBED -> JOINING
      [] cs.status = ACKNOWLEDGING ->
            IF cs.assignment_to_reconcile = {}
            THEN STABLE
            ELSE RECONCILING
      [] cs.status = LEAVING -> UNSUBSCRIBED 
      [] OTHER -> cs.status

\* ----------------------------------------------
\* ACTION: SendHeartbeatRequest
\*
\* There is no inflight heartbeat so the client sends
\* a heartbeat request. See SendHeartbeatRequest for
\* more details on this logic.

\* Sends a heartbeat and updates the client state. Some notes:
    \* - only enabled when the system has not converged (to avoid infinite traces with simulation mode)
    \* - sets the topic_partitions field only when the current assignment
    \*   is not equal to the last sent value of the topic_partitions field.
    \* - If the topic_partitions is set, it records the value in last_sent_partitions
    \*   in the client state.
SendHeartbeatRequest(c) ==
    /\ client_state[c].has_inflight = FALSE
    /\ ~Converged
    /\ LET cs  == client_state[c]
           conn_id == IF cs.connection_id = 0 THEN aux_conn_id + 1 ELSE cs.connection_id
           send_partitions == IF cs.last_sent_partitions /= cs.curr_assignment
                              THEN TRUE ELSE FALSE
           next_status == NextClientStatus(cs)
           cs1 == [cs EXCEPT !.status = next_status,
                             !.subscribed = Topics, \* fixed topics for now
                             !.last_sent_partitions = IF send_partitions
                                                      THEN cs.curr_assignment
                                                      ELSE cs.last_sent_partitions,
                             !.connection_id = conn_id,
                             !.has_inflight = TRUE]
           cs2 == IF next_status = UNSUBSCRIBED
                  THEN [cs1 EXCEPT !.member_id = 0,
                                   !.member_epoch = 0]
                  ELSE cs1
       IN
          /\ client_state' = [client_state EXCEPT ![c] = cs2]
          /\ Send([type             |-> HeartbeatRequestMsg,
                   member_id        |-> cs.member_id,
                   member_epoch     |-> cs.member_epoch,
                   subscribed       |-> cs2.subscribed,
                   topic_partitions |-> IF send_partitions
                                        THEN cs.curr_assignment
                                        ELSE Nil,
                   connection_id    |-> conn_id,
                   source           |-> c])
          /\ IF conn_id > aux_conn_id
             THEN aux_conn_id' = conn_id
             ELSE UNCHANGED aux_conn_id
          /\ UNCHANGED << client_leave_proc, client_recon_proc,
                          group_vars, aux_member_id, aux_fencing_ctr >>               

\* ----------------------------------------------
\* ACTION: StartLeaveGroup
\*
\* 
                       
StartLeaveGroup(c) ==
    /\ aux_fencing_ctr < MaxFencings
    /\ client_state[c].member_epoch > 0
    /\ client_state[c].status \notin {UNSUBSCRIBED, PREPARE_LEAVING, LEAVING}
    /\ LET cs  == client_state[c]
           cs1 == [cs EXCEPT !.status = TransitionTo(cs.status, PREPARE_LEAVING)]
       IN /\ UpdateClientState(c, cs1)
          /\ client_leave_proc' = [client_leave_proc EXCEPT ![c] =
                                        [assignment |-> cs.curr_assignment]]
          /\ aux_fencing_ctr' = aux_fencing_ctr + 1
    /\ UNCHANGED << client_recon_proc, group_vars, messages, 
                    aux_member_id, aux_conn_id>> 

\* ----------------------------------------------
\* ACTION: CompleteLeaveGroup
\*
\* 

CompleteLeaveGroup(c) ==
    /\ client_leave_proc[c] /= Nil
    /\ LET cs  == client_state[c]
           cs_leave == [cs EXCEPT !.status = TransitionTo(cs.status, LEAVING),
                                  !.member_epoch = LEAVE_GROUP_MEMBER_EPOCH,
                                  !.subscribed = {},
                                  !.curr_assignment = {},
                                  !.last_sent_partitions = Nil,
                                  !.assignment_to_reconcile = {}]
       IN /\ CASE cs.status = PREPARE_LEAVING ->
                    UpdateClientState(c, cs_leave)
               [] OTHER ->
                    UNCHANGED client_state
          /\ client_leave_proc' = [client_leave_proc EXCEPT ![c] = Nil]
          /\ UNCHANGED << client_recon_proc, group_vars, messages, aux_vars >>

\* ----------------------------------------------
\* ACTION: CompleteReconciliation
\*
\* An ongoing reconcilation completes.
\* TODO: What to do when the epoch_on_start /= member_epoch?
\*       Currently just ends the process and leaves the client_state unchanged.

CompleteReconciliation(c) ==
     LET cs == client_state[c]
         recon == client_recon_proc[c]
     IN
       /\ recon /= Nil
       /\ client_recon_proc' = [client_recon_proc EXCEPT ![c] = Nil]
       /\ IF /\ cs.status = RECONCILING
             /\ recon.epoch_on_start = cs.member_epoch
          THEN UpdateClientState(c, 
                [cs EXCEPT !.status = TransitionTo(cs.status, ACKNOWLEDGING),
                           !.curr_assignment = recon.assignment,
                           !.assignment_to_reconcile = 
                                cs.assignment_to_reconcile \ recon.assignment])
          ELSE UNCHANGED client_state
       /\ UNCHANGED << client_leave_proc, group_vars, messages, aux_vars >>

\* ----------------------------------------------
\* ACTION: ReceiveErrorResponse
\*
\* An error response (fenced member).
\* If not already leaving, then it transitions atomically to FENCED then JOINING.
\* If it is leaving, then it only transitions to FENCED.

ReceiveErrorResponse(c) ==
    \E m \in DOMAIN messages :
        /\ ReceivableMsg(m, HeartbeatResponseMsg)
        /\ c = m.dest
        /\ client_state[c].connection_id = m.connection_id
        /\ m.error /= Nil
        /\ IF client_state[c].status = UNSUBSCRIBED
           THEN UpdateClientState(c, [client_state[c] EXCEPT !.has_inflight = FALSE])
           ELSE LET cs  == client_state[c]
                    cs1 == [cs EXCEPT !.member_id = 0, \* NOTE, can't see this in the code
                                      !.member_epoch = 0, 
                                      !.has_inflight = FALSE,
                                      !.curr_assignment = {},
                                      !.last_sent_partitions = Nil,
                                      !.assignment_to_reconcile = {},
                                      !.status = TransitionTo(cs.status, FENCED)]
                    cs_join == [cs1 EXCEPT !.status = TransitionTo(cs1.status, JOINING)]
                    cs_unsub == [cs1 EXCEPT !.status = TransitionTo(cs1.status, UNSUBSCRIBED)]
                IN IF cs.status \in {PREPARE_LEAVING, LEAVING}
                   THEN UpdateClientState(c, cs_unsub)
                   ELSE UpdateClientState(c, cs_join)
        /\ Discard(m)
        /\ UNCHANGED << client_leave_proc, client_recon_proc, group_vars, aux_vars >>

\* ----------------------------------------------
\* ACTION: ReceiveSuccessResponse
\*
\* 

ValidMemberId(c, m) ==
    IF client_state[c].member_id > 0
    THEN client_state[c].member_id = m.member_id
    ELSE TRUE

Reconcile(c, cs1, m) ==
    LET cs2 == [cs1 EXCEPT !.assignment_to_reconcile = m.assignment]
    IN
        IF client_recon_proc[c] /= Nil
        THEN /\ UpdateClientState(c, cs2)
             /\ UNCHANGED client_recon_proc
        ELSE /\ UpdateClientState(c, [cs2 EXCEPT !.status = TransitionTo(cs2.status, RECONCILING)])
             /\ client_recon_proc' = [client_recon_proc EXCEPT ![c] = 
                                            [epoch_on_start |-> cs2.member_epoch,
                                             assignment     |-> cs2.assignment_to_reconcile]]

ReceiveSuccessResponse(c) ==
    \E m \in DOMAIN messages :
        /\ ReceivableMsg(m, HeartbeatResponseMsg)
        /\ c = m.dest
        /\ m.error = Nil
\*        /\ ValidMemberId(c, m) EXPERIMENT
        /\ client_state[c].connection_id = m.connection_id
        /\ LET cs  == client_state[c]
               cs1 == [cs EXCEPT !.member_id = m.member_id,
                                 !.member_epoch = m.member_epoch,
                                 !.has_inflight = FALSE]
               cs_stable == [cs1 EXCEPT !.status = TransitionTo(cs.status, STABLE)]                                 
           IN
               CASE 
                 \* CASE 1: The client is unsubscribed so just discard the message
                    \/ client_state[m.dest].status \in {UNSUBSCRIBED, PREPARE_LEAVING, LEAVING} ->
                        \* TODO, member_id updated here or not?
                        /\ UpdateClientState(c, [cs EXCEPT !.has_inflight = FALSE])
                        /\ UNCHANGED client_recon_proc
                 \* CASE 2: The assignment is Nil
                 [] m.assignment = Nil ->
                        /\ IF cs1.assignment_to_reconcile = {}
                           THEN UpdateClientState(c, cs_stable)
                           ELSE UpdateClientState(c, cs1)
                        /\ UNCHANGED client_recon_proc
                 \* CASE 3: The assignment is non-Nil
                 [] m.assignment /= Nil ->    
                        IF IsValidTransition(cs.status, RECONCILING)
                        THEN 
                             IF m.assignment = cs.curr_assignment
                             THEN /\ \/ /\ cs.status = RECONCILING \* \in {JOINING, RECONCILING}
                                        /\ UpdateClientState(c, cs_stable)
                                     \/ /\ cs.status \notin {JOINING, RECONCILING}
                                        /\ UpdateClientState(c, cs1)
                                  /\ UNCHANGED client_recon_proc
                             ELSE Reconcile(c, cs1, m)
                        ELSE UpdateClientState(c, cs1)
                 
        /\ Discard(m)
        /\ UNCHANGED << client_leave_proc, group_vars, aux_vars >>

\* ----------------------------------------------
\* ACTION: ClientCrash
\*
\* 

ClientCrash(c) ==
     /\ aux_fencing_ctr < MaxFencings
     /\ client_state[c].member_epoch > 0
     /\ UpdateClientState(c, 
                    [host |-> c,
                     connection_id |-> 0,
                     member_id |-> 0,
                     member_epoch |-> 0,
                     subscribed |-> Topics, \* start already in a joining state
                     status |-> JOINING,    \* start already in a joining state
                     curr_assignment |-> {},
                     last_sent_partitions |-> Nil,
                     assignment_to_reconcile |-> {},
                     has_inflight |-> FALSE])
     /\ client_recon_proc' = [client_recon_proc EXCEPT ![c] = Nil]
     /\ client_leave_proc' = [client_leave_proc EXCEPT ![c] = Nil]
     /\ aux_fencing_ctr' = aux_fencing_ctr + 1
     /\ UNCHANGED << group_vars, messages, aux_member_id, aux_conn_id >>
        
(* ----------------------------------------------
     GROUP COORDINATOR ACTIONS 
   ----------------------------------------------*)

Reply(d, m) ==
    \* if the connection is still ok then send it, else if
    \* the connection failed, don't. Not required for
    \* correctness but reduces state-space a little.
    IF m.connection_id = client_state[m.dest].connection_id
    THEN SendReply(d, m)
    ELSE Discard(d)

NewMemberState(m, member_id) ==
    [host |-> m.source,
     member_id |-> member_id,
     member_epoch |-> 0,
     prev_member_epoch |-> 0,
     subscribed |-> m.subscribed,
     status |-> STABLE,
     assigned_partitions |-> {},
     revoked_partitions |-> {}]

UpdatedGroupMemberState(mid, updated_member) ==
    IF mid \notin group_members
    THEN group_member_state @@ (mid :> updated_member)
    ELSE [group_member_state EXCEPT ![mid] = updated_member]

BuildAssignment(partitions, updated_members, new_epoch) ==
     \E candidates \in kSubset(Cardinality(partitions),
                               [partition: partitions,
                                member: DOMAIN updated_members]) :
        /\ \A p \in partitions :
            \E ca \in candidates : ca.partition = p 
        /\ \A ca \in candidates :
            ca.partition[1] \in updated_members[ca.member].subscribed
        /\ LET filter_by_member(c) == { ca \in candidates : ca.member = c}
               assignment == [c \in DOMAIN updated_members
                                |-> {ca.partition : ca \in filter_by_member(c)}]
           IN group_target_assignment' = [epoch       |-> new_epoch,
                                          assignments |-> assignment]

CreateNewAssignment(mid, updated_member, new_epoch) ==
    LET updated_members == UpdatedGroupMemberState(mid, updated_member)
        partitions == TopicPartitions
    IN BuildAssignment(partitions, updated_members, new_epoch)

RemoveOldAddNew(old_partitions, new_partitions, p_epochs, updated_member) ==
    LET p_epochs1  == IF old_partitions /= new_partitions
                      THEN [p \in TopicPartitions |->
                               IF p \in old_partitions
                               THEN 0
                               ELSE p_epochs[p]]
                      ELSE p_epochs
        p_epochs2  == IF old_partitions /= new_partitions
                      THEN [p \in TopicPartitions |->
                               IF p \in new_partitions
                               THEN updated_member.member_epoch
                               ELSE p_epochs1[p]]
                      ELSE p_epochs1
    IN p_epochs2

MaybeUpdatePartitionEpochs(mid, updated_member) ==
    IF mid \notin group_members
    THEN group_partition_epoch' = 
                    [p \in TopicPartitions |->
                        IF \/ p \in updated_member.assigned_partitions
                           \/ p \in updated_member.revoked_partitions
                        THEN updated_member.member_epoch
                        ELSE group_partition_epoch[p]]
    ELSE LET old_member == group_member_state[mid]
             new_member == updated_member
             p_epochs   == group_partition_epoch
             p_epochs1  == IF old_member.assigned_partitions /= new_member.assigned_partitions
                           THEN RemoveOldAddNew(old_member.assigned_partitions,
                                                new_member.assigned_partitions,
                                                p_epochs, updated_member)
                           ELSE p_epochs
             p_epochs2  == IF old_member.revoked_partitions /= new_member.revoked_partitions
                           THEN RemoveOldAddNew(old_member.revoked_partitions,
                                                new_member.revoked_partitions,
                                                p_epochs1, updated_member)
                           ELSE p_epochs1
          IN group_partition_epoch' = p_epochs2

\*MaybeRemovePartitionEpoch(removed_member) ==
\*    group_partition_epoch' = [p \in TopicPartitions |->
\*                                   IF p \in removed_member.assigned_partitions
\*                                   THEN 0 ELSE group_partition_epoch[p]]
            
ComputeNextAssignment(updated_member, target_assignment, target_epoch) ==
    LET keep_partitions == updated_member.assigned_partitions \intersect target_assignment
        pending_revoke == updated_member.assigned_partitions \ keep_partitions
        pending_assign == target_assignment \ keep_partitions
        pending_assign1 == { p \in pending_assign : group_partition_epoch[p] = 0 }
        has_unrel       == pending_assign /= pending_assign1
    IN 
        CASE Cardinality(pending_revoke) > 0 ->
                [updated_member EXCEPT 
                              !.status              = UNACKED_ASSIGNMENT,
                              !.assigned_partitions = keep_partitions,
                              !.revoked_partitions  = pending_revoke]
          [] Cardinality(pending_assign1) > 0 ->
                [updated_member EXCEPT 
                              !.status              = UNACKED_ASSIGNMENT,
                              !.member_epoch        = target_epoch,
                              !.assigned_partitions = keep_partitions \union pending_assign1,
                              !.revoked_partitions  = {}]
          [] has_unrel = TRUE ->
                [updated_member EXCEPT 
                              !.status              = UNREL_PARTITIONS,
                              !.member_epoch        = target_epoch,
                              !.assigned_partitions = keep_partitions,
                              !.revoked_partitions  = {}]
          [] OTHER ->
                [updated_member EXCEPT 
                              !.status              = STABLE,
                              !.member_epoch        = target_epoch,
                              !.assigned_partitions = keep_partitions,
                              !.revoked_partitions  = {}]

IsReconciled(member, grp_epoch) ==
    /\ member.status = STABLE
    /\ member.member_epoch = grp_epoch

MaybeUpdateGroupState(member_state, grp_epoch, target_epoch) ==
    CASE DOMAIN member_state = {} ->
            group_status' = EMPTY
      [] grp_epoch > target_epoch ->
            group_status' = ASSIGNING
      [] OTHER ->
            IF \E mid \in DOMAIN member_state : ~IsReconciled(member_state[mid], grp_epoch)
            THEN group_status' = RECONCILING
            ELSE group_status' = STABLE

IsLeaving(m) ==
    /\ m.member_id \in group_members
    /\ group_member_state[m.member_id].member_epoch /= LEAVE_GROUP_MEMBER_EPOCH
    /\ m.member_epoch = LEAVE_GROUP_MEMBER_EPOCH

ShouldFence(m) ==
    /\ m.member_id \in group_members
    /\ m.member_epoch /= LEAVE_GROUP_MEMBER_EPOCH
    /\ group_member_state[m.member_id].member_epoch /= m.member_epoch
    
IsUnknown(m) ==
    /\ m.member_id \notin group_members
    /\ m.member_id /= 0

FenceMember(mid) ==
    LET updated_member == [assigned_partitions |-> {},
                           revoked_partitions  |-> {}]
        new_members       == group_members \ {mid}
        new_group_epoch   == group_epoch + 1
        new_members_state == [mid1 \in new_members |-> group_member_state[mid1]]
                                    
    IN /\ group_members' = new_members
       /\ group_epoch' = new_group_epoch
       /\ group_member_state' = new_members_state
       /\ MaybeUpdateGroupState(new_members_state, new_group_epoch, 
                                group_target_assignment.epoch)
       /\ MaybeUpdatePartitionEpochs(mid, updated_member)
       /\ UNCHANGED << group_target_assignment >> 

\* ----------------------------------------------------
\* ACTION: ReceiveBadHeartbeatRequest
\*
\* Receive a non-joining heartbeat from a non-member
\* or receive a regular heartbeat with a non-matching member epoch.

ReceiveBadHeartbeatRequest(c) ==
    \E m \in DOMAIN messages :
        /\ ReceivableMsg(m, HeartbeatRequestMsg)
        /\ c = m.source
        /\ CASE IsUnknown(m) ->
                 /\ Reply(m, [type          |-> HeartbeatResponseMsg,
                              error         |-> UNKNOWN_MEMBER_ID,
                              member_epoch  |-> 0,
                              member_id     |-> 0,
                              assignment    |-> Nil,
                              connection_id |-> m.connection_id,
                              dest          |-> c])
                 /\ UNCHANGED <<client_vars, group_vars, aux_vars>>
             [] ShouldFence(m) ->
                 /\ FenceMember(m.member_id)
                 /\ Reply(m, [type          |-> HeartbeatResponseMsg,
                              error         |-> FENCED_MEMBER_EPOCH,
                              member_epoch  |-> 0,
                              member_id     |-> 0,
                              assignment    |-> Nil,
                              connection_id |-> m.connection_id,
                              dest          |-> c])
                 /\ UNCHANGED <<client_vars, aux_vars>> 
             [] OTHER -> FALSE

\* ----------------------------------------------------
\* ACTION: ReceiveLeaveHeartbeatRequest
\*
\* Receive a leaving heartbeat from a member.

ReceiveLeaveHeartbeatRequest(c) ==
    \E m \in DOMAIN messages :
        /\ ReceivableMsg(m, HeartbeatRequestMsg)
        /\ c = m.source
        /\ IsLeaving(m)
        /\ FenceMember(m.member_id)
        /\ Reply(m, [type          |-> HeartbeatResponseMsg,
                     error         |-> Nil,
                     member_epoch  |-> LEAVE_GROUP_MEMBER_EPOCH,
                     member_id     |-> m.member_id,
                     assignment    |-> Nil,
                     connection_id |-> m.connection_id,
                     dest          |-> c])
    /\ UNCHANGED << group_target_assignment, client_vars, aux_vars >>

\* ----------------------------------------------------
\* ACTION: ReceiveRegularHeartbeatRequest
\*
\* Receive a joining or regular heartbeat.

ReceiveRegularHeartbeatRequest(c) ==
    \E m \in DOMAIN messages :
        /\ ReceivableMsg(m, HeartbeatRequestMsg)
        /\ c = m.source
        /\ ~IsUnknown(m)
        /\ ~ShouldFence(m)
        /\ ~IsLeaving(m)
        /\ LET member_id      == IF m.member_id = 0 THEN aux_member_id + 1 ELSE m.member_id
               updated_member == IF m.member_id = 0
                                 THEN NewMemberState(m, member_id)
                                 ELSE [group_member_state[member_id] EXCEPT !.subscribed = m.subscribed]
               bump_epoch     == \/ member_id \notin group_members
                                 \/ group_member_state[member_id].subscribed /= updated_member.subscribed
               new_group_epoch   == IF bump_epoch THEN group_epoch + 1 ELSE group_epoch
               new_target_epoch  == new_group_epoch
               new_members       == group_members \union {member_id}
               new_target_assignment == group_target_assignment'.assignments
               updated_member1   == IF /\ ~IsReconciled(updated_member, new_group_epoch)
                                       /\ \/ /\ updated_member.status = STABLE
                                             /\ updated_member.member_epoch /= new_group_epoch
                                          \/ /\ updated_member.status = UNACKED_ASSIGNMENT
                                             /\ m.topic_partitions = updated_member.assigned_partitions
                                          \/ updated_member.status = UNREL_PARTITIONS
                                    THEN ComputeNextAssignment(updated_member, 
                                                               new_target_assignment[member_id],
                                                               new_target_epoch)
                                    ELSE updated_member
               send_assignment   == \/ m.topic_partitions /= Nil
                                    \/ m.member_epoch = 0
                                    \/ updated_member1.status = UNACKED_ASSIGNMENT
           IN /\ group_members' = new_members
              /\ group_epoch' = new_group_epoch
              /\ IF new_group_epoch > group_target_assignment.epoch \* TODO check
                 THEN CreateNewAssignment(member_id, updated_member, new_group_epoch)
                 ELSE UNCHANGED group_target_assignment
              /\ group_member_state' = UpdatedGroupMemberState(member_id, updated_member1)
              /\ MaybeUpdateGroupState(group_member_state', new_group_epoch, new_target_epoch)
              /\ MaybeUpdatePartitionEpochs(member_id, updated_member1)
              /\ Reply(m, [type          |-> HeartbeatResponseMsg,
                           error         |-> Nil,
                           member_epoch  |-> updated_member1.member_epoch,
                           member_id     |-> updated_member1.member_id,
                           assignment    |-> IF send_assignment = TRUE
                                            THEN updated_member1.assigned_partitions
                                            ELSE Nil,
                           connection_id |-> m.connection_id,
                           dest          |-> c])
              /\ aux_member_id' = IF m.member_id = 0 THEN member_id ELSE aux_member_id
    /\ UNCHANGED << client_vars, aux_fencing_ctr, aux_conn_id >>

\* ----------------------------------------------------
\* ACTION: MemberExpired
\*
\* Arbitrarily fences a group member.

DeadMemberExpired ==
    \E mid \in group_members :
        LET c == group_member_state[mid].host
        IN /\ client_state[c].member_id /= mid
           /\ client_state[c].member_id /= 0
           /\ client_state[c].status /= JOINING
           /\ FenceMember(mid)
           /\ UNCHANGED << client_vars, messages, aux_vars >>
        
LiveMemberExpired(c) ==
    /\ aux_fencing_ctr < MaxFencings
    /\ \E mid \in group_members :
        /\ group_member_state[mid].host = c
        /\ FenceMember(mid)
        /\ aux_fencing_ctr' = aux_fencing_ctr + 1
        /\ UNCHANGED << client_vars, messages, aux_member_id, aux_conn_id >>        

(* ----------------------------------------------
   INVARIANTS
   ----------------------------------------------*)

\* INV: TypeOK ----------------------------------
\* Checks that the variables have correct types.
ValidGroupAssignment(assignment) ==
    /\ assignment.epoch \in Nat
    /\ \A mid \in DOMAIN assignment.assignments :
        assignment.assignments[mid] \in SUBSET TopicPartitions

TypeOK ==
    /\ \A mid \in DOMAIN group_member_state : group_member_state[mid] \in GroupMemberState
    /\ group_epoch \in Nat
    /\ group_target_assignment.epoch \in Nat
    /\ ValidGroupAssignment(group_target_assignment)
    /\ group_partition_epoch \in [TopicPartitions -> Nat]
    /\ group_status \in GroupStatuses
    /\ client_state \in [Clients -> ClientState]
    /\ client_recon_proc \in [Clients -> ReconcileProcess \union {Nil}]
    /\ client_leave_proc \in [Clients -> LeaveProcess \union {Nil}]
    /\ aux_member_id \in Nat
    /\ aux_fencing_ctr \in Nat

\* INV: AllPartitionsAssigned
\* A target assignment cannot leave out any partitions of the group subscription
AllPartitionsAssigned ==
    \/ group_target_assignment.assignments = <<>>
    \/ /\ group_target_assignment.assignments /= <<>>
       /\ \A p \in TopicPartitions :
           \E c \in DOMAIN group_target_assignment.assignments :
               p \in group_target_assignment.assignments[c]
               
\* INV: NoDoubleTargetAssignment
\* No partition can be assigned to more than one member
NoDoubleTargetAssignment ==
    \/ group_target_assignment.assignments = <<>>
    \/ /\ group_target_assignment.assignments /= <<>>
       /\ \A p \in TopicPartitions :
           ~\E mid1, mid2 \in DOMAIN group_target_assignment.assignments :
                /\ mid1 /= mid2
                /\ p \in group_target_assignment.assignments[mid1]
                /\ p \in group_target_assignment.assignments[mid2]               

\* INV: NoDoubleClientAssignment
\* No two clients, which are current group members, can both believe
\* they are assigned the same partition.
NoDoubleClientAssignment ==
    ~\E c1, c2 \in DOMAIN client_state :
        /\ c1 /= c2
        /\ client_state[c1].member_id \in group_members
        /\ client_state[c2].member_id \in group_members
        /\ \E p \in TopicPartitions : 
            /\ p \in client_state[c1].curr_assignment
            /\ p \in client_state[c2].curr_assignment

ConsistentClient ==
    \A c \in Clients :
        LET cs  == client_state[c]
            mid == cs.member_id
            target_epoch == group_target_assignment.epoch
            target_assignment == group_target_assignment.assignments[mid]
        IN
            (/\ cs.status = STABLE
             /\ cs.member_epoch = target_epoch) => 
                    (cs.curr_assignment = target_assignment)

\* INV: ValidMemberEpoch
\* A member cannot have reached the group epoch if it has
\* partitions to revoke.
ValidMemberEpoch ==
    /\ ~\E mid \in group_members :
        /\ group_member_state[mid].member_epoch = group_epoch
        /\ group_member_state[mid].revoked_partitions /= {}
    /\ ~\E c \in Clients :
        /\ client_state[c].member_epoch = group_epoch
        /\ client_state[c].member_id \in group_members
        /\ group_member_state[client_state[c].member_id].revoked_partitions /= {}
        
\* INV: ValidReconcileState
\* TODO: check this, it is not true
ValidReconcileState ==
    \A c \in Clients :
        client_state[c].status = RECONCILING => client_recon_proc[c] /= Nil 

\* INV: ValidLeaveState
\* When in PREPARE_LEAVING, there must be a leave process
ValidLeaveState ==
    \A c \in Clients :
        client_state[c].status = PREPARE_LEAVING => client_leave_proc[c] /= Nil

\* INV: ValidStableGroupState
\* If the group state is STABLE, this implies that all group members:
\* 1. Have status=STABLE.
\* 2. Have a member epoch the matches the group epoch.
\* 3. Have no revoked partitions. 
\* 4. Have reported assigned partitions that match their assignment. 
ValidStableGroupState ==
    (group_status = STABLE) => 
        (\A mid \in group_members :
            /\ group_member_state[mid].status = STABLE
            /\ group_member_state[mid].member_epoch = group_epoch
            /\ group_member_state[mid].revoked_partitions = {}
            /\ group_member_state[mid].assigned_partitions = group_target_assignment.assignments[mid])

\* for debugging. Set to TRUE to disable it.
TestInv ==
    TRUE
\*    TLCGet("level") < 70

\* LIVENESS -------------------------------------

\* LIVENESS: EventuallyConverges
\* This specification places limits on perturbations, but not on
\* actions that lead to convergence, therefore the system should
\* always converge eventually (meaning that all members assume the
\* target assignment).
EventuallyConverges ==
    ~Converged ~> Converged

\* LIVENESS: MemberEpochIsMonotonic
\* A client's member epoch can only decrease if it
\* gets set to the joining or leaving value.
MemberEpochIsMonotonic ==
    \A c \in Clients :
        [][client_state[c]' /= client_state[c] 
            => \/ client_state[c]'.member_epoch <= 0
               \/ client_state[c]'.member_epoch >= client_state[c].member_epoch]_vars

\* for debugging. Set to TRUE to disable it.
TestLiveness ==
    TRUE

\* INIT and NEXT --------------------------------

Next ==
    \/ \E c \in Clients :
        \* client actions
        \/ SendHeartbeatRequest(c)
        \/ ReceiveErrorResponse(c)
        \/ ReceiveSuccessResponse(c)
        \/ CompleteReconciliation(c)
        \/ StartLeaveGroup(c)
        \/ CompleteLeaveGroup(c)
        \/ ClientCrash(c)
        \* coordinator actions
        \/ ReceiveRegularHeartbeatRequest(c)
        \/ ReceiveLeaveHeartbeatRequest(c)
        \/ ReceiveBadHeartbeatRequest(c)
        \/ LiveMemberExpired(c)
    \/ DeadMemberExpired

Init ==
    /\ group_members = {}
    /\ group_member_state = [c \in {} |-> Nil]
    /\ group_epoch = 0
    /\ group_status = EMPTY
    /\ group_target_assignment = [epoch |-> 0,
                                  assignments |-> <<>>]
    /\ group_partition_epoch = [p \in TopicPartitions |-> 0]
    /\ client_state = [c \in Clients |->
                           [host |-> c,
                            connection_id |-> 0,
                            member_id |-> 0,
                            member_epoch |-> JOIN_GROUP_MEMBER_EPOCH,
                            subscribed |-> Topics, \* start already in a joining state
                            status |-> JOINING,    \* start already in a joining state
                            curr_assignment |-> {},
                            last_sent_partitions |-> Nil,
                            assignment_to_reconcile |-> {},
                            has_inflight |-> FALSE]]
    /\ client_recon_proc = [c \in Clients |-> Nil]
    /\ client_leave_proc = [c \in Clients |-> Nil]
    /\ aux_member_id = 0
    /\ aux_conn_id = 0
    /\ aux_fencing_ctr = 0
    /\ messages = [m \in {} |-> 0]
    
\* For all clients, if an action that leads to convergence
\* is enabled (forever), then eventually it must happen.
\* Perturbation actions, such as leaving a group and fencing 
\* a live member are not given fairness as we don't need for
\* them to occur to reach convergence.
Fairness ==
    /\ \A c \in Clients :
        /\ WF_vars(SendHeartbeatRequest(c))
        /\ WF_vars(ReceiveErrorResponse(c))
        /\ WF_vars(ReceiveSuccessResponse(c))
        /\ WF_vars(CompleteReconciliation(c))
        /\ WF_vars(CompleteLeaveGroup(c))
        /\ WF_vars(ReceiveRegularHeartbeatRequest(c))
        /\ WF_vars(ReceiveLeaveHeartbeatRequest(c))
        /\ WF_vars(ReceiveBadHeartbeatRequest(c))
    /\ WF_vars(DeadMemberExpired)    
    
Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

=============================================================================