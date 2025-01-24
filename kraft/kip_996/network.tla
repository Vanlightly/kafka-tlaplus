--------------------------- MODULE network ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC

(*
    This file includes all message passing and network connectivity logic.
*)

\* Limits the number of times connectivity between server
\* pairs can change.
CONSTANT MaxConnectivityChanges 

VARIABLES net_messages,           \* the messages sent but not received
          net_messages_processed, \* the messages already processed
          net_connectivity,       \* map of KEY: set of server pairs, VALUE: TRUE/FALSE for connectivity
          net_connectivity_ctr    \* the number of times connectivity has changed

NetworkView == << net_messages, net_connectivity>>
NetworkVars == << net_messages,
                  net_messages_processed,
                  net_connectivity,
                  net_connectivity_ctr >>

Messages == net_messages
ProcessedMessages == net_messages_processed

ServerPairs(servers) == 
    { s \in SUBSET servers : Cardinality(s) = 2 }

\* All servers start connected to each other.
NetworkInit(servers) == 
    /\ net_messages = {}
    /\ net_messages_processed = {}
    /\ net_connectivity = [pairs \in ServerPairs(servers) |-> TRUE]
    /\ net_connectivity_ctr = 0

\* ======================================================================
\* Network connectivity -------------------------------------------------

Drop(msgs) ==
    (*
        Drops the set of messages.
    *)
    /\ net_messages' = net_messages \ msgs
    /\ UNCHANGED net_messages_processed

NewConnectedPairs == 
    (*
        Returns all possible subsets of connected server pairs.
    *)
    SUBSET DOMAIN net_connectivity

CanChangeConnectivity ==
    net_connectivity_ctr < MaxConnectivityChanges

ChangeConnectivity(connected) ==
    (*
        Updates the connected server to match the provided set of
        connected servers. Also drops any inflight messages between
        servers that have just lost connectivity.
    *)
    /\ net_connectivity' = [pair \in DOMAIN net_connectivity |->
                                IF pair \in connected
                                THEN TRUE
                                ELSE FALSE]
    /\ Drop({m \in net_messages : 
                ~\E pair \in connected :
                    /\ m.source \in pair
                    /\ m.dest \in pair})
    /\ net_connectivity_ctr' = net_connectivity_ctr + 1

Connected(s1, s2) ==
    (*
        TRUE if the two servers have visibility of each other.
    *)
    /\ s1 # s2
    /\ \E pair \in DOMAIN net_connectivity :
        /\ s1 \in pair
        /\ s2 \in pair
        /\ net_connectivity[pair] = TRUE
    
NumConnections(target, servers) ==
    (*
        The number of connections the target server has. So in a 
        cluster of 3, if s1 is connected to s2 and s3 the result is 2.
    *)
    Quantify(servers, LAMBDA s : 
                    /\ s # target
                    /\ \E pair \in DOMAIN net_connectivity :
                        /\ target \in pair
                        /\ s \in pair
                        /\ net_connectivity[pair] = TRUE)

ConnectedPairsWithoutServer(s) ==
    (*
        The number of connected server pairs, if server s were removed.
    *)
    { pair \in DOMAIN net_connectivity : 
        /\ s \notin pair
        /\ net_connectivity[pair] = TRUE }

DisconnectServer(server) ==
    (*
        Disconnect the provided server. Drop all its incoming
        and outgoing inflight messages.
    *)
    LET new_conn == [pair \in DOMAIN net_connectivity |->
                                IF server \in pair
                                THEN FALSE
                                ELSE net_connectivity[pair]]
    IN /\ net_connectivity' = new_conn 
       /\ Drop({m \in net_messages : 
                    \/ m.source = server
                    \/ m.dest = server})
       /\ UNCHANGED << net_connectivity_ctr >>

\* ======================================================================
\* ----- Message passing ------------------------------------------------

SendFunc(m, msgs, deliver_count) ==
    (*
        Send the message whether it already exists or not.
        If it does exist, the delivery count will go above 1 and
        the message can be delivered multiple times.
    *)
    IF deliver_count > 0
    THEN msgs \union {m}
    ELSE msgs

DiscardFunc(m, msgs) ==
    (*
        Remove a message from the bag of messages. Used when a 
        server is done processing a message.
    *)
    msgs \ {m}

Send(m) ==
    (*
        Send a message, but if the connection is down, lose the message.
    *)
    /\ net_messages' = IF Connected(m.dest, m.source)
                       THEN SendFunc(m, net_messages, 1)
                       ELSE SendFunc(m, net_messages, 0)
    /\ UNCHANGED << net_messages_processed, net_connectivity, net_connectivity_ctr >>

RECURSIVE SendAllFunc(_,_)
SendAllFunc(send_msgs, msgs) ==
    (*
        Send a set of messages. Lose any messages on connections
        that are down.
    *)
    IF send_msgs = {}
    THEN msgs
    ELSE LET m == CHOOSE m \in send_msgs : TRUE
             new_msgs == IF Connected(m.dest, m.source)
                         THEN SendFunc(m, msgs, 1)
                         ELSE SendFunc(m, msgs, 0)
             remaining == send_msgs \ {m}
         IN SendAllFunc(remaining, new_msgs)

SendAll(msgs) ==
    /\ net_messages' = SendAllFunc(msgs, net_messages)
    /\ UNCHANGED << net_messages_processed, net_connectivity, 
                    net_connectivity_ctr >>

SendAllOnce(msgs) ==
    (*
        Sends all the messages.
    *)
\*    /\ ~\E m \in msgs :
\*        \/ m \in net_messages
\*        \/ m \in net_messages_processed
    /\ net_messages' = SendAllFunc(msgs, net_messages)
    /\ UNCHANGED << net_messages_processed, net_connectivity, net_connectivity_ctr >>    

DiscardAndSendAll(d, msgs) ==
    (*
        Discards message (d) and sends all the messages of set (msgs).
    *)
    /\ net_messages' = SendAllFunc(msgs, DiscardFunc(d, net_messages))
    /\ net_messages_processed' = net_messages_processed \union {d}
    /\ UNCHANGED << net_connectivity, net_connectivity_ctr >>

Discard(d) ==
    (*
        Discards the message and adds it to the processed set.
    *)
    /\ net_messages' = DiscardFunc(d, net_messages)
    /\ net_messages_processed' = net_messages_processed \union {d}
    /\ UNCHANGED << net_connectivity, net_connectivity_ctr >>
    
Reply(d, m) ==
    (*
        Discards one message and sends another.
    *)
    /\ Connected(m.dest, m.source)
    /\ d \in net_messages
    /\ net_messages' = SendFunc(m, DiscardFunc(d, net_messages), 1)
    /\ net_messages_processed' = net_messages_processed \union {d}
    /\ UNCHANGED << net_connectivity, net_connectivity_ctr >>

HasInflightVoteReq(s, type, pre_vote) ==
    (*
        TRUE if the server has any outbound requests inflight.
        Used to figure out if a timeout should occur.
    *)
    \E m \in net_messages :
        /\ m.type = type
        /\ m.pre_vote = pre_vote
        /\ m.source = s

HasInflightVoteRes(s, type, pre_vote) ==
    (*
        TRUE if the server has any inbound responses inflight.
        Used to figure out if a timeout should occur.
    *)
    \E m \in net_messages :
        /\ m.type = type
        /\ m.pre_vote = pre_vote
        /\ m.dest = s

NotLostReqWithReplicaEpoch(source, dest, type, epoch) ==
    (*
        Figures out if a server never received a BeginQuorumEpochRequest
        it needs. TRUE if the request has been processed or is 
        still inflight.
    *)
    \/ \E m \in net_messages :
        /\ m.type = type
        /\ m.replica_epoch = epoch
        /\ m.source = source
        /\ m.dest = dest
    \/ \E m \in net_messages_processed :
        /\ m.type = type
        /\ m.source = source
        /\ m.replica_epoch = epoch
        /\ m.dest = dest

FetchRequestOrResLost(req, type) ==
    (*
        Figures out if a fetch request or its corresponding
        response has been lost. This is needed to detect
        a fetch timeout.
    *)
    /\ req \notin net_messages
    /\ ~\E res \in net_messages :
        /\ res.type = type
        /\ res.correlation = req

=============================================================================    