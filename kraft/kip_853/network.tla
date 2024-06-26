--------------------------- MODULE network ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC

CONSTANT MaxDisconnectedPairs,
         MaxConnectivityChanges \* Limits the number of times connectivity between server
                                \* pairs can change.

VARIABLES net_messages,
          net_messages_processed,
          net_connectivity,
          net_connectivity_ctr    \* the number of times connectivity changes

NetworkView == << net_messages, net_connectivity>>
NetworkVars == << net_messages,
                  net_messages_processed,
                  net_connectivity,
                  net_connectivity_ctr >>

Messages == net_messages
ProcessedMessages == net_messages_processed

ServerPairs(servers) == 
    { s \in SUBSET servers : Cardinality(s) = 2 }

NetworkInit(servers) == 
    /\ net_messages = {}
    /\ net_messages_processed = {}
    /\ net_connectivity = [pairs \in ServerPairs(servers) |-> TRUE]
    /\ net_connectivity_ctr = 0

----

Drop(msgs) ==
    /\ net_messages' = net_messages \ msgs
    /\ net_messages_processed' = net_messages_processed \union msgs

\* Network state transitions

\* Any dead servers are included in network disconnection
\* to avoid the combination of server death and networking
\* issues from causing a cluster to be unable to form
\* a majority of connected servers (which is a fundamental
\* requisite for KRaft).

PairMatch(servers, pair) ==
    \E s \in servers : s \in pair
    
WholeCohortInPairs(servers, pairs) ==
    \A s \in servers :
        \E p \in pairs : s \in p
        
IncludesAllDead(dead_servers, disconnected_pairs) ==
    /\ WholeCohortInPairs(dead_servers, disconnected_pairs)
    /\ ~\E pair \in DOMAIN net_connectivity :
        /\ PairMatch(dead_servers, pair)
        /\ pair \notin disconnected_pairs    

DisconnectedCount(net_conn) ==
    Quantify(DOMAIN net_conn, 
             LAMBDA pair : net_conn[pair] = FALSE)

ChangeConnectivity(dead_servers) ==
    /\ net_connectivity_ctr < MaxConnectivityChanges
    /\ \E disconnected_pairs \in SUBSET DOMAIN net_connectivity :
        \* the new disconnected set must include dead servers
        /\ IncludesAllDead(dead_servers, disconnected_pairs)
        \* if we're already over the disconnected limit, then reduce
        \* the number of disconnected pairs, else simply stay at or below the limit
        /\ IF DisconnectedCount(net_connectivity) > MaxDisconnectedPairs
           THEN Cardinality(disconnected_pairs) < DisconnectedCount(net_connectivity)
           ELSE Cardinality(disconnected_pairs) <= MaxDisconnectedPairs
        \* make sure the new disconnected set is different to the current
        /\ IF Cardinality(disconnected_pairs) = DisconnectedCount(net_connectivity)
           THEN \E pair \in disconnected_pairs :
                    net_connectivity[pair] = TRUE
           ELSE TRUE
        /\ net_connectivity' = [pair \in DOMAIN net_connectivity |->
                                    IF pair \in disconnected_pairs
                                    THEN FALSE
                                    ELSE TRUE]
        /\ Drop({m \in net_messages : 
                    \E pair \in disconnected_pairs :
                        /\ m.source \in pair
                        /\ m.dest \in pair})
    /\ net_connectivity_ctr' = net_connectivity_ctr + 1
    
\* ======================================================================
\* ----- Message passing ------------------------------------------------

Connected(s1, s2) ==
    \/ s1 = s2
    \/ \E pair \in DOMAIN net_connectivity :
        /\ s1 \in pair
        /\ s2 \in pair
        /\ net_connectivity[pair] = TRUE
    
ConnectedServers(target, servers) ==
    1 + Quantify(servers, LAMBDA s : 
                        /\ s # target
                        /\ \E pair \in DOMAIN net_connectivity :
                            /\ target \in pair
                            /\ s \in pair
                            /\ net_connectivity[pair] = TRUE)

ConnectedMajority(target, servers) ==
    ConnectedServers(target, servers) > Cardinality(servers) \div 2

DisconnectDeadServer(dead_server) ==
    LET new_conn == [pair \in DOMAIN net_connectivity |->
                                IF dead_server \in pair
                                THEN FALSE
                                ELSE net_connectivity[pair]]
    IN /\ DisconnectedCount(new_conn) <= MaxDisconnectedPairs
       /\ net_connectivity' = new_conn 
       /\ Drop({m \in net_messages : 
                    \/ m.source = dead_server
                    \/ m.dest = dead_server})
       /\ UNCHANGED << net_connectivity_ctr >>


\* Send the message whether it already exists or not.
\* If it does exist, the delivery count will go above 1 and
\* the message can be delivered multiple times.
SendFunc(m, msgs, deliver_count) ==
    IF deliver_count > 0
    THEN msgs \union {m}
    ELSE msgs

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
DiscardFunc(m, msgs) ==
    msgs \ {m}

\* Send a message, without restriction
Send(m) ==
    /\ net_messages' = IF Connected(m.dest, m.source)
                       THEN SendFunc(m, net_messages, 1)
                       ELSE SendFunc(m, net_messages, 0)
    /\ UNCHANGED << net_messages_processed, net_connectivity, net_connectivity_ctr >>

RECURSIVE SendAllFunc(_,_)
SendAllFunc(send_msgs, msgs) ==
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
    /\ UNCHANGED << net_messages_processed, net_connectivity, net_connectivity_ctr >>

\* Guarantees the message is sent once. Used to disable an action without
\* an explicit variable.
SendAllOnce(msgs) ==
    /\ ~\E m \in msgs :
        \/ m \in net_messages
        \/ m \in net_messages_processed
    /\ net_messages' = SendAllFunc(msgs, net_messages)
    /\ UNCHANGED << net_messages_processed, net_connectivity, net_connectivity_ctr >>    

DiscardAndSendAll(d, msgs) ==
    /\ net_messages' = SendAllFunc(msgs, DiscardFunc(d, net_messages))
    /\ net_messages_processed' = net_messages_processed \union {d}
    /\ UNCHANGED << net_connectivity, net_connectivity_ctr >>

\* Set the delivery count to 0 so the message cannot be processed again.
Discard(d) ==
    /\ net_messages' = DiscardFunc(d, net_messages)
    /\ net_messages_processed' = net_messages_processed \union {d}
    /\ UNCHANGED << net_connectivity, net_connectivity_ctr >>
    
\* Discard incoming message and reply with another    
Reply(d, m) ==
    /\ Connected(m.dest, m.source)
    /\ d \in net_messages
    /\ net_messages' = SendFunc(m, DiscardFunc(d, net_messages), 1)
    /\ net_messages_processed' = net_messages_processed \union {d}
    /\ UNCHANGED << net_connectivity, net_connectivity_ctr >>

PreviouslySent(m) ==
    \/ m \in net_messages
    \/ m \in net_messages_processed    

HasInflightVoteReq(s, type) ==
    \E m \in net_messages :
        /\ m.type = type
        /\ m.source = s

HasInflightVoteRes(s, type) ==
    \E m \in net_messages :
        /\ m.type = type
        /\ m.dest = s

InflightOrProcessed(source, dest, type) ==
    \/ \E m \in net_messages :
        /\ m.type = type
        /\ m.source = source
        /\ m.dest = dest
    \/ \E m \in net_messages_processed :
        /\ m.type = type
        /\ m.source = source
        /\ m.dest = dest
        
RequestOrResLost(req, type) ==
    /\ req \notin net_messages
    /\ ~\E res \in net_messages :
        /\ res.type = type
        /\ res.correlation = req        

=============================================================================    