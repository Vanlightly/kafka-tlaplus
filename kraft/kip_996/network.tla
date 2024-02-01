--------------------------- MODULE network ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC

CONSTANT MaxDisconnectedPairs,
         MaxConnectivityChanges \* Limits the number of times connectivity between server
                                \* pairs can change.

VARIABLES net_messages,
          net_messages_discard,
          net_connectivity,
          net_connectivity_ctr    \* the number of times connectivity changes

NetworkView == << net_messages, net_connectivity>>
NetworkVars == << net_messages,
                  net_messages_discard,
                  net_connectivity,
                  net_connectivity_ctr >>

Messages == net_messages
ProcessedMessages == net_messages_discard

ServerPairs(servers) == 
    { s \in SUBSET servers : Cardinality(s) = 2 }

NetworkInit(servers) == 
    /\ net_messages = {}
    /\ net_messages_discard = {}
    /\ net_connectivity = [pairs \in ServerPairs(servers) |-> TRUE]
    /\ net_connectivity_ctr = 0

----

Drop(msgs) ==
    /\ net_messages' = net_messages \ msgs
    /\ net_messages_discard' = net_messages_discard \union msgs

\* Network state transitions

\* Any dead servers are included in network disconnection
\* to avoid the combination of server death and networking
\* issues from causing a cluster to become unavailable.

ChangeConnectivity(dead_servers) ==
    /\ net_connectivity_ctr < MaxConnectivityChanges
    /\ \E disconnected \in SUBSET DOMAIN net_connectivity :
       /\ \A dead \in dead_servers :
            \E pair \in disconnected : dead \in pair
       \* cannot have more disconnected pairs than the max
       /\ Cardinality(disconnected) <= MaxDisconnectedPairs
       \* make sure the new disconnected set is different to the current
       /\ disconnected /= { pair \in DOMAIN net_connectivity : 
                                net_connectivity[pair] = FALSE } 
       /\ net_connectivity' = [pair \in DOMAIN net_connectivity |->
                                    IF pair \in disconnected
                                    THEN FALSE
                                    ELSE TRUE]
       /\ Drop({m \in net_messages : 
                    \E pair \in disconnected :
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
    Quantify(servers, LAMBDA s : 
                        \E pair \in DOMAIN net_connectivity :
                            /\ target \in pair
                            /\ s \in pair) + 1

ConnectedMajority(target, servers) ==
    ConnectedServers(target, servers) > Cardinality(servers) \div 2

DisconnectDeadServer(dead_server) ==
    /\ net_connectivity' = [pair \in DOMAIN net_connectivity |->
                                IF dead_server \in pair
                                THEN FALSE
                                ELSE net_connectivity[pair]]
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
    /\ UNCHANGED << net_messages_discard, net_connectivity, net_connectivity_ctr >>

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
    /\ UNCHANGED << net_messages_discard, net_connectivity, net_connectivity_ctr >>

\* Guarantees the message is sent once. Used to disable an action without
\* an explicit variable.
SendAllOnce(msgs) ==
    /\ ~\E m \in msgs :
        \/ m \in net_messages
        \/ m \in net_messages_discard
    /\ net_messages' = SendAllFunc(msgs, net_messages)
    /\ UNCHANGED << net_messages_discard, net_connectivity, net_connectivity_ctr >>    

DiscardAndSendAll(d, msgs) ==
    /\ net_messages' = SendAllFunc(msgs, DiscardFunc(d, net_messages))
    /\ net_messages_discard' = net_messages_discard \union {d}
    /\ UNCHANGED << net_connectivity, net_connectivity_ctr >>

\* Set the delivery count to 0 so the message cannot be processed again.
Discard(d) ==
    /\ net_messages' = DiscardFunc(d, net_messages)
    /\ net_messages_discard' = net_messages_discard \union {d}
    /\ UNCHANGED << net_connectivity, net_connectivity_ctr >>
    
\* Discard incoming message and reply with another    
Reply(d, m) ==
    /\ Connected(m.dest, m.source)
    /\ d \in net_messages
    /\ net_messages' = SendFunc(m, DiscardFunc(d, net_messages), 1)
    /\ net_messages_discard' = net_messages_discard \union {d}
    /\ UNCHANGED << net_connectivity, net_connectivity_ctr >>

PreviouslySent(m) ==
    \/ m \in net_messages
    \/ m \in net_messages_discard    

HasInflightVoteReq(s, type, pre_vote) ==
    \E m \in net_messages :
        /\ m.type = type
        /\ m.pre_vote = pre_vote
        /\ m.source = s

HasInflightVoteRes(s, type, pre_vote) ==
    \E m \in net_messages :
        /\ m.type = type
        /\ m.pre_vote = pre_vote
        /\ m.dest = s
    

=============================================================================    