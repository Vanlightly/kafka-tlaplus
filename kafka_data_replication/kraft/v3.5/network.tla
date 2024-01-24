--------------------------- MODULE network ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC

VARIABLES messages,
          messages_discard

NetworkView == << messages >>
NetworkVars == << messages, messages_discard >>

Messages == messages
ProcessedMessages == messages_discard

NetworkInit == 
    /\ messages = {}
    /\ messages_discard = {}

\* ======================================================================
\* ----- Message passing ------------------------------------------------

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
    /\ messages' = SendFunc(m, messages, 1)
    /\ UNCHANGED messages_discard

RECURSIVE SendAllFunc(_,_)
SendAllFunc(send_msgs, msgs) ==
    IF send_msgs = {}
    THEN msgs
    ELSE LET m == CHOOSE m \in send_msgs : TRUE
             new_msgs == SendFunc(m, msgs, 1)
             remaining == send_msgs \ {m}
         IN SendAllFunc(remaining, new_msgs)

SendAll(msgs) ==
    /\ messages' = SendAllFunc(msgs, messages)
    /\ UNCHANGED messages_discard

DiscardAndSendAll(d, msgs) ==
    /\ messages' = SendAllFunc(msgs, DiscardFunc(d, messages))
    /\ messages_discard' = messages_discard \union {d}

\* Set the delivery count to 0 so the message cannot be processed again.
Discard(d) ==
    /\ messages' = DiscardFunc(d, messages)
    /\ messages_discard' = messages_discard \union {d}
    
Drop(msgs) ==
    /\ messages' = messages \ msgs
    /\ messages_discard' = messages_discard \union msgs    

\* Discard incoming message and reply with another    
Reply(d, m) ==
    /\ d \in messages
    /\ messages' = SendFunc(m, DiscardFunc(d, messages), 1)
    /\ messages_discard' = messages_discard \union {d}
    
PreviouslySent(m) ==
    \/ m \in messages
    \/ m \in messages_discard    
    
=============================================================================    