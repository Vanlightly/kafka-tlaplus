--------------------------- MODULE message_passing ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC

VARIABLES messages

\* ======================================================================
\* ----- Message passing ------------------------------------------------

\* Send the message whether it already exists or not.
\* If it does exist, the delivery count will go above 1 and
\* the message can be delivered multiple times.
SendFunc(m, msgs, deliver_count) ==
    IF m \in DOMAIN msgs
    THEN [msgs EXCEPT ![m] = @ + 1]
    ELSE msgs @@ (m :> deliver_count)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
DiscardFunc(m, msgs) ==
    [msgs EXCEPT ![m] = @ - 1]

\* Send a message, without restriction
Send(m) ==
    messages' = SendFunc(m, messages, 1)

RECURSIVE SendAllFunc(_,_)
SendAllFunc(send_msgs, msgs) ==
    IF send_msgs = {}
    THEN msgs
    ELSE LET m == CHOOSE m \in send_msgs : TRUE
             new_msgs == SendFunc(m, msgs, 1)
             remaining == send_msgs \ {m}
         IN SendAllFunc(remaining, new_msgs)

SendAll(msgs) ==
    messages' = SendAllFunc(msgs, messages)

DiscardAndSendAll(d, msgs) ==
    messages' = SendAllFunc(msgs, DiscardFunc(d, messages))

\* Set the delivery count to 0 so the message cannot be processed again.
Discard(d) ==
    messages' = DiscardFunc(d, messages)

\* Discard incoming message and reply with another    
Reply(d, m) ==
    /\ d \in DOMAIN messages
    /\ messages[d] > 0 \* message must exist
    /\ messages' = SendFunc(m, DiscardFunc(d, messages), 1)

\* TRUE iff the message is of the desired type and has not
\* been delivered yet.
ReceivableMsg(m, type) ==
    /\ m.type = type
    /\ messages[m] > 0  \* the message hasn't been delivered yet
    
=============================================================================    