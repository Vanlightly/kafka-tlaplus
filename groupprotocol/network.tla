--------------------------- MODULE network ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC

CONSTANTS HeartbeatRequestMsg,
          HeartbeatResponseMsg

VARIABLES messages,
          messages_last_discard

NetworkView == << messages >>
NetworkVars == << messages, messages_last_discard >>

Messages == messages

NetworkInit == 
    /\ messages = {}
    /\ messages_last_discard = {}

NetworkInactive ==
    UNCHANGED NetworkVars

\* Send the message whether it already exists or not.
\* If it does exist, the delivery count will go above 1 and
\* the message can be delivered multiple times.
SendFunc(m, msgs, deliver_count) ==
    msgs \union {m}

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
DiscardFunc(m, msgs) ==
    msgs \ {m}

\* Send a message, without restriction
Send(m) ==
    /\ messages' = SendFunc(m, messages, 1)
    /\ messages_last_discard' = {}

\* Set the delivery count to 0 so the message cannot be processed again.
Discard(d) ==
    /\ messages' = DiscardFunc(d, messages)
    /\ messages_last_discard' = {d}

\* Discard incoming message and reply with another    
SendReply(d, m) ==
    /\ d \in messages
    /\ messages' = SendFunc(m, DiscardFunc(d, messages), 1)
    /\ messages_last_discard' = {d}
    
\* TRUE iff the message is of the desired type and has not
\* been delivered yet.
ReceivableMsg(m, type) ==
    m.type = type

    
=============================================================================    