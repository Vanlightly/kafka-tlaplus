# Kafka data replication with the KRaft controller

## The protocol

TODO, create a description of the protocol in prose.

## The versions

### kafka_replication_v3_5

A detailed specification of the KRaft controller and data replication as of v3.5.0.
This version has one divergence from 3.5.0 in that leader epochs are only bumped on leader changes.

### kafka_replication_v3_5_simple

A simplified specification with a smaller state space. Sacrifices some detail for better modeling checking (smaller state space).

## Guide to reading the spec

Guide to reading the spec:

1. There exists (\E)
The broker ids are numeric. When you see something like: 
"\E b \in Brokers : ...",
the spec is saying "there exists a broker id in the set 
of brokers such that some condition is true.
 
2. State changes
In TLA+, the ' character (called prime) denotes a change to a variable in the
next global state of the universe. In TLA+, we move through time
as a sequence of global states.

For example: my_var' = my_var + 1

Each action that occurs must assign a value to ALL variables. Those
variables which do not change can be set by using the UNCHANGED keyword.

3. AND, OR, IF, CASE, NOT

- "and" is written as /\
- "or" is written as \/
- "if" is written as IF cond THEN ... ELSE ...
- "case" is written as CASE cond1 -> ...
                         [] cond2 -> ...
                         [] OTHER -> ...
- "not" is written as ~ or (...) = FALSE

Example: either X is true or (Y is true and X is false)
    \/ X
    \/ /\ ~X
       /\ Y
       
4. Data structures and updating them

Maps (known as functions in TLA+) require a special mention
here due to the somewhat strange way of updating map values. 
In TLA+, an action must set ALL variables. This means that when
a change to a map value of any given key is made, we must also
set the values of all other keys. To achieve this, the TLA+ syntax
says something like "the map stays the same in the next state
as it is in the current EXCEPT that the value of key K is now set
to V".

Example: my_map' = [my_map EXCEPT ![key] = value]

You will see this a lot in the spec as all broker related state is stored
in maps, where the broker id is the key.