---------- MODULE Handshaking ----------

EXTENDS FiniteSets, Naturals

CONSTANTS
    NODES,      \* set of nodes in the network
    GOOD_NODES, \* set of nodes which follow the protocol, bad nodes can act arbitrarily
    MIN,        \* minimum number of connections
    MAX         \* maximum number of connections

VARIABLES
    blacklist,         \* tuple of each node's blacklisted peers
    connections,       \* tuple of each node's accepted connections
    handshaking,       \* tuple of each node's in-progress handshake
    messages,          \* tuple of each node's incoming messages
    received_conn_msg, \* tuple of each node's peers who have sent a conn_msg
    timeout_count      \* tuple of each node's timeout count

vars == <<blacklist, connections, handshaking, messages, received_conn_msg, timeout_count>>

ASSUME NODES \subseteq Nat
ASSUME GOOD_NODES \subseteq NODES
ASSUME MIN \in Nat /\ MIN > 0
ASSUME MAX \in Nat /\ MIN <= MAX /\ MAX < Cardinality(NODES)
ASSUME Cardinality(NODES \ GOOD_NODES) < Cardinality(GOOD_NODES)
\* For combinatorial reasons, we must also have:
ASSUME Cardinality(GOOD_NODES) > MIN
ASSUME
    LET N == Cardinality(NODES) IN
    IF N = 3 THEN MAX /= 1 ELSE MAX /= 2 /\ MAX /= N - 2

----

(***********)
(* Helpers *)
(***********)

conn_msg(from) == [ type |-> "conn_msg", from |-> from ]

ack_msg(from) == [ type |-> "ack", from |-> from ]

nack_msg(from) == [ type |-> "nack", from |-> from ]

Bad_nodes == NODES \ GOOD_NODES

Bad(n) == n \in Bad_nodes

Bad_messages == [ type : {"conn_msg", "ack", "nack", "bad"}, from : Bad_nodes ]

Messages == [ type : {"conn_msg", "ack", "nack"}, from : NODES ] \cup Bad_messages

(***********)
(* Actions *)
(***********)

\* Good node actions

\* connection messages
send_conn_msg(m, n) ==
    /\ messages' = [ messages EXCEPT ![n] = IF Bad(n) THEN @ ELSE @ \cup {conn_msg(m)} ]
    /\ handshaking' = [ handshaking EXCEPT ![m] = @ \cup {n} ]
    /\ UNCHANGED <<blacklist, connections, received_conn_msg, timeout_count>>

SendConnectionMessage == \E g \in GOOD_NODES, n \in NODES :
    /\ g /= n
    /\ Cardinality(connections[g]) < MAX
    /\ n \notin blacklist[g]
    /\ n \notin connections[g]
    /\ n \notin handshaking[g]
    /\ n \notin received_conn_msg[g]
    \* [g] currently has a nack from [n]
    /\ n \notin { m.from : m \in { mm \in messages[g] : mm.type = "nack" } }
    /\ send_conn_msg(g, n)

handle_conn_msg(m, n, msg) ==
    /\ CASE n \notin handshaking[m] \cup received_conn_msg[m] \cup connections[m] ->
                    /\ handshaking' = [ handshaking EXCEPT ![m] = @ \cup {n} ]
                    /\ messages' = [ messages EXCEPT ![m] = @ \ {msg},
                                                     ![n] = IF Bad(n) THEN @ ELSE @ \cup {conn_msg(m)} ]
                    /\ received_conn_msg' = [ received_conn_msg EXCEPT ![m] = @ \cup {n} ]
             [] n \in handshaking[m] /\ n \notin received_conn_msg[m] \cup connections[m] ->
                    /\ messages' = [ messages EXCEPT ![m] = @ \ {msg},
                                                     ![n] = IF Bad(n) THEN @ ELSE @ \cup {ack_msg(m)} ]
                    /\ received_conn_msg' = [ received_conn_msg EXCEPT ![m] = @ \cup {n} ]
                    /\ UNCHANGED handshaking
             [] OTHER ->
                    /\ messages' = [ messages EXCEPT ![n] = @ \ {msg} ]
                    /\ UNCHANGED <<handshaking, received_conn_msg>>
    /\ UNCHANGED <<blacklist, connections, timeout_count>>

HandleConnectionMessage == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "conn_msg" } :
        LET n == msg.from IN
        /\ n \notin blacklist[g]
        /\ handle_conn_msg(g, n, msg)

\* acks
ack(m, n, msg) ==
    LET type == msg.type IN
    IF n \in received_conn_msg[m]
    THEN IF type = "ack"
         THEN /\ connections' = [ connections EXCEPT ![m] = @ \cup {n} ]
              /\ handshaking' = [ handshaking EXCEPT ![m] = @ \ {n} ]
              /\ messages' = [ messages EXCEPT ![m] = @ \ {msg},
                                               ![n] = IF Bad(n) THEN @ ELSE @ \cup {ack_msg(m)} ]
              /\ received_conn_msg' = [ received_conn_msg EXCEPT ![m] = @ \ {n} ]
              /\ UNCHANGED <<blacklist, timeout_count>>
         ELSE /\ messages' = [ messages EXCEPT ![m] = @ \ {msg} ]
              /\ UNCHANGED <<blacklist, connections, handshaking, received_conn_msg, timeout_count>>
    ELSE IF type = "conn_msg"
         THEN /\ messages' = [ messages EXCEPT ![m] = @ \ {msg},
                                               ![n] = IF Bad(n) THEN @ ELSE @ \cup {ack_msg(m)} ]
              /\ received_conn_msg' = [ received_conn_msg EXCEPT ![m] = @ \cup {n} ]
              /\ UNCHANGED <<blacklist, connections, handshaking, timeout_count>>
         ELSE /\ messages' = [ messages EXCEPT ![m] = @ \cup {msg} ]
              /\ UNCHANGED <<blacklist, connections, handshaking, received_conn_msg, timeout_count>>

Ack == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "conn_msg" \/ m.type = "ack" } :
        LET n == msg.from IN
        /\ Cardinality(connections[g] \ {n}) < MAX
        /\ n \in handshaking[g]
        /\ ack(g, n, msg)

handle_ack(m, n, msg) ==
    /\ connections' = [ connections EXCEPT ![m] = @ \cup {n} ]
    /\ handshaking' = [ handshaking EXCEPT ![m] = @ \ {n} ]
    /\ messages' = [ messages EXCEPT ![m] = @ \ {msg} ]
    /\ received_conn_msg' = [ received_conn_msg EXCEPT ![m] = @ \ {n} ]
    /\ UNCHANGED <<blacklist, timeout_count>>

HandleAck == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "ack" } :
        LET n == msg.from IN
        /\ n \in connections[g]
        /\ handle_ack(g, n, msg)

\* nacks
nack(m, n, msg) ==
    /\ connections' = [ connections EXCEPT ![m] = @ \ {n} ]
    /\ handshaking' = [ handshaking EXCEPT ![m] = @ \ {n} ]
    /\ messages' = [ messages EXCEPT ![m] = @ \ {msg},
                                     ![n] = IF Bad(n) THEN @ ELSE @ \cup {nack_msg(m)} ]
    /\ received_conn_msg' = [ received_conn_msg EXCEPT ![m] = @ \ {n} ]
    /\ UNCHANGED <<blacklist, timeout_count>>

Nack == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "conn_msg" \/ m.type = "ack" } :
        LET n == msg.from IN
        /\ Cardinality(connections[g]) >= MIN
        /\ n \notin connections[g]
        /\ nack(g, n, msg)

HandleNack == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "nack" } :
        LET n == msg.from IN
        /\ connections' = [ connections EXCEPT ![g] = @ \ {n} ]
        /\ handshaking' = [ handshaking EXCEPT ![g] = @ \ {n} ]
        /\ messages' = [ messages EXCEPT ![g] = @ \ {msg} ]
        /\ received_conn_msg' = [ received_conn_msg EXCEPT ![g] = @ \ {n} ]
        /\ UNCHANGED <<blacklist, timeout_count>>

HandleBad == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "bad" } :
        LET n == msg.from IN
        /\ blacklist' = [ blacklist EXCEPT ![g] = @ \cup {n} ]
        /\ connections' = [ connections EXCEPT ![g] = @ \ {n} ]
        /\ handshaking' = [ handshaking EXCEPT ![g] = @ \ {n} ]
        /\ messages' = [ messages EXCEPT ![g] = @ \ {msg} ]
        /\ received_conn_msg' = [ received_conn_msg EXCEPT ![g] = @ \ {n} ]
        /\ UNCHANGED timeout_count

\* Undesirable actions

\* bad node action
BadNodeSendsGoodNodeArbitraryMessage == \E n \in GOOD_NODES :
    \E msg \in Bad_messages :
        /\ messages' = [ messages EXCEPT ![n] = @ \cup {msg} ]
        /\ UNCHANGED <<blacklist, connections, handshaking, received_conn_msg, timeout_count>>

Timeout(n) == \E m \in handshaking[n] :
    /\ m \notin connections[n]
    /\ handshaking' = [ handshaking EXCEPT ![n] = @ \ {m} ]
    /\ received_conn_msg' = [ received_conn_msg EXCEPT ![n] = @ \ {m} ]
    /\ messages' = [ messages EXCEPT ![n] = { mm \in @ : mm /= conn_msg(m) /\ mm /= ack_msg(m) } ]
    /\ timeout_count' = [ timeout_count EXCEPT ![n] = @ + 1 ]
    /\ UNCHANGED <<blacklist, connections>>

(*****************)
(* Specification *)
(*****************)

\* initially there are no connections
Init ==
    /\ blacklist = [ n \in NODES |-> {} ]
    /\ connections = [ n \in NODES |-> {} ]
    /\ handshaking = [ n \in NODES |-> {} ]
    /\ messages = [ n \in NODES |-> {} ]
    /\ received_conn_msg = [ n \in NODES |-> {} ]
    /\ timeout_count = [ n \in NODES |-> 0 ]

Next ==
    \/ SendConnectionMessage
    \/ HandleConnectionMessage
    \/ Ack
    \/ HandleAck
    \/ Nack
    \/ HandleNack
    \/ HandleBad
    \/ BadNodeSendsGoodNodeArbitraryMessage
    \/ \E n \in NODES : Timeout(n)

Fairness ==
    /\ WF_vars(SendConnectionMessage)
    /\ WF_vars(HandleConnectionMessage)
    /\ WF_vars(Ack)
    /\ WF_vars(HandleAck)
    /\ WF_vars(HandleBad)
    /\ WF_vars(HandleNack)

Timeout_bound == \A n \in NODES : timeout_count[n] < 3

Spec == Init /\ [][Next /\ Timeout_bound]_vars /\ Fairness

(***************************)
(* Invariants & Properties *)
(***************************)

TypeOK ==
    /\ \A n \in NODES : blacklist[n] \subseteq NODES
    /\ \A n \in NODES : connections[n] \subseteq NODES
    /\ \A n \in NODES : handshaking[n] \subseteq NODES
    /\ \A n \in NODES : messages[n] \subseteq Messages
    /\ \A n \in NODES : received_conn_msg[n] \subseteq NODES

Safety ==
    \* no self blacklisting, connections, handshaking, messages, or received_conn_msgs
    /\ \A n \in NODES :
        /\ n \notin blacklist[n]
        /\ n \notin connections[n]
        /\ n \notin handshaking[n]
        /\ n \notin { msg.from : msg \in messages[n] }
        /\ n \notin received_conn_msg[n]
    \* good nodes never exceed MAX connections
    /\ \A n \in GOOD_NODES : Cardinality(connections[n]) <= MAX
    \* good nodes are never both handshaking and connected to another node
    /\ \A n \in GOOD_NODES : connections[n] \cap handshaking[n] = {}
    \* if a good node has received a conn_msg from another node, they must be handshaking
    /\ \A n \in GOOD_NODES : received_conn_msg[n] \subseteq handshaking[n]
    \* good nodes do not blacklist other good nodes
    /\ \A n \in GOOD_NODES : blacklist[n] \subseteq Bad_nodes

Liveness ==
    \* good nodes always respond to requests with an ack or nack
    /\ \A m, n \in GOOD_NODES : conn_msg(m) \in messages[n] =>
        LET msg == conn_msg(m) IN
        []<><<ack(n, m, msg) \/ nack(n, m, msg)>>_vars
    \* eventually it's always the case that all good nodes will have >= MIN connections
    /\ <>[](\A n \in GOOD_NODES : Cardinality(connections[n]) >= MIN)
    \* if good nodes are ever partially connected,
    \* then eventually that partial connection will become bidirectional and stay that way or it will be closed
    /\ \A m, n \in GOOD_NODES :
        \/ m \in connections[n]
        \/ n \in connections[m] ~> [](\/ m \in connections[n] /\ n \in connections[m]
                                      \/ m \notin connections[n] /\ n \notin connections[m])

========================================
