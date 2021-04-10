---------- MODULE Handshaking ----------

EXTENDS FiniteSets, Naturals

CONSTANTS
    NODES,        \* set of nodes in the network
    GOOD_NODES,   \* set of nodes which follow the protocol, bad nodes can act arbitrarily
    MIN,          \* minimum number of connections
    MAX,          \* maximum number of connections
    CONN_ATTEMPT, \* maximum number of connection attempts with any given node
    TIMEOUT       \* maximum number of timeouts with any given node

VARIABLES
    blacklist,         \* tuple of each node's blacklisted peers
    connections,       \* tuple of each node's accepted connections
    conn_attempts,     \* tuple of each node's connection attempt count
    handshaking,       \* tuple of each node's in-progress handshake
    messages,          \* tuple of each node's incoming messages
    received_conn_msg, \* tuple of each node's peers who have sent a conn_msg
    timeout_count      \* tuple of each node's timeout count

vars == <<blacklist, connections, conn_attempts, handshaking, messages, received_conn_msg, timeout_count>>

ASSUME NODES \subseteq Nat
ASSUME GOOD_NODES \subseteq NODES
ASSUME MIN \in Nat /\ MIN > 0
ASSUME MAX \in Nat /\ MIN <= MAX /\ MAX < Cardinality(NODES)
ASSUME CONN_ATTEMPT \in Nat
ASSUME TIMEOUT \in Nat
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

Timeout_bound == \A g \in GOOD_NODES : \A n \in NODES \ {g} : timeout_count[g][n] <= TIMEOUT

(***********)
(* Actions *)
(***********)

\* Good node actions

\* connection messages
send_conn_msg(m, n) ==
    /\ conn_attempts' = [ conn_attempts EXCEPT ![m][n] = @ + 1 ]
    /\ messages' = [ messages EXCEPT ![n] = IF Bad(n) THEN @ ELSE @ \cup {conn_msg(m)} ]
    /\ handshaking' = [ handshaking EXCEPT ![m] = @ \cup {n} ]
    /\ UNCHANGED <<blacklist, connections, received_conn_msg, timeout_count>>

SendConnectionMessage == \E g \in GOOD_NODES, n \in NODES :
    /\ g /= n
    /\ Cardinality(connections[g]) < MAX
    /\ conn_attempts[g][n] < CONN_ATTEMPT
    /\ n \notin blacklist[g]
    /\ n \notin connections[g]
    /\ n \notin handshaking[g]
    /\ n \notin received_conn_msg[g]
    \* [g] does not currently have a nack from [n]
    /\ n \notin { m.from : m \in { mm \in messages[g] : mm.type = "nack" } }
    /\ send_conn_msg(g, n)
    /\ Timeout_bound

handle_conn_msg(m, n, msg) ==
    /\ CASE n \notin handshaking[m] \cup received_conn_msg[m] \cup connections[m] ->
                /\ conn_attempts[m][n] < CONN_ATTEMPT
                /\ conn_attempts' = [ conn_attempts EXCEPT ![m][n] = @ + 1 ]
                /\ handshaking' = [ handshaking EXCEPT ![m] = @ \cup {n} ]
                /\ messages' = [ messages EXCEPT ![m] = @ \ {msg},
                                                    ![n] = IF Bad(n) THEN @ ELSE @ \cup {conn_msg(m)} ]
                /\ received_conn_msg' = [ received_conn_msg EXCEPT ![m] = @ \cup {n} ]
                /\ UNCHANGED blacklist
         [] n \in handshaking[m] /\ n \notin received_conn_msg[m] \cup connections[m] ->
                /\ messages' = [ messages EXCEPT ![m] = @ \ {msg},
                                                    ![n] = IF Bad(n) THEN @ ELSE @ \cup {ack_msg(m)} ]
                /\ received_conn_msg' = [ received_conn_msg EXCEPT ![m] = @ \cup {n} ]
                /\ UNCHANGED <<blacklist, conn_attempts, handshaking>>
         [] OTHER ->
                /\ blacklist' = [ blacklist EXCEPT ![m] = @ \cup {n} ]
                /\ messages' = [ messages EXCEPT ![m] = @ \ {msg} ]
                /\ UNCHANGED <<conn_attempts, handshaking, received_conn_msg>>
    /\ UNCHANGED <<connections, timeout_count>>

HandleConnectionMessage == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "conn_msg" } :
        LET n == msg.from IN
        /\ n \notin blacklist[g]
        /\ handle_conn_msg(g, n, msg)
        /\ Timeout_bound

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
              /\ UNCHANGED <<blacklist, conn_attempts, timeout_count>>
         ELSE /\ messages' = [ messages EXCEPT ![m] = @ \ {msg} ]
              /\ UNCHANGED <<blacklist, connections, conn_attempts, handshaking, received_conn_msg, timeout_count>>
    ELSE IF type = "conn_msg"
         THEN /\ messages' = [ messages EXCEPT ![m] = @ \ {msg},
                                               ![n] = IF Bad(n) THEN @ ELSE @ \cup {ack_msg(m)} ]
              /\ received_conn_msg' = [ received_conn_msg EXCEPT ![m] = @ \cup {n} ]
              /\ UNCHANGED <<blacklist, connections, conn_attempts, handshaking, timeout_count>>
         ELSE /\ messages' = [ messages EXCEPT ![m] = @ \cup {msg} ]
              /\ UNCHANGED <<blacklist, connections, conn_attempts, handshaking, received_conn_msg, timeout_count>>

Ack == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "conn_msg" \/ m.type = "ack" } :
        LET n == msg.from IN
        /\ Cardinality(connections[g] \ {n}) < MAX
        /\ n \in handshaking[g]
        /\ ack(g, n, msg)
        /\ Timeout_bound

handle_ack(m, n, msg) ==
    /\ connections' = [ connections EXCEPT ![m] = @ \cup {n} ]
    /\ handshaking' = [ handshaking EXCEPT ![m] = @ \ {n} ]
    /\ messages' = [ messages EXCEPT ![m] = @ \ {msg} ]
    /\ received_conn_msg' = [ received_conn_msg EXCEPT ![m] = @ \ {n} ]
    /\ UNCHANGED <<blacklist, conn_attempts, timeout_count>>

HandleAck == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "ack" } :
        LET n == msg.from IN
        /\ n \in connections[g]
        /\ handle_ack(g, n, msg)
        /\ Timeout_bound

\* nacks
nack(m, n, msg) ==
    /\ connections' = [ connections EXCEPT ![m] = @ \ {n} ]
    /\ handshaking' = [ handshaking EXCEPT ![m] = @ \ {n} ]
    /\ messages' = [ messages EXCEPT ![m] = @ \ {msg},
                                     ![n] = IF Bad(n) THEN @ ELSE @ \cup {nack_msg(m)} ]
    /\ received_conn_msg' = [ received_conn_msg EXCEPT ![m] = @ \ {n} ]
    /\ UNCHANGED <<blacklist, conn_attempts, timeout_count>>

Nack == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "conn_msg" \/ m.type = "ack" } :
        LET n == msg.from IN
        /\ Cardinality(connections[g]) >= MIN
        /\ n \notin connections[g]
        /\ n \in handshaking[g]
        /\ n \in received_conn_msg[g]
        /\ nack(g, n, msg)
        /\ Timeout_bound

handle_nack(m, n, msg) ==
    /\ connections' = [ connections EXCEPT ![m] = @ \ {n} ]
    /\ handshaking' = [ handshaking EXCEPT ![m] = @ \ {n} ]
    /\ messages' = [ messages EXCEPT ![m] = @ \ {msg} ]
    /\ received_conn_msg' = [ received_conn_msg EXCEPT ![m] = @ \ {n} ]
    /\ UNCHANGED <<blacklist, conn_attempts, timeout_count>>

HandleNack == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "nack" } :
        LET n == msg.from IN
        /\ n \notin connections[g]
        /\ n \in handshaking[g]
        /\ n \in received_conn_msg[g]
        /\ handle_nack(g, n, msg)
        /\ Timeout_bound

handle_bad(m, n, msg) ==
    /\ blacklist' = [ blacklist EXCEPT ![m] = @ \cup {n} ]
    /\ connections' = [ connections EXCEPT ![m] = @ \ {n} ]
    /\ handshaking' = [ handshaking EXCEPT ![m] = @ \ {n} ]
    /\ messages' = [ messages EXCEPT ![m] = @ \ {msg} ]
    /\ received_conn_msg' = [ received_conn_msg EXCEPT ![m] = @ \ {n} ]
    /\ UNCHANGED <<conn_attempts, timeout_count>>

HandleBad == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "bad" } :
        LET n == msg.from IN
        /\ handle_bad(g, n, msg)
        /\ Timeout_bound

HandleBadAckNack == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "ack" \/ m.type = "nack" } :
        LET n == msg.from IN
        /\ n \notin handshaking[g]
        /\ n \notin received_conn_msg[g]
        /\ handle_bad(g, n, msg)
        /\ Timeout_bound

\* Undesirable actions

\* bad node action
BadNodeSendsGoodNodeMessage == \E n \in GOOD_NODES :
    \E msg \in Bad_messages :
        /\ msg.from \notin blacklist[n]
        /\ messages' = [ messages EXCEPT ![n] = @ \cup {msg} ]
        /\ UNCHANGED <<blacklist, connections, conn_attempts, handshaking, received_conn_msg, timeout_count>>
        /\ Timeout_bound

timeout(n, m) ==
    /\ connections' = [ connections EXCEPT ![n] = @ \ {m} ]
    /\ handshaking' = [ handshaking EXCEPT ![n] = @ \ {m} ]
    /\ received_conn_msg' = [ received_conn_msg EXCEPT ![n] = @ \ {m} ]
    /\ messages' = [ messages EXCEPT ![n] = { mm \in @ : mm /= conn_msg(m) /\ mm /= ack_msg(m) } ]
    /\ timeout_count' = [ timeout_count EXCEPT ![n][m] = @ + 1 ]
    /\ UNCHANGED <<blacklist, conn_attempts>>

Timeout_handshaking(n) == \E m \in handshaking[n] :
    /\ timeout_count[n][m] < TIMEOUT
    /\ timeout(n, m)

Timeout_connection(n) == \E m \in connections[n] :
    /\ n \notin connections[m]
    /\ timeout_count[n][m] < TIMEOUT
    /\ timeout(n, m)

(*****************)
(* Specification *)
(*****************)

Init ==
    /\ blacklist = [ n \in NODES |-> {} ]
    /\ connections = [ n \in NODES |-> {} ]
    /\ handshaking = [ n \in NODES |-> {} ]
    /\ messages = [ n \in NODES |-> {} ]
    /\ received_conn_msg = [ n \in NODES |-> {} ]
    /\ conn_attempts = [ m \in NODES |-> [ n \in NODES \ {m} |-> 0 ] ]
    /\ timeout_count = [ m \in NODES |-> [ n \in NODES \ {m} |-> 0 ] ]

Next ==
    \/ SendConnectionMessage
    \/ HandleConnectionMessage
    \/ Ack
    \/ HandleAck
    \/ Nack
    \/ HandleNack
    \/ HandleBad
    \/ HandleBadAckNack
    \/ BadNodeSendsGoodNodeMessage
    \/ \E n \in GOOD_NODES : Timeout_handshaking(n)
    \/ \E n \in GOOD_NODES : Timeout_connection(n)

Fairness ==
    /\ WF_vars(SendConnectionMessage)
    /\ WF_vars(HandleConnectionMessage)
    /\ WF_vars(Ack)
    /\ WF_vars(HandleAck)
    /\ WF_vars(HandleBad)
    /\ WF_vars(HandleBadAckNack)
    /\ WF_vars(HandleNack)
    /\ WF_vars(\E n \in GOOD_NODES : Timeout_connection(n))

Spec == Init /\ [][Next]_vars /\ Fairness

(*********************)
(* Invariants/Safety *)
(*********************)

TypeOK ==
    /\ \A n \in GOOD_NODES : blacklist[n] \subseteq NODES
    /\ \A n \in GOOD_NODES : connections[n] \subseteq NODES
    /\ \A n \in GOOD_NODES : handshaking[n] \subseteq NODES
    /\ \A n \in GOOD_NODES : messages[n] \subseteq Messages
    /\ \A n \in GOOD_NODES : received_conn_msg[n] \subseteq NODES
    /\ \A m \in GOOD_NODES : \A n \in NODES \ {m} : conn_attempts[m][n] \in Nat
    /\ \A m \in GOOD_NODES : \A n \in NODES \ {m} : timeout_count[m][n] \in Nat

NoSelfInteractions == \A n \in GOOD_NODES :
    /\ n \notin blacklist[n]
    /\ n \notin connections[n]
    /\ n \notin handshaking[n]
    /\ n \notin { msg.from : msg \in messages[n] }
    /\ n \notin received_conn_msg[n]

GoodNodesDoNotExceedMaxConnections ==
    \A n \in GOOD_NODES : Cardinality(connections[n]) <= MAX

GoodNodesDoNotHandshakeTheirConnections ==
    \A n \in GOOD_NODES : connections[n] \cap handshaking[n] = {}

GoodNodesOnlyReceiveConnectionMessagesWhenHandshaking ==
    \A n \in GOOD_NODES : received_conn_msg[n] \subseteq handshaking[n]

GoodNodesDoNotExceedMaxConnectionAttempts ==
    \A g \in GOOD_NODES : \A n \in NODES \ {g} : conn_attempts[g][n] \in 0..CONN_ATTEMPT

GoodNodesDoNotExceedMaxTimeouts ==
    \A g \in GOOD_NODES : \A n \in NODES \ {g} : timeout_count[g][n] \in 0..TIMEOUT

(***********************)
(* Properties/Liveness *)
(***********************)

GoodNodesAlwaysRespondToConnectionMessagesWithAckOrNack ==
    \A m, n \in GOOD_NODES : conn_msg(m) \in messages[n] =>
        LET msg == conn_msg(m) IN
        []<><<ack(n, m, msg) \/ nack(n, m, msg)>>_vars

IfPossibleGoodNodesWillEventuallyExceedMinConnections ==
    <>[](\A g \in GOOD_NODES :
        LET exhausted ==
            { n \in NODES \ {g} :
                \/ conn_attempts[g][n] = CONN_ATTEMPT
                \/ conn_attempts[n][g] = CONN_ATTEMPT
                \/ timeout_count[g][n] = TIMEOUT
                \/ timeout_count[n][g] = TIMEOUT }
        IN
        Cardinality(NODES \ (exhausted \cup blacklist[g] \cup {g})) >= MIN => Cardinality(connections[g]) >= MIN)

ConnectionsBetweenGoodNodesAreEventuallyBidirectionalOrClosed ==
    \A m, n \in GOOD_NODES :
        \/ m \in connections[n]
        \/ n \in connections[m] ~> [](\/ m \in connections[n] /\ n \in connections[m]
                                      \/ m \notin connections[n] /\ n \notin connections[m])

========================================
