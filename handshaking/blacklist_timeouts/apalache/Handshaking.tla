---------- MODULE Handshaking ----------

EXTENDS FiniteSets, Naturals

CONSTANTS
    \* @type: Set(Int);
    BAD_NODES,
    \* @type: Set(Int);
    GOOD_NODES,
    \* @type: Int;
    MIN,
    \* @type: Int;
    MAX

VARIABLES
    \* @type: Int -> Set(Int);
    blacklist,
    \* @type: Int -> Set(Int);
    connections,
    \* @type: Int -> Set([from: Int, type: Str]);
    messages,
    \* @type: Int -> Set(Int);
    recv_ack,
    \* @type: Int -> Set(Int);
    recv_conn,
    \* @type: Int -> Set(Int);
    recv_meta,
    \* @type: Int -> Set(Int);
    sent_ack,
    \* @type: Int -> Set(Int);
    sent_conn,
    \* @type: Int -> Set(Int);
    sent_meta,
    \* @type: Int -> Set(Int);
    in_progress

\* @type: <<Int -> Set(Int), Int -> Set(Int), Int -> Set([from: Int, type: Str]), Int -> Set(Int), Int -> Set(Int), Int -> Set(Int), Int -> Set(Int), Int -> Set(Int), Int -> Set(Int), Int -> Set(Int)>>;
vars == <<blacklist, connections, messages, recv_ack, recv_conn, recv_meta, sent_ack, sent_conn, sent_meta, in_progress>>

ASSUME BAD_NODES \cap GOOD_NODES = {}
ASSUME MIN \in Nat /\ MIN > 0
ASSUME MAX \in Nat /\ MIN <= MAX /\ MAX < Cardinality(BAD_NODES \cup GOOD_NODES)
\* For combinatorial reasons, we must also have:
ASSUME Cardinality(GOOD_NODES) > MIN
ASSUME
    LET N == Cardinality(BAD_NODES \cup GOOD_NODES) IN
    IF N = 3 THEN MAX /= 1 ELSE MAX /= 2 /\ MAX /= N - 2

----

(***********)
(* Helpers *)
(***********)

\* @type: (Int) => [from: Int, type: Str];
conn_msg(from) == [ type |-> "conn", from |-> from ]

\* @type: (Int) => [from: Int, type: Str];
meta_msg(from) == [ type |-> "meta", from |-> from ]

\* @type: (Int) => [from: Int, type: Str];
ack_msg(from) == [ type |-> "ack", from |-> from ]

\* @type: (Int) => [from: Int, type: Str];
nack_msg(from) == [ type |-> "nack", from |-> from ]

\* @type: Set(Int);
Nodes == BAD_NODES \cup GOOD_NODES

\* @type: (Int) => Bool;
Bad(n) == n \in BAD_NODES

\* @type: Set([from: Int, type: Str]);
Bad_messages == [ type : {"conn", "meta", "ack", "nack", "bad"}, from : BAD_NODES ]

\* @type: Set([from: Int, type: Str]);
Messages == [ type : {"conn", "meta", "ack", "nack"}, from : GOOD_NODES ] \cup Bad_messages

\* @type: (Int) => Int;
Num_connections(g) == Cardinality(connections[g])

\* @type: (Int) => Bool;
Can_start_connection_attempt(g) == Num_connections(g) + Cardinality(in_progress[g]) < MAX

\* @type: (Int, Int) => Bool;
Blacklisted(g, n) == n \in blacklist[g]

\* @type: (Int, Int) => Bool;
Connected(g, h) == g \in connections[h] /\ h \in connections[g]

(***********)
(* Actions *)
(***********)

\* Good node actions

\* @type: (Int, Int) => Bool;
exit_handshaking(g, n) ==
    /\ blacklist' = [ blacklist EXCEPT ![g] = @ \cup {n}]
    /\ connections' = [ connections EXCEPT ![g] = @ \ {n} ]
    /\ messages' = [ messages EXCEPT ![g] = { msg \in @ : msg.from /= n } ]
    /\ recv_conn' = [ recv_conn EXCEPT ![g] = @ \ {n} ]
    /\ sent_conn' = [ sent_conn EXCEPT ![g] = @ \ {n} ]
    /\ recv_meta' = [ recv_meta EXCEPT ![g] = @ \ {n} ]
    /\ sent_meta' = [ sent_meta EXCEPT ![g] = @ \ {n} ]
    /\ recv_ack' = [ recv_ack EXCEPT ![g] = @ \ {n} ]
    /\ sent_ack' = [ sent_ack EXCEPT ![g] = @ \ {n} ]
    /\ in_progress' = [ in_progress EXCEPT ![g] = @ \ {n} ]

\* connection messages

\* @type: (Int, Int) => Bool;
send_conn_msg(g, n) ==
    /\ messages' = [ messages EXCEPT ![n] = IF Bad(n) \/ Blacklisted(n, g) THEN @ ELSE @ \cup {conn_msg(g)} ]
    /\ sent_conn' = [ sent_conn EXCEPT ![g] = @ \cup {n} ]
    /\ in_progress' = [ in_progress EXCEPT ![g] = @ \cup {n} ]
    /\ UNCHANGED blacklist
    /\ UNCHANGED connections
    /\ UNCHANGED recv_ack
    /\ UNCHANGED recv_conn
    /\ UNCHANGED recv_meta
    /\ UNCHANGED sent_ack
    /\ UNCHANGED sent_meta

\* @type: Bool;
InitiateConnection == \E g \in GOOD_NODES, n \in Nodes :
    /\ g /= n
    /\ Can_start_connection_attempt(g)
    /\ n \notin blacklist[g]
    /\ n \notin connections[g]
    /\ n \notin recv_conn[g]
    /\ n \notin sent_conn[g]
    /\ n \notin recv_meta[g]
    /\ n \notin sent_meta[g]
    /\ n \notin recv_ack[g]
    /\ n \notin sent_ack[g]
    /\ n \notin in_progress[g]
    /\ n \notin { m.from : m \in messages[g] }
    /\ send_conn_msg(g, n)

\* @type: Bool;
RespondToConnectionMessage == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "conn" } :
        LET n == msg.from IN
        /\ Can_start_connection_attempt(g)
        /\ CASE n \notin sent_conn[g] \cup recv_conn[g] ->
                    /\ messages' = [ messages EXCEPT
                                        ![g] = @ \ {msg},
                                        ![n] = IF Bad(n) \/ Blacklisted(n, g) THEN @ ELSE @ \cup {conn_msg(g)} ]
                    /\ recv_conn' = [ recv_conn EXCEPT ![g] = @ \cup {n} ]
                    /\ sent_conn' = [ sent_conn EXCEPT ![g] = @ \cup {n} ]
                    /\ in_progress' = [ in_progress EXCEPT ![g] = @ \cup {n} ]
                    /\ UNCHANGED blacklist
                    /\ UNCHANGED connections
                    /\ UNCHANGED recv_ack
                    /\ UNCHANGED recv_meta
                    /\ UNCHANGED sent_ack
                    /\ UNCHANGED sent_meta
             [] n \in sent_conn[g] /\ n \notin recv_conn[g] ->
                    /\ messages' = [ messages EXCEPT
                                        ![g] = @ \ {msg},
                                        ![n] = IF Bad(n) \/ Blacklisted(n, g) THEN @ ELSE @ \cup {meta_msg(g)} ]
                    /\ recv_conn' = [ recv_conn EXCEPT ![g] = @ \cup {n} ]
                    /\ sent_meta' = [ sent_meta EXCEPT ![g] = @ \cup {n} ]
                    /\ UNCHANGED blacklist
                    /\ UNCHANGED connections
                    /\ UNCHANGED recv_ack
                    /\ UNCHANGED recv_meta
                    /\ UNCHANGED sent_ack
                    /\ UNCHANGED sent_conn
                    /\ UNCHANGED in_progress
             [] OTHER -> exit_handshaking(g, n)

\* meta messages

\* @type: (Int, Int, [from: Int, type: Str]) => Bool;
exchange_meta(g, n, msg) ==
    LET type == msg.type IN
    IF n \in sent_meta[g]
    THEN /\ messages' = [ messages EXCEPT
                            ![g] = @ \ {msg},
                            ![n] = IF Bad(n) \/ Blacklisted(n, g) THEN @ ELSE @ \cup {ack_msg(g)} ]
         /\ recv_meta' = [ sent_meta EXCEPT ![g] = @ \cup {n} ]
         /\ sent_ack' = [ sent_ack EXCEPT ![g] = @ \cup {n} ]
         /\ UNCHANGED blacklist
         /\ UNCHANGED connections
         /\ UNCHANGED recv_ack
         /\ UNCHANGED recv_conn
         /\ UNCHANGED sent_conn
         /\ UNCHANGED sent_meta
         /\ UNCHANGED in_progress
    ELSE /\ messages' = [ messages EXCEPT
                            ![g] = @ \ {msg},
                            ![n] = IF Bad(n) \/ Blacklisted(n, g) THEN @ ELSE @ \cup {meta_msg(g)} ]
         /\ recv_meta' = [ recv_meta EXCEPT ![g] = @ \cup {n} ]
         /\ sent_meta' = [ sent_meta EXCEPT ![g] = @ \cup {n} ]
         /\ UNCHANGED blacklist
         /\ UNCHANGED connections
         /\ UNCHANGED recv_ack
         /\ UNCHANGED recv_conn
         /\ UNCHANGED sent_ack
         /\ UNCHANGED sent_conn
         /\ UNCHANGED in_progress

\* @type: Bool;
ExchangeMeta == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "meta" } :
        LET n == msg.from IN
        /\ n \in recv_conn[g]
        /\ n \in sent_conn[g]
        /\ n \notin recv_meta[g]
        /\ n \notin recv_ack[g]
        /\ n \notin sent_ack[g]
        /\ n \in in_progress[g]
        /\ exchange_meta(g, n, msg)

\* ack/nack messages

\* @type: (Int, Int, [from: Int, type: Str]) => Bool;
exchange_ack(g, n, msg) ==
    LET type == msg.type IN
    IF n \in sent_ack[g]
    THEN /\ connections' = [ connections EXCEPT ![g] = @ \cup {n} ]
         /\ messages' = [ messages EXCEPT ![g] = @ \ {msg} ]
         /\ recv_ack' = [ recv_ack EXCEPT ![g] = @ \cup {n} ]
         /\ in_progress' = [ in_progress EXCEPT ![g] = @ \ {n} ]
         /\ UNCHANGED blacklist
         /\ UNCHANGED recv_conn
         /\ UNCHANGED recv_meta
         /\ UNCHANGED sent_ack
         /\ UNCHANGED sent_conn
         /\ UNCHANGED sent_meta
    ELSE /\ connections' = [ connections EXCEPT ![g] = @ \cup {n} ]
         /\ messages' = [ messages EXCEPT
                            ![g] = @ \ {msg},
                            ![n] = IF Bad(n) \/ Blacklisted(n, g) THEN @ ELSE @ \cup {ack_msg(g)} ]
         /\ recv_ack' = [ recv_ack EXCEPT ![g] = @ \cup {n} ]
         /\ sent_ack' = [ sent_ack EXCEPT ![g] = @ \cup {n} ]
         /\ in_progress' = [ in_progress EXCEPT ![g] = @ \ {n} ]
         /\ UNCHANGED blacklist
         /\ UNCHANGED recv_conn
         /\ UNCHANGED recv_meta
         /\ UNCHANGED sent_conn
         /\ UNCHANGED sent_meta

\* @type: Bool;
ExchangeAck == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "ack" } :
        LET n == msg.from IN
        /\ n \in sent_conn[g]
        /\ n \in recv_conn[g]
        /\ n \in sent_meta[g]
        /\ n \in recv_meta[g]
        /\ n \notin recv_ack[g]
        /\ n \in in_progress[g]
        /\ exchange_ack(g, n, msg)

\* @type: (Int, Int, [from: Int, type: Str]) => Bool;
nack(g, n, msg) ==
    /\ blacklist' = [ blacklist EXCEPT ![g] = @ \cup {n} ]
    /\ connections' = [ connections EXCEPT ![g] = @ \ {n} ]
    /\ messages' = [ messages EXCEPT
                        ![g] = { m \in @ : m.from /= n },
                        ![n] = IF Bad(n) \/ Blacklisted(n, g) THEN @ ELSE @ \cup {nack_msg(g)} ]
    /\ recv_conn' = [ recv_conn EXCEPT ![g] = @ \ {n} ]
    /\ sent_conn' = [ sent_conn EXCEPT ![g] = @ \ {n} ]
    /\ recv_meta' = [ recv_meta EXCEPT ![g] = @ \ {n} ]
    /\ sent_meta' = [ sent_meta EXCEPT ![g] = @ \ {n} ]
    /\ recv_ack' = [ recv_ack EXCEPT ![g] = @ \ {n} ]
    /\ sent_ack' = [ sent_ack EXCEPT ![g] = @ \ {n} ]
    /\ in_progress' = [ in_progress EXCEPT ![g] = @ \ {n} ]

\* @type: Bool;
Nack == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type \in { "ack", "meta" } } :
        LET n == msg.from IN
        /\ Num_connections(g) >= MIN
        /\ n \notin connections[g]
        /\ n \in sent_conn[g]
        /\ n \in recv_conn[g]
        /\ nack(g, n, msg)

\* @type: Bool;
HandleNack == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "nack" } :
        LET n == msg.from IN
        /\ n \notin connections[g]
        /\ n \in sent_conn[g]
        /\ n \in recv_conn[g]
        /\ exit_handshaking(g, n)

\* @type: Bool;
HandleBad == \E g \in GOOD_NODES :
    \/ \E msg \in { m \in messages[g] : m.type = "bad" } :
        LET n == msg.from IN exit_handshaking(g, n)
    \/ \E msg \in { m \in messages[g] : m.type \notin { "conn", "nack" } } :
        LET n == msg.from IN
        /\ n \notin recv_conn[g]
        /\ exit_handshaking(g, n)
    \/ \E msg \in { m \in messages[g] : m.type \notin { "meta", "nack" } } :
        LET n == msg.from IN
        /\ n \in recv_conn[g]
        /\ n \in sent_conn[g]
        /\ n \notin recv_meta[g]
        /\ exit_handshaking(g, n)
    \/ \E msg \in { m \in messages[g] : m.type \notin { "ack", "nack" } } :
        LET n == msg.from IN
        /\ n \in sent_conn[g]
        /\ n \in recv_conn[g]
        /\ n \in sent_meta[g]
        /\ n \in recv_meta[g]
        /\ n \notin recv_ack[g]
        /\ exit_handshaking(g, n)

\* Undesirable actions

\* bad node action

\* @type: Bool;
BadNodeSendsGoodNodeMessage == \E g \in GOOD_NODES :
    \E msg \in Bad_messages :
        LET n == msg.from IN
        /\ ~Blacklisted(g, n)
        /\ messages' = [ messages EXCEPT ![g] = @ \cup {msg} ]
        /\ UNCHANGED blacklist
        /\ UNCHANGED connections
        /\ UNCHANGED recv_ack
        /\ UNCHANGED recv_conn
        /\ UNCHANGED recv_meta
        /\ UNCHANGED sent_ack
        /\ UNCHANGED sent_conn
        /\ UNCHANGED sent_meta
        /\ UNCHANGED in_progress

\* @type: Bool;
Timeout == \E g \in GOOD_NODES :
    \/ \E n \in in_progress[g] : exit_handshaking(g, n)
    \/ \E n \in connections[g] :
        /\ g \notin connections[n]
        /\ exit_handshaking(g, n)

(*****************)
(* Specification *)
(*****************)

\* @type: Bool;
Init ==
    /\ blacklist = [ n \in Nodes |-> {} ]
    /\ connections = [ n \in Nodes |-> {} ]
    /\ messages = [ n \in Nodes |-> {} ]
    /\ recv_conn = [ n \in Nodes |-> {} ]
    /\ sent_conn = [ n \in Nodes |-> {} ]
    /\ recv_meta = [ n \in Nodes |-> {} ]
    /\ sent_meta = [ n \in Nodes |-> {} ]
    /\ recv_ack = [ n \in Nodes |-> {} ]
    /\ sent_ack = [ n \in Nodes |-> {} ]
    /\ in_progress = [ n \in Nodes |-> {} ]

\* @type: Bool;
Next ==
    \/ InitiateConnection
    \/ RespondToConnectionMessage
    \/ ExchangeMeta
    \/ ExchangeAck
    \/ Nack
    \/ HandleNack
    \/ HandleBad
    \/ BadNodeSendsGoodNodeMessage
    \/ Timeout

\* @type: Bool;
Spec == Init /\ [][Next]_vars

(*********************)
(* Invariants/Safety *)
(*********************)

\* @type: Bool;
TypeOK ==
    /\ \A g \in GOOD_NODES : blacklist[g] \subseteq Nodes
    /\ \A g \in GOOD_NODES : connections[g] \subseteq Nodes
    /\ \A g \in GOOD_NODES : messages[g] \subseteq Messages
    /\ \A g \in GOOD_NODES : recv_conn[g] \subseteq Nodes
    /\ \A g \in GOOD_NODES : sent_conn[g] \subseteq Nodes
    /\ \A g \in GOOD_NODES : recv_meta[g] \subseteq Nodes
    /\ \A g \in GOOD_NODES : sent_meta[g] \subseteq Nodes
    /\ \A g \in GOOD_NODES : recv_ack[g] \subseteq Nodes
    /\ \A g \in GOOD_NODES : sent_ack[g] \subseteq Nodes
    /\ \A g \in GOOD_NODES : in_progress[g] \subseteq Nodes

\* @type: Bool;
NoSelfInteractions == \A g \in GOOD_NODES :
    /\ g \notin blacklist[g]
    /\ g \notin connections[g]
    /\ g \notin { msg.from : msg \in messages[g] }
    /\ g \notin recv_conn[g]
    /\ g \notin sent_conn[g]
    /\ g \notin recv_meta[g]
    /\ g \notin sent_meta[g]
    /\ g \notin recv_ack[g]
    /\ g \notin sent_ack[g]
    /\ g \notin in_progress[g]

\* @type: Bool;
GoodNodesDoNotExceedMaxConnections ==
    \A g \in GOOD_NODES : Num_connections(g) + Cardinality(in_progress[g]) <= MAX

\* @type: Bool;
GoodNodesNeverHaveMessagesFromBlacklistedPeers ==
    \A g \in GOOD_NODES : { msg \in messages[g] : msg.from \in blacklist[g] } = {}

\* @type: Bool;
GoodNodesHaveExlcusiveInProgressAndConnections ==
    \A g \in GOOD_NODES : in_progress[g] \cap connections[g] = {}

\* @type: Bool;
GoodNodesOnlyConnectToNodesWithWhomTheyHaveExchangedAllMessages ==
    \A g \in GOOD_NODES :
        connections[g] \subseteq recv_conn[g] \cap sent_conn[g] \cap recv_meta[g] \cap sent_meta[g] \cap recv_ack[g] \cap sent_ack[g]

\* @type: Bool;
GoodNodesOnlyExchangeMetaMessagesAfterSendingAndReceivingConnectionMessages ==
    \A g \in GOOD_NODES : recv_meta[g] \cup sent_meta[g] \subseteq recv_conn[g] \cap sent_conn[g]

\* @type: Bool;
GoodNodesOnlyExchangeAckMessagesAfterSendingAndReceivingConnectionAndMetaMessages ==
    \A g \in GOOD_NODES : recv_ack[g] \cup sent_ack[g] \subseteq recv_conn[g] \cap sent_conn[g] \cap recv_meta[g] \cap sent_meta[g]

\* @type: Bool;
Safety == 
    /\ TypeOK
    /\ NoSelfInteractions
    /\ GoodNodesDoNotExceedMaxConnections
    /\ GoodNodesNeverHaveMessagesFromBlacklistedPeers
    /\ GoodNodesHaveExlcusiveInProgressAndConnections
    /\ GoodNodesOnlyConnectToNodesWithWhomTheyHaveExchangedAllMessages
    /\ GoodNodesOnlyExchangeMetaMessagesAfterSendingAndReceivingConnectionMessages
    /\ GoodNodesOnlyExchangeAckMessagesAfterSendingAndReceivingConnectionAndMetaMessages

========================================
