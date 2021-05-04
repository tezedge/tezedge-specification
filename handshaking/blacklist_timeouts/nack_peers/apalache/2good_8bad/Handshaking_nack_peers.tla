---------- MODULE Handshaking_nack_peers ----------

EXTENDS FiniteSets, Naturals

CONSTANTS
    \* @type: Set(Int);
    BAD_NODES,
    \* @type: Set(Int);
    GOOD_NODES,
    \* @type: Int;
    MIN,
    \* @type: Int;
    MAX,
    \* @type: Int;
    MIN_PEERS

VARIABLES
    \* @type: Int -> Set(Int);
    blacklist,
    \* @type: Int -> Set(Int);
    connections,
    \* @typeDef: NonPeerMsg = [from: Int, type: Str];
    \* @typeDef: PeerMsg = [from: Int, peers: Set(Int), type: Str];
    \* @typeDef: MSG = NonPeerMsg | PeerMsg;
    \* @type: Set(MSG);
    messages,
    \* @type: Int -> Set(Int);
    peers,
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

vars == <<blacklist, connections, messages, peers, recv_ack, recv_conn, recv_meta, sent_ack, sent_conn, sent_meta, in_progress>>

ASSUME BAD_NODES \cap GOOD_NODES = {}
ASSUME MIN \in Nat /\ MIN > 0
ASSUME MAX \in Nat /\ MIN <= MAX /\ MAX < Cardinality(BAD_NODES \cup GOOD_NODES)
\* For combinatorial reasons, we must also have:
ASSUME Cardinality(GOOD_NODES) > MIN
ASSUME
    LET N == Cardinality(BAD_NODES \cup GOOD_NODES) IN
    IF N = 3 THEN MAX /= 1 ELSE MAX /= 2 /\ MAX /= N - 2
ASSUME MIN_PEERS \in Nat /\ MIN <= MIN_PEERS

----

(***********)
(* Helpers *)
(***********)

\* @type: (Int) => NonPeerMsg;
conn_msg(from) == [ type |-> "conn", from |-> from ]

\* @type: (Int) => NonPeerMsg;
meta_msg(from) == [ type |-> "meta", from |-> from ]

\* @type: (Int) => NonPeerMsg;
ack_msg(from) == [ type |-> "ack", from |-> from ]

\* @type: (Int) => NonPeerMsg;
nack_msg(from) == [ type |-> "nack", from |-> from ]

\* @type: (Int, Set(Int)) => PeerMsg;
nack_peers_msg(from, ps) == [ type |-> "nack", from |-> from, peers |-> ps ]

\* @type: Set(Int);
Nodes == BAD_NODES \cup GOOD_NODES

\* @type: (Int) => Bool;
Bad(n) == n \in BAD_NODES

\* @type: Set(MSG);
Bad_messages == [ type : {"conn", "meta", "ack", "nack", "bad"}, from : BAD_NODES ]

\* @type: Set(MSG);
Good_messages == [ type : {"nack"}, peers : SUBSET Nodes, from : GOOD_NODES ] \cup
    [ type : {"conn", "meta", "ack", "nack"}, from : GOOD_NODES ]

\* @type: Set(MSG);
Messages == Bad_messages \cup Good_messages

\* @type: (Int) => Int;
Num_connections(g) == Cardinality(connections[g])

\* @type: (Int) => Bool;
Can_start_connection_attempt(g) == Num_connections(g) + Cardinality(in_progress[g]) < MAX

\* @type: (Int, Int) => Bool;
Blacklisted(g, n) == n \in blacklist[g]

\* @type: (Int, Int) => Bool;
Connected(g, h) == g \in connections[h] /\ h \in connections[g]

PeerSaturated == \A n \in Nodes : Cardinality(peers[n]) + Cardinality(blacklist[n]) >= MIN_PEERS

(***********)
(* Actions *)
(***********)

\* Good node actions

\* @type: (Int, Int) => Bool;
exit_handshaking(g, n) ==
    /\ blacklist' = [ blacklist EXCEPT ![g] = @ \cup {n}]
    /\ connections' = [ connections EXCEPT ![g] = @ \ {n} ]
    /\ messages' = [ messages EXCEPT ![g] = { msg \in @ : msg.from /= n } ]
    /\ peers' = [ peers EXCEPT ![g] = @ \ {n} ]
    /\ recv_conn' = [ recv_conn EXCEPT ![g] = @ \ {n} ]
    /\ sent_conn' = [ sent_conn EXCEPT ![g] = @ \ {n} ]
    /\ recv_meta' = [ recv_meta EXCEPT ![g] = @ \ {n} ]
    /\ sent_meta' = [ sent_meta EXCEPT ![g] = @ \ {n} ]
    /\ recv_ack' = [ recv_ack EXCEPT ![g] = @ \ {n} ]
    /\ sent_ack' = [ sent_ack EXCEPT ![g] = @ \ {n} ]
    /\ in_progress' = [ in_progress EXCEPT ![g] = @ \ {n} ]

\* @type: (Int, Int, Set(Int)) => Bool;
exit_handshaking_with_peers(g, n, ps) ==
    /\ blacklist' = [ blacklist EXCEPT ![g] = @ \cup {n}]
    /\ connections' = [ connections EXCEPT ![g] = @ \ {n} ]
    /\ messages' = [ messages EXCEPT ![g] = { msg \in @ : msg.from /= n } ]
    /\ peers' = [ peers EXCEPT ![n] = (@ \cup ps) \ {n} ]
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
    /\ UNCHANGED <<blacklist, connections, peers, recv_ack, recv_conn, recv_meta, sent_ack, sent_meta>>

InitiateConnection == \E g \in GOOD_NODES, n \in Nodes :
    /\ Can_start_connection_attempt(g)
    /\ PeerSaturated
    /\ n \in peers[g]
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

RespondToConnectionMessage == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "conn" } :
        LET n == msg.from IN
        /\ Can_start_connection_attempt(g)
        /\ PeerSaturated
        /\ CASE n \notin sent_conn[g] \cup recv_conn[g] ->
                    /\ messages' = [ messages EXCEPT
                                        ![g] = @ \ {msg},
                                        ![n] = IF Bad(n) \/ Blacklisted(n, g) THEN @ ELSE @ \cup {conn_msg(g)} ]
                    /\ peers' = [ peers EXCEPT ![g] = @ \cup {n} ]
                    /\ recv_conn' = [ recv_conn EXCEPT ![g] = @ \cup {n} ]
                    /\ sent_conn' = [ sent_conn EXCEPT ![g] = @ \cup {n} ]
                    /\ in_progress' = [ in_progress EXCEPT ![g] = @ \cup {n} ]
                    /\ UNCHANGED <<blacklist, connections, recv_ack, recv_meta, sent_ack, sent_meta>>
             [] n \in sent_conn[g] /\ n \notin recv_conn[g] ->
                    /\ messages' = [ messages EXCEPT
                                        ![g] = @ \ {msg},
                                        ![n] = IF Bad(n) \/ Blacklisted(n, g) THEN @ ELSE @ \cup {meta_msg(g)} ]
                    /\ peers' = [ peers EXCEPT ![g] = @ \cup {n} ]
                    /\ recv_conn' = [ recv_conn EXCEPT ![g] = @ \cup {n} ]
                    /\ sent_meta' = [ sent_meta EXCEPT ![g] = @ \cup {n} ]
                    /\ UNCHANGED <<blacklist, connections, recv_ack, recv_meta, sent_ack, sent_conn, in_progress>>
             [] OTHER -> exit_handshaking(g, n)

\* meta messages

\* @type: (Int, Int, Set(MSG)) => Bool;
exchange_meta(g, n, msg) ==
    LET type == msg.type IN
    IF n \in sent_meta[g]
    THEN /\ messages' = [ messages EXCEPT
                            ![g] = @ \ {msg},
                            ![n] = IF Bad(n) \/ Blacklisted(n, g) THEN @ ELSE @ \cup {ack_msg(g)} ]
         /\ recv_meta' = [ sent_meta EXCEPT ![g] = @ \cup {n} ]
         /\ sent_ack' = [ sent_ack EXCEPT ![g] = @ \cup {n} ]
         /\ UNCHANGED <<blacklist, connections, peers, recv_ack, recv_conn, sent_conn, sent_meta, in_progress>>
    ELSE /\ messages' = [ messages EXCEPT
                            ![g] = @ \ {msg},
                            ![n] = IF Bad(n) \/ Blacklisted(n, g) THEN @ ELSE @ \cup {meta_msg(g)} ]
         /\ recv_meta' = [ recv_meta EXCEPT ![g] = @ \cup {n} ]
         /\ sent_meta' = [ sent_meta EXCEPT ![g] = @ \cup {n} ]
         /\ UNCHANGED <<blacklist, connections, peers, recv_ack, recv_conn, sent_ack, sent_conn, in_progress>>

ExchangeMeta == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "meta" } :
        LET n == msg.from IN
        /\ PeerSaturated
        /\ n \in peers[g]
        /\ n \in recv_conn[g]
        /\ n \in sent_conn[g]
        /\ n \notin recv_meta[g]
        /\ n \notin recv_ack[g]
        /\ n \notin sent_ack[g]
        /\ n \in in_progress[g]
        /\ exchange_meta(g, n, msg)

\* ack/nack messages

\* @type: (Int, Int, Set(MSG)) => Bool;
exchange_ack(g, n, msg) ==
    LET type == msg.type IN
    IF n \in sent_ack[g]
    THEN /\ connections' = [ connections EXCEPT ![g] = @ \cup {n} ]
         /\ messages' = [ messages EXCEPT ![g] = @ \ {msg} ]
         /\ recv_ack' = [ recv_ack EXCEPT ![g] = @ \cup {n} ]
         /\ in_progress' = [ in_progress EXCEPT ![g] = @ \ {n} ]
         /\ UNCHANGED <<blacklist, peers, recv_conn, recv_meta, sent_ack, sent_conn, sent_meta>>
    ELSE /\ connections' = [ connections EXCEPT ![g] = @ \cup {n} ]
         /\ messages' = [ messages EXCEPT
                            ![g] = @ \ {msg},
                            ![n] = IF Bad(n) \/ Blacklisted(n, g) THEN @ ELSE @ \cup {ack_msg(g)} ]
         /\ recv_ack' = [ recv_ack EXCEPT ![g] = @ \cup {n} ]
         /\ sent_ack' = [ sent_ack EXCEPT ![g] = @ \cup {n} ]
         /\ in_progress' = [ in_progress EXCEPT ![g] = @ \ {n} ]
         /\ UNCHANGED <<blacklist, peers, recv_conn, recv_meta, sent_conn, sent_meta>>

ExchangeAck == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "ack" } :
        LET n == msg.from IN
        /\ PeerSaturated
        /\ n \in peers[g]
        /\ n \in sent_conn[g]
        /\ n \in recv_conn[g]
        /\ n \in sent_meta[g]
        /\ n \in recv_meta[g]
        /\ n \notin recv_ack[g]
        /\ n \in in_progress[g]
        /\ exchange_ack(g, n, msg)

\* @type: (Int, Int, Set(MSG)) => Bool;
nack_no_peers(g, n, msg) ==
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
    /\ UNCHANGED peers

\* @type: (Int, Int, Set(MSG), Set(Int)) => Bool;
nack_peers(g, n, msg, ps) ==
    /\ blacklist' = [ blacklist EXCEPT ![g] = @ \cup {n} ]
    /\ connections' = [ connections EXCEPT ![g] = @ \ {n} ]
    /\ messages' = [ messages EXCEPT
                        ![g] = { m \in @ : m.from /= n },
                        ![n] = IF Bad(n) \/ Blacklisted(n, g) THEN @ ELSE @ \cup {nack_peers_msg(g, ps)} ]
    /\ recv_conn' = [ recv_conn EXCEPT ![g] = @ \ {n} ]
    /\ sent_conn' = [ sent_conn EXCEPT ![g] = @ \ {n} ]
    /\ recv_meta' = [ recv_meta EXCEPT ![g] = @ \ {n} ]
    /\ sent_meta' = [ sent_meta EXCEPT ![g] = @ \ {n} ]
    /\ recv_ack' = [ recv_ack EXCEPT ![g] = @ \ {n} ]
    /\ sent_ack' = [ sent_ack EXCEPT ![g] = @ \ {n} ]
    /\ in_progress' = [ in_progress EXCEPT ![g] = @ \ {n} ]
    /\ UNCHANGED peers

Nack == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type \in { "ack", "meta" } } :
        LET n == msg.from IN
        /\ PeerSaturated
        /\ Num_connections(g) >= MIN
        /\ n \notin connections[g]
        /\ n \in peers[g]
        /\ n \in sent_conn[g]
        /\ n \in recv_conn[g]
        /\ \/ nack_no_peers(g, n, msg)
           \/ \E ps \in SUBSET (peers[g] \ {n}) \ {{}} : nack_peers(g, n, msg, ps)

HandleNack == \E g \in GOOD_NODES :
    \E msg \in { m \in messages[g] : m.type = "nack" } :
        LET n  == msg.from
            ps == msg.peers
        IN
        /\ PeerSaturated
        /\ n \notin connections[g]
        /\ n \in peers[g]
        /\ n \in sent_conn[g]
        /\ n \in recv_conn[g]
        /\ IF ps = {}
           THEN exit_handshaking(g, n)
           ELSE exit_handshaking_with_peers(g, n, ps)

HandleBad == \E g \in GOOD_NODES :
    \/ \E msg \in { m \in messages[g] : m.type = "bad" } :
        LET n == msg.from IN
        /\ PeerSaturated
        /\ n \in peers[g]
        /\ exit_handshaking(g, n)
    \/ \E msg \in { m \in messages[g] : m.type \notin { "conn", "nack" } } :
        LET n == msg.from IN
        /\ PeerSaturated
        /\ n \in peers[g]
        /\ n \notin recv_conn[g]
        /\ exit_handshaking(g, n)
    \/ \E msg \in { m \in messages[g] : m.type \notin { "meta", "nack" } } :
        LET n == msg.from IN
        /\ PeerSaturated
        /\ n \in peers[g]
        /\ n \in recv_conn[g]
        /\ n \in sent_conn[g]
        /\ n \notin recv_meta[g]
        /\ exit_handshaking(g, n)
    \/ \E msg \in { m \in messages[g] : m.type \notin { "ack", "nack" } } :
        LET n == msg.from IN
        /\ PeerSaturated
        /\ n \in peers[g]
        /\ n \in sent_conn[g]
        /\ n \in recv_conn[g]
        /\ n \in sent_meta[g]
        /\ n \in recv_meta[g]
        /\ n \notin recv_ack[g]
        /\ exit_handshaking(g, n)

\* Undesirable actions

\* bad node action
BadNodeSendsGoodNodeMessage == \E g \in GOOD_NODES :
    \E msg \in Bad_messages :
        LET n == msg.from IN
        /\ ~Blacklisted(g, n)
        /\ PeerSaturated
        /\ g \in peers[n]
        /\ messages' = [ messages EXCEPT ![g] = @ \cup {msg} ]
        /\ UNCHANGED <<blacklist, connections, peers, recv_ack, recv_conn, recv_meta, sent_ack, sent_conn, sent_meta, in_progress>>

Timeout == \E g \in GOOD_NODES :
    /\ PeerSaturated
    /\ \/ \E n \in in_progress[g] : exit_handshaking(g, n)
       \/ \E n \in connections[g] : g \notin connections[n] /\ exit_handshaking(g, n)

\* @type: (Int, Set(Int)) => Bool;
init_peers(n, ps) ==
    /\ peers' = [ peers EXCEPT ![n] = ps ]
    /\ UNCHANGED <<blacklist, connections, messages, recv_ack, recv_conn, recv_meta, sent_ack, sent_conn, sent_meta, in_progress>>

InitPeers == \E n \in Nodes :
    \E ps \in SUBSET (Nodes \ {n}) :
        /\ peers[n] = {}
        /\ Cardinality(ps) >= MIN_PEERS
        /\ init_peers(n, ps)

(*****************)
(* Specification *)
(*****************)

Init ==
    /\ blacklist = [ n \in Nodes |-> {} ]
    /\ connections = [ n \in Nodes |-> {} ]
    /\ messages = [ n \in Nodes |-> {} ]
    /\ peers = [ n \in Nodes |-> {} ]
    /\ recv_conn = [ n \in Nodes |-> {} ]
    /\ sent_conn = [ n \in Nodes |-> {} ]
    /\ recv_meta = [ n \in Nodes |-> {} ]
    /\ sent_meta = [ n \in Nodes |-> {} ]
    /\ recv_ack = [ n \in Nodes |-> {} ]
    /\ sent_ack = [ n \in Nodes |-> {} ]
    /\ in_progress = [ n \in Nodes |-> {} ]

Next ==
    \/ InitPeers
    \/ InitiateConnection
    \/ RespondToConnectionMessage
    \/ ExchangeMeta
    \/ ExchangeAck
    \/ Nack
    \/ HandleNack
    \/ HandleBad
    \/ BadNodeSendsGoodNodeMessage
    \/ Timeout

Spec == Init /\ [][Next]_vars

(*********************)
(* Invariants/Safety *)
(*********************)

TypeOK ==
    /\ blacklist \in [ Nodes -> SUBSET Nodes ]
    /\ connections \in [ Nodes -> SUBSET Nodes ]
    /\ messages \in [ Nodes -> SUBSET Messages ]
    /\ peers \in [ Nodes -> SUBSET Nodes ]
    /\ recv_conn \in [ Nodes -> SUBSET Nodes ]
    /\ sent_conn \in [ Nodes -> SUBSET Nodes ]
    /\ recv_meta \in [ Nodes -> SUBSET Nodes ]
    /\ sent_meta \in [ Nodes -> SUBSET Nodes ]
    /\ recv_ack \in [ Nodes -> SUBSET Nodes ]
    /\ sent_ack \in [ Nodes -> SUBSET Nodes ]
    /\ in_progress \in [ Nodes -> SUBSET Nodes ]

NoSelfInteractions == \A g \in GOOD_NODES :
    /\ g \notin blacklist[g]
    /\ g \notin connections[g]
    /\ g \notin { msg.from : msg \in messages[g] }
    /\ g \notin peers[g]
    /\ g \notin recv_conn[g]
    /\ g \notin sent_conn[g]
    /\ g \notin recv_meta[g]
    /\ g \notin sent_meta[g]
    /\ g \notin recv_ack[g]
    /\ g \notin sent_ack[g]
    /\ g \notin in_progress[g]

GoodNodesOnlyConnectWithPeers == \A g \in GOOD_NODES : connections[g] \subseteq peers[g]

GoodNodesDoNotExceedMaxConnections == \A g \in GOOD_NODES :
    Num_connections(g) + Cardinality(in_progress[g]) <= MAX

GoodNodesOnlyExchangeMessagesWithPeers == \A g \in GOOD_NODES :
    recv_conn[g] \cup sent_conn[g] \cup recv_meta[g] \cup sent_meta[g] \cup recv_ack[g] \cup sent_ack[g] \subseteq peers[g]

GoodNodesNeverHaveMessagesFromBlacklistedPeers == \A g \in GOOD_NODES :
    { msg \in messages[g] : msg.from \in blacklist[g] } = {}

GoodNodesHaveExlcusiveInProgressAndConnections == \A g \in GOOD_NODES : in_progress[g] \cap connections[g] = {}

GoodNodesOnlyConnectToNodesWithWhomTheyHaveExchangedAllMessages == \A g \in GOOD_NODES :
    connections[g] = recv_conn[g] \cap sent_conn[g] \cap recv_meta[g] \cap sent_meta[g] \cap recv_ack[g] \cap sent_ack[g]

GoodNodesOnlyExchangeMetaMessagesAfterSendingAndReceivingConnectionMessages == \A g \in GOOD_NODES :
    recv_meta[g] \cup sent_meta[g] \subseteq recv_conn[g] \cap sent_conn[g]

GoodNodesOnlyExchangeAckMessagesAfterSendingAndReceivingConnectionAndMetaMessages == \A g \in GOOD_NODES :
    recv_ack[g] \cup sent_ack[g] \subseteq recv_conn[g] \cap sent_conn[g] \cap recv_meta[g] \cap sent_meta[g]

Safety ==
    /\ NoSelfInteractions
    /\ GoodNodesOnlyConnectWithPeers
    /\ GoodNodesDoNotExceedMaxConnections
    /\ GoodNodesOnlyExchangeMessagesWithPeers
    /\ GoodNodesNeverHaveMessagesFromBlacklistedPeers
    /\ GoodNodesHaveExlcusiveInProgressAndConnections
    /\ GoodNodesOnlyConnectToNodesWithWhomTheyHaveExchangedAllMessages
    /\ GoodNodesOnlyExchangeMetaMessagesAfterSendingAndReceivingConnectionMessages
    /\ GoodNodesOnlyExchangeAckMessagesAfterSendingAndReceivingConnectionAndMetaMessages

\* inductive invariant
IndInv == TypeOK /\ Safety

===================================================
