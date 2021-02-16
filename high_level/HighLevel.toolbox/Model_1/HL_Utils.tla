------------------------------- MODULE HL_Utils -------------------------------

EXTENDS Utils

CONSTANTS NumNodes, NumJoins, ValidStates, peerThreshold, connectionThreshold, sizeBound

VARIABLES state, secured, mailbox, recv, sent, joined, peers, phase

nodes == 1..NumNodes

joining == 1..NumJoins

---------------------------------------------------------------------------------

(***************************)
(* Phases of joining nodes *)
(***************************)

\* Joining nodes in init only request peers from DNS
\* Joining nodes in handshaking only attempt to make connections with peers (established nodes)
\* Handshaking nodes are peerSaturated
\* Joining nodes in bootstrapping only request state from connected established nodes
\* Bootstrapping nodes are peerSaturated and connectionSaturated

init == { j \in joining : phase[j] = "init" }

handshaking == { j \in joining : phase[j] = "handshake" }

bootstrapping == { j \in joining : phase[j] = "bootstrap" }

PossiblePhases == { "init", "handshake", "bootstrap", "joined" }

(*********)
(* Peers *)
(*********)

peerSaturated(j) == Cardinality(peers[j]) >= peerThreshold

connected(j, n) ==
    /\ n \in secured.join[j]
    /\ j \in secured.node[n]

connections(j) == { n \in nodes : connected(j, n) }

connectionSaturated(j) == Cardinality(connections(j)) >= connectionThreshold

connectionSaturatedFrom(n, S) == Cardinality(secured.node[n]) >= connectionThreshold

hasState(j) == state.join[j] /= <<>>

hasSeenMostRecentStateFrom(j, n) == state.node[n] \in ToSet(state.join[j])

---------------------------------------------------------------------------------

(************)
(* Messages *)
(************)

\* Messages sent by joing nodes
AckMsgTypes == { "Ack_current_state" }

ReqMsgTypes == { "Get_current_state" }

JoinMsgTypes == AckMsgTypes \cup ReqMsgTypes

JoinMsgs == [ from : joining, to : nodes, type : JoinMsgTypes ]

\* Messages sent by established nodes
AdvMsgTypes == { "Current_state" }

NodeMsgs == [ from : nodes, to : joining, type : AdvMsgTypes, data : ValidStates ]

\* All messages
Messages == JoinMsgs \cup NodeMsgs

\* acknowledgement
isValidAck(msg) ==
    /\ DOMAIN msg = { "from", "to", "type" }
    /\ msg.type \in AckMsgTypes

Ack(from, to, type) ==
    LET msg == [ from |-> from, to |-> to, type |-> type ]
    IN CASE isValidAck(msg) -> msg

\* advertisement
isValidAdv(msg) ==
    /\ DOMAIN msg = { "from", "to", "type", "data" }
    /\ msg.type \in AdvMsgTypes
    /\ msg.data \in ValidStates

Adv(from, to, type, data) ==
    LET msg == [ from |-> from, to |-> to, type |-> type, data |-> data ]
    IN CASE isValidAdv(msg) -> msg

\* request
isValidReq(msg) ==
    /\ DOMAIN msg = { "from", "to", "type" }
    /\ msg.type \in ReqMsgTypes

Req(from, to, type) ==
    LET msg == [ from |-> from, to |-> to, type |-> type ]
    IN CASE isValidReq(msg) -> msg

\* filtering messages
\* @type: (Seq([from: Int, to: Int, type: Str]), [from: Int, to: Int, type: Str]) => Seq([from: Int, to: Int, type: Str]);
filter(queue, msg) ==
    LET \* @type: ([from: Int, to: Int, type: Str]) => Bool;
        keep(m) ==
          \/ m.from /= msg.from
          \/ m.to /= msg.to
          \/ msg.type = "Current_state" => m.type = "Get_current_state"
          \/ m.type /= "Current_state"
    IN SelectSeq(queue, keep)
    
--------------------------------------------------------------------------------

(*********************)
(* Helpful operators *)
(*********************)

\* valid state predicate
isValidState(st) == st \in ValidStates

\* Check that [m]'s mailbox is not full
check_mailbox(b, m) ==
    CASE b /\ m \in joining -> Len(mailbox.join[m]) < sizeBound
      [] ~b /\ m \in nodes  -> Len(mailbox.node[m]) < sizeBound

\* Check that [m]'s recv queue is not full
check_recv(b, m) ==
    CASE b /\ m \in joining -> Len(recv.join[m]) < sizeBound
      [] ~b /\ m \in nodes  -> Len(recv.node[m]) < sizeBound

\* Check that [m]'s sent queue is not full
check_sent(b, m) ==
    CASE b /\ m \in joining -> Len(sent.join[m]) < sizeBound
      [] ~b /\ m \in nodes  -> Len(sent.node[m]) < sizeBound

\* Check that [m]'s state queue is not full
check_state(b, m) == Len(state.join[m]) < sizeBound

\* Check that the length of [m]'s mailbox does not exceed sizeBound
ok_mailbox(b, m) ==
    CASE b /\ m \in joining -> Len(mailbox.join[m]) <= sizeBound
      [] ~b /\ m \in nodes  -> Len(mailbox.node[m]) <= sizeBound

\* Check that the length of [m]'s recv queue does not exceed sizeBound
ok_recv(b, m) ==
    CASE b /\ m \in joining -> Len(recv.join[m]) <= sizeBound
      [] ~b /\ m \in nodes  -> Len(recv.node[m]) <= sizeBound

\* Check that the length of [m]'s sent queue does not exceed sizeBound
ok_sent(b, m) ==
    CASE b /\ m \in joining -> Len(sent.join[m]) <= sizeBound
      [] ~b /\ m \in nodes  -> Len(sent.node[m]) <= sizeBound

\* Check that the length of [m]'s state queue does not exceed sizeBound
ok_state(m) == Len(state.join[m]) <= sizeBound

check_append(queue, data) ==
    CASE Len(queue) < sizeBound -> Append(queue, data)
      [] OTHER -> queue

Broadcast(mlb, n) == [ j \in joining |->
    LET conns == secured.node[n] \cap bootstrapping
    IN CASE j \in conns -> check_append(mlb.join[j], Adv(n, j, "Current_state", state.node[n]))
         [] OTHER -> mlb.join[j] ]

================================================================================
