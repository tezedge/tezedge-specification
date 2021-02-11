------------------------------ MODULE HL_Actions ------------------------------

CONSTANTS NumNodes, NumJoins, ValidStates, peerThreshold, connectionThreshold, sizeBound

VARIABLES state, secured, mailbox, recv, sent, joined, peers, phase

LOCAL INSTANCE HL_Utils

(*************************************************************************************)
(* The nodes are already connected to the network and have a valid blockchain state. *)
(* They do not request state from anyone, they share their state with joining nodes. *)
(* The joining nodes represent the nodes that are joining the network.               *)
(* They must do:                                                                     *)
(*  - RequestPeers: get peers from DNS                                               *)
(*  - Handshake: once peers have been obtained, make secure connections with peers   *)
(*  - Transition: once connections have been made, start bootstrapping               *)
(*  - Bootstrap: request state from connections                                      *)
(*  - Join: once a valid state has been obtained, join the network                   *)
(*************************************************************************************)

(***********************)
(* Handshaking Actions *)
(***********************)

(* Request Peers *)
\* Requesting peers from the DNS
\* Joining nodes in the "init" phase request peers and transition to the "handshake" phase
Request_peers(j, ps) ==
    /\ phase' = [ phase EXCEPT ![j] = "handshake" ]
    /\ peers' = [ peers EXCEPT ![j] = @ \cup ps ]
    /\ UNCHANGED <<sent, joined, recv, secured, mailbox, state>>

\* An init node requests peers from the DNS
InitRequestPeers ==
    \E j \in init :
        \E ps \in SUBSET nodes :
            /\ Cardinality(ps) >= peerThreshold
            /\ Request_peers(j, ps)



(* Handshake *)
\* Once peers have been obtained (i.e. the joining node is in the "handshake" phase
\* and they are peerSaturated), these joining nodes attempt to handshake with their peers
Handshake(j, n) ==
    /\ secured' = [ secured EXCEPT !.join[j] = @ \cup {n}, !.node[n] = @ \cup {j} ]
    /\ UNCHANGED <<sent, joined, peers, phase, recv, mailbox, state>>

\* A handshaking node makes a secure connection with a peer
HandshakesHappen ==
    \E j \in handshaking :
        \E n \in peers[j] :
            /\ ~connected(j, n)
            /\ ~connectionSaturated(j)
            /\ Handshake(j, n)

(**************)
(* Transition *)
(**************)

\* Once a handshaking node is connectionSaturated, they can start bootstrapping
Transition(j) ==
    /\ phase' = [ phase EXCEPT ![j] = "bootstrap" ]
    /\ UNCHANGED <<sent, joined, peers, recv, secured, mailbox, state>>

\* A connectionSaturated handshaking node transitions to bootstrap phase
TransitionHappen ==
    \E j \in handshaking :
        /\ connectionSaturated(j)
        /\ Transition(j)

(*************************)
(* Bootstrapping Actions *)
(*************************)

(*************)
(* Bootstrap *)
(*************)

\* Once a joining node is bootstrapping, they can request state from their connections
Bootstrap(j, n) ==
    LET msg == Req(j, n, "Get_current_state") \* j requests the current state from n
    IN /\ mailbox' = [ mailbox EXCEPT !.node[n] = check_append(@, msg) ]
       /\ sent' = [ sent EXCEPT !.join[j] = check_append(@, msg) ]
       /\ UNCHANGED <<joined, peers, phase, recv, secured, state>>

\* A bootstrapping node can request state from a connection
GettingBootstrap ==
    \E j \in bootstrapping :
        \E n \in secured.join[j] :
            /\ connected(j, n)                   \* j and n are connected
            /\ ~hasSeenMostRecentStateFrom(j, n) \* j has not seen the most recent state from n
            /\ check_sent(TRUE, j)             \* j can send a message
            /\ Bootstrap(j, n)

(***********)
(* Receive *)
(***********)

\* If a message has been sent to a node and they can receive it, they do
Receive_node(n) ==
    LET msg  == Head(mailbox.node[n])
        from == msg.from
        to   == msg.to
        type == msg.type
    IN /\ recv' = [ recv EXCEPT !.node[n] = Append(@, msg) ] \* receive the sent message
       /\ mailbox' = [ mailbox EXCEPT !.node[n] = Tail(@) ]  \* delete msg from mailbox
       /\ sent' = [ sent EXCEPT !.node[n] = filter(@, msg) ]
       /\ UNCHANGED <<joined, peers, phase, secured, state>>

Receive_join(j) ==
    LET msg  == Head(mailbox.join[j])
        from == msg.from
        to   == msg.to
        type == msg.type
    IN /\ recv' = [ recv EXCEPT !.join[j] = Append(@, msg) ] \* receive the sent message
       /\ mailbox' = [ mailbox EXCEPT !.join[j] = Tail(@) ]  \* delete msg from mailbox
       /\ sent' = [ sent EXCEPT !.join[j] = filter(@, msg) ]
       /\ UNCHANGED <<joined, peers, phase, secured, state>>

\* If a message has been sent to a node, they can receive it
Receive ==
    \/ \E j \in bootstrapping :
           /\ check_recv(TRUE, j)  \* the node can receive a message
           /\ mailbox.join[j] /= <<>> \* messages have been sent to the node
           /\ Receive_join(j)
    \/ \E n \in nodes :
           /\ check_recv(FALSE, n) \* the node can receive a message
           /\ mailbox.node[n] /= <<>> \* messages have been sent to the node
           /\ Receive_node(n)

(**********)
(* Handle *)
(**********)

\* Joining node incorporates state message into state
Handle_join(j) ==
    LET msg == Head(recv.join[j])
        n   == msg.from
        st  == msg.data
        ack == Ack(j, n, "Ack_current_state")
    IN /\ mailbox' = [ mailbox EXCEPT !.node[n] = check_append(@, ack) ]
       /\ recv' = [ recv EXCEPT !.join[j] = Tail(@) ]
       /\ sent' = [ sent EXCEPT !.join[j] = check_append(@, msg) ]
       /\ state' = [ state EXCEPT !.join[j] = check_append(@, st) ]
       /\ UNCHANGED <<joined, peers, phase, secured>>

\* Established node responds to a message from a joining node
Handle_node(n) ==
    LET m   == Head(recv.node[n])
        j   == m.from
        st  == state.node[n]
        msg == Adv(n, j, "Current_state", st)
    IN /\ mailbox' = [ mailbox EXCEPT !.join[j] = check_append(@, msg)  ]
       /\ recv' = [ recv EXCEPT !.node[n] = Tail(@) ]
       /\ sent' = [ sent EXCEPT !.node[n] = check_append(@, msg) ]
       /\ UNCHANGED <<joined, peers, phase, secured, state>>

\* If a node has received a message, they can respond to it
Handle ==
    \/ \E j \in bootstrapping :
           /\ recv.join[j] /= <<>>
           /\ Handle_join(j)
    \/ \E n \in nodes :
           /\ recv.node[n] /= <<>>
           /\ Handle_node(n)

(*************)
(* Advertise *)
(*************)

\* An established node can advertise their state to their bootstrapping connections.
\* Since these messages are not specifically requested by the bootstrapping nodes,
\* nothing is added to the established node's sent queue.
Advertise_state(n) ==
    /\ mailbox' = [ mailbox EXCEPT !.join = Broadcast(@, n) ]
    /\ UNCHANGED <<sent, joined, peers, phase, recv, secured, state>>

\* An established node can advertise their state to their connections
Advertise ==
    \E n \in nodes :
        /\ secured.node[n] \cap bootstrapping /= {}
        /\ Advertise_state(n)

\*(**************)
\*(* Send_again *)
\*(**************)
\*
\*\* If a node is expecting a response, they can send the corresponding message again *)
\*Send_again_join(j) ==
\*    /\ sent.join[j] /= <<>>
\*    /\ LET exp  == Head(sent.join[j])
\*           to   == exp.from
\*           type == exp.msg
\*       IN CASE type = "Current_state" ->
\*            mailbox' = [ mailbox EXCEPT !.node[to] =
\*              CASE check_mailbox(FALSE, to) -> Append(@, Msg(j, to, "Get_current_state"))
\*                [] OTHER -> @ ]
\*    /\ UNCHANGED <<sent, joined, peers, phase, recv, secured, state>>
\*
\*Send_again_node(n) ==
\*    /\ sent.node[n] /= <<>>
\*    /\ LET exp  == Head(sent.node[n])
\*           to   == exp.from
\*           type == exp.msg
\*           curr == state.node[n]
\*       IN CASE type = "Ack_current_state" ->
\*            mailbox' = [ mailbox EXCEPT !.join[to] =
\*              CASE check_mailbox(TRUE, to) -> Append(@, Msg(n, to, <<"Current_state", curr>>))
\*                [] OTHER -> @ ]
\*    /\ UNCHANGED <<sent, joined, peers, phase, recv, secured, state>>
\*
\*\* If an expected response has not been received, send original message again
\*Send_again ==
\*    \/ \E j \in bootstrapping : Send_again_join(j)
\*    \/ \E n \in nodes : Send_again_node(n)
\*
\*(********)
\*(* Drop *)
\*(********)
\*
\*\* Messages can be dropped only before they are received.
\*Drop_join(j) ==
\*    /\ mailbox.join[j] /= <<>>
\*    /\ mailbox' = [ mailbox EXCEPT !.join[j] = Tail(@) ] \* a message is dropped
\*    /\ UNCHANGED <<sent, joined, peers, phase, recv, secured, state>>
\*
\*Drop_node(n) ==
\*    /\ mailbox.node[n] /= <<>>
\*    /\ mailbox' = [ mailbox EXCEPT !.node[n] = Tail(@) ] \* a message is dropped
\*    /\ UNCHANGED <<sent, joined, peers, phase, recv, secured, state>>
\*
\*\* Either an established or joining node drops a message
\*Drop ==
\*    \/ \E j \in joining : Drop_join(j)
\*    \/ \E n \in nodes : Drop_node(n)

(********)
(* Join *)
(********)
\* Once a joining node has sufficiently many peers and connections and
\* has bootstrapped state, they are ready and able to join the network.
Join(j) ==
    /\ phase' = [ phase EXCEPT ![j] = "joined" ]
    /\ joined' = joined \cup {j}
    /\ UNCHANGED <<sent, peers, recv, secured, mailbox, state>>

\* Once a bootstrapping node has successfully bootstrapped, they can join the network
BootstrapperJoin ==
    \E j \in bootstrapping :
        /\ hasState(j)
        /\ Join(j)

================================================================================
