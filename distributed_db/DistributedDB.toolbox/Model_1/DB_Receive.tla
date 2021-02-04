---------------------------- MODULE DB_Receive -----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages
LOCAL INSTANCE Utils

----------------------------------------------------------------------------

(*******************)
(* Receive actions *)
(*******************)

(* Nodes can either receive or drop messages that are sent to them *)

\* [node] receives a message on [chain]
Receive_msg(node, chain) ==
    LET msgs == network_info.sent[chain][node]
        in_q == node_info.messages[node][chain]
        msg  == Pick(msgs)
    IN \* [msg] is added to the end of [node]'s queue
       /\ node_info' = [ node_info EXCEPT !.messages[node][chain] = checkAppend(@, msg) ]
       \* [msg] is removed from [node]'s sent set
       /\ network_info' = [ network_info EXCEPT !.sent[chain][node] = @ \ {msg} ]

\* A node with messages on some chain and room in their queue, receives a message
Receive_node ==
    \E chain \in activeChains :
        \E node \in activeNodes[chain] :
            /\ network_info.sent[chain][node] # {} \* there are [chain] messages for [node]
            /\ checkMessages[node][chain]          \* [node] has space for incoming [chain] messages
            /\ Receive_msg(node, chain)

\* [sys] receives a message on [chain]
Receive_sys_msg(chain) ==
    LET msgs == network_info.sent[chain][sys]
        in_q == network_info.sysmsgs[chain]
        msg  == Pick(msgs)
    IN \* [msg] is removed from [sys]'s sent set
       /\ network_info' = [ network_info EXCEPT
            !.sent[chain][sys] = @ \ {msg},
            !.sysmsgs[chain] = checkAppend(@, msg) ]
       /\ UNCHANGED node_info

\* [sys] receives a message on some chain
Receive_sys ==
    \A chain \in activeChains :
        /\ network_info.sent[chain][sys] # {} \* [sys] has a message to receive on [chain]
        /\ checkSysMsgs[chain]                \* [sys] has room to receive on [chain]
        /\ Receive_sys_msg(chain)             \* [sys] receives a message on [chain]

\* Receive a message
Receive == Receive_node \/ Receive_sys

\* [node] drops a [chain] message
Drop_msg(node, chain) ==
    /\ network_info' = [ network_info EXCEPT !.sent[chain][node] = @ \ {Pick(@)} ]
    /\ UNCHANGED node_info

\* A node drops a message on some chain
Drop_node ==
    \E chain \in activeChains :
        \E node \in activeNodes[chain] :
            /\ network_info.sent[chain][node] # {} \* [node] has a message to drop
            /\ Drop_msg(node, chain)               \* [node] drops a message

\* [sys] drops a message on some chain
Drop_sys ==
    \E chain \in activeChains :
        /\ network_info.sent[chain][sys] # {} \* [sys] has a message to drop
        /\ Drop_msg(sys, chain)               \* [sys] drops a message

\* Drop a message
Drop == Drop_node \/ Drop_sys

=============================================================================
