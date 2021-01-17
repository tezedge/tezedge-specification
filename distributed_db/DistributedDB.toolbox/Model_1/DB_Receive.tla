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
    IN
      \* [msg] is added to the end of [node]'s queue
      /\ Recv(node, chain, msg)
      \* [msg] is removed from [node]'s sent set
      /\ Consume_sent(chain, node, msg)

\* A node with messages on some chain and room in their queue, receives a message
Receive ==
    \E chain \in activeChains :
        \E node \in activeNodes[chain] :
            /\ network_info.sent[chain][node] # {} \* there are [chain] messages for [node]
            /\ checkMessages[node][chain]          \* [node] has space for incoming [chain] messages
            /\ Receive_msg(node, chain)

\* [node] drops a [chain] message
Drop_msg(node, chain) ==
    /\ network_info' = [ network_info EXCEPT !.sent[chain][node] = @ \ {Pick(@)} ]
    /\ UNCHANGED node_info

\* A node drops a message on some chain
Drop ==
    \E chain \in activeChains :
        \E node \in activeNodes[chain] :
            /\ network_info.sent[chain][node] # {} \* [node] has a message to drop
            /\ Drop_msg(node, chain)               \* [node] drops a message

\* [node] drops an offchain message
Drop_offchain_msg(node) ==
    /\ node_info' = [ node_info EXCEPT !.offchain[node] = Tail(@) ]
    /\ UNCHANGED network_info

\* A node drops an offchain message
Drop_offchain ==
    \E node \in Nodes :
        /\ node_info.offchain[node] # <<>> \* [node] has an offchain message
        /\ Drop_offchain_msg(node)         \* [node] drops an offchain message

=============================================================================
