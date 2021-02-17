---------------------------- MODULE DB_Receive -----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES node_active, node_blocks, node_branches, node_headers, node_height, node_incoming, node_sent,
          active, blocks, branch, chains, mailbox, height, sysmsgs

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
    LET msgs == mailbox[chain][node]
        in_q == node_incoming[node][chain]
        msg  == Head(msgs)
    IN \* [msg] is added to [node]'s incoming messages
       /\ node_incoming' = [ node_incoming EXCEPT ![node][chain] = checkAppend(@, msg) ]
       \* [msg] is removed from [node]'s sent set
       /\ mailbox' = [ mailbox EXCEPT ![chain][node] = Tail(@) ]
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches,
                      node_headers, node_height, node_sent>>

\* A node with messages on some chain and room in their queue, receives a message
Receive_node ==
    \E chain \in activeChains :
        \E node \in activeNodes[chain] :
            /\ mailbox[chain][node] /= <<>> \* there are [chain] messages for [node]
            /\ checkIncoming[node][chain]   \* [node] has space for incoming [chain] messages
            /\ Receive_msg(node, chain)

\* [sys] receives a message on [chain]
Receive_sys_msg(chain) ==
    LET msgs == mailbox[chain][sys]
        in_q == sysmsgs[chain]
        msg  == Head(msgs)
    IN \* [msg] is removed from [sys]'s sent set
       /\ mailbox' = [ mailbox EXCEPT ![chain][sys] = Tail(@) ]
       /\ sysmsgs' = [ sysmsgs EXCEPT ![chain] = checkAppend(@, msg) ]
       /\ UNCHANGED <<active, blocks, branch, chains, height>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                      node_height, node_incoming, node_sent>>

\* [sys] receives a message on some chain
Receive_sys ==
    \A chain \in activeChains :
        /\ mailbox[chain][sys] /= <<>> \* [sys] has a message to receive on [chain]
        /\ checkSysMsgs[chain]         \* [sys] has room to receive on [chain]
        /\ Receive_sys_msg(chain)      \* [sys] receives a message on [chain]

\* Receive a message
Receive == Receive_node \/ Receive_sys

\* [node] drops a [chain] message
Drop_msg(node, chain) ==
    /\ mailbox' = [ mailbox EXCEPT ![chain][node] = Tail(@) ]
    /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
    /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                   node_height, node_incoming, node_sent>>

\* A node drops a message on some chain
Drop ==
    \E chain \in activeChains :
        \E node \in SysNodes :
            /\ mailbox[chain][node] /= <<>> \* [node] has a message to drop
            /\ Drop_msg(node, chain)        \* [node] drops a message

=============================================================================
