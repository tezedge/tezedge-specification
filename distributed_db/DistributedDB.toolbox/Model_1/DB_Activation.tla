--------------------------- MODULE DB_Activation ----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES node_active, node_blocks, node_branches, node_headers, node_height, node_incoming, node_sent,
          active, blocks, branch, chains, mailbox, height, sysmsgs

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages
LOCAL INSTANCE Utils

----------------------------------------------------------------------------

(*******************************)
(* Activate/Deactivate actions *)
(*******************************)

\* [node] becomes active on [chain]
\* [node] immediately receives current system branch on [chain]
Activate(node, chain) ==
    LET welcome_msg == Msg(sys, node, "Current_branch", [ branch |-> branch[chain] ])
    IN /\ active' = [ active EXCEPT ![chain] = @ \cup {node} ]
       /\ Send(sys, chain, welcome_msg)
       /\ node_active' = [ node_active EXCEPT ![node] = @ \cup {chain} ]
       /\ UNCHANGED <<blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_blocks, node_branches, node_headers,
                      node_height, node_incoming, node_sent>>

\* An inactive node on some chain becomes active
Activation ==
    \E chain \in activeChains :
        \E node \in inactiveNodes[chain] : Activate(node, chain)

\* [node] becomes inactive on [chain]
\* [node] immediately drops all [chain] messages
Deactivate(node, chain) ==
    /\ active' = [ active EXCEPT ![chain] = @ \ {node} ]
    /\ node_active' = [ node_active EXCEPT ![node] = @ \ {chain} ]
    /\ UNCHANGED <<blocks, branch, chains, mailbox, height, sysmsgs>>
    /\ UNCHANGED <<node_blocks, node_branches, node_headers,
                   node_height, node_incoming, node_sent>>

\* An active node on some chain becomes inactive
Deactivation ==
    \E chain \in activeChains :
        \E node \in activeNodes[chain] : Deactivate(node, chain)

=============================================================================
