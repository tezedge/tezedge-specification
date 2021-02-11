--------------------------- MODULE DB_Advertise ----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES node_active, node_blocks, node_branches, node_headers, node_height, node_incoming, node_sent,
          active, blocks, branch, chains, mailbox, height, sysmsgs

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages
LOCAL INSTANCE Utils

----------------------------------------------------------------------------

(*********************)
(* Advertise actions *)
(*********************)

(* Advertise messages are explicitly passed between nodes *)

\* Advertise messages can serve as responses to specific requests, i.e. one recipient,
\* or they can be broadcast to all active nodes on a chain

\* [node] advertises their current branch of [chain]
Ad_current_branch(node, chain) ==
    LET b   == Head(node_branches[node][chain])
        msg == PartialMsg("Current_branch", [ branch |-> b ])
    IN /\ mailbox' = [ mailbox EXCEPT ![chain] = BroadcastNodes(@, node, chain, msg) ]
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                      node_height, node_incoming, node_sent>>

\* An active node on some chain advertises their current branch
Ad_node_branch ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            /\ branchSet[from, chain] /= {}      \* [from] knows about a branch on [chain]
            /\ activeNodes[chain] \ {from} /= {} \* there are other active nodes on [chain] besides [sys]
            /\ Ad_current_branch(from, chain)    \* [from] advertises their current branch

\* [sys] advertises the current branch [b] of [chain]
Ad_sys_current_branch(chain) ==
    LET b   == branch[chain]
        msg == PartialMsg("Current_branch", [ branch |-> b ])
    IN /\ mailbox' = [ mailbox EXCEPT ![chain] = Broadcast(@, sys, chain, msg) ]
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                      node_height, node_incoming, node_sent>>

\* [sys] advertises the current branch of some chain
Ad_sys_branch ==
    \E chain \in activeChains :
        /\ activeNodes[chain] /= {}     \* there are active nodes on [chain]
        /\ Ad_sys_current_branch(chain) \* [sys] advertises current branch

Advertise_branch == Ad_node_branch \/ Ad_sys_branch

\* [node] advertises their current head of branch [b] on [chain]
Ad_current_head(node, chain, b) ==
    LET h   == Head(node_blocks[node][chain][b]).header.height
        msg == PartialMsg("Current_head", [ branch |-> b, height |-> h ])
    IN /\ mailbox' = [ mailbox EXCEPT ![chain] = BroadcastNodes(@, node, chain, msg) ]
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                      node_height, node_incoming, node_sent>>

\* An active node on some chain advertises their current head
Ad_node_head ==
    \E chain \in activeChains :
        \E b \in activeBranches[chain],
           from \in activeNodes[chain] :
             /\ current_height[from, chain, b] >= 0 \* [node] knows about a block on branch [b] of [chain]
             /\ activeNodes[chain] \ {from} /= {}   \* there are other active nodes on [chain]
             /\ Ad_current_head(from, chain, b)     \* [node] advertises their current head

\* [sys] advertises the current [head] of branch [b] on [chain]
Ad_sys_current_head(chain, b) ==
    LET h   == height[chain][b]
        msg == PartialMsg("Current_head", [ branch |-> b, height |-> h ])
    IN /\ mailbox' = [ mailbox EXCEPT ![chain] = Broadcast(@, sys, chain, msg) ]
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                      node_height, node_incoming, node_sent>>

\* [sys] advertises the current head of some branch on some chain
Ad_sys_head ==
    \E chain \in activeChains :
        \E b \in activeBranches[chain] :
           /\ height[chain][b] >= 0         \* there is a block on branch [b] of [chain]
           /\ activeNodes[chain] /= {}      \* there are active nodes on [chain]
           /\ Ad_sys_current_head(chain, b) \* [sys] advertises current head

Advertise_head == Ad_node_head \/ Ad_sys_head

=============================================================================
