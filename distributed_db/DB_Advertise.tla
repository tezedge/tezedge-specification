--------------------------- MODULE DB_Advertise ----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

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

\* [node] advertises their current [branch] of [chain]
Ad_current_branch(node, chain) ==
    LET branch == Head(node_info.branches[node][chain])
        msg    == [ type |-> "Current_branch", params |-> [ branch |-> branch ] ]
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain] = BroadcastNodes(@, node, chain, msg) ]
       /\ UNCHANGED node_info

\* An active node on some chain advertises their current branch
Advertise_branch ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            /\ branchSet[from, chain] # {}      \* [from] knows about a [branch] on [chain]
            /\ activeNodes[chain] \ {from} # {} \* there are other active nodes on [chain] besides [sys]
            /\ Ad_current_branch(from, chain)   \* [from] advertises their current branch

\* [sys] advertises the current [branch] of [chain]
Ad_sys_current_branch(chain) ==
    LET branch == network_info.branch[chain]
        msg    == [ type |-> "Current_branch", params |-> [ branch |-> branch ] ]
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain] = Broadcast(@, sys, chain, msg) ]
       /\ UNCHANGED node_info

\* [sys] advertises the current branch of some chain
Advertise_sys_branch ==
    \E chain \in activeChains :
        /\ activeNodes[chain] # {}      \* there are active nodes on [chain]
        /\ Ad_sys_current_branch(chain) \* [sys] advertises current branch

\* [node] advertises their current [head] of [branch] on [chain]
Ad_current_head(node, chain, branch) ==
    LET height == Head(node_info.blocks[node][chain][branch]).header.height
        msg    == [ type |-> "Current_head", params |-> [ branch |-> branch, height |-> height ] ]
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain] = BroadcastNodes(@, node, chain, msg) ]
       /\ UNCHANGED node_info

\* An active node on some chain advertises their current head
Advertise_head ==
    \E chain \in activeChains :
        \E branch \in activeBranches[chain],
           from \in activeNodes[chain] :
             /\ current_height[from, chain, branch] >= 0 \* [node] knows about a block on [branch] of [chain]
             /\ activeNodes[chain] \ {from} # {}         \* there are other active nodes on [chain]
             /\ Ad_current_head(from, chain, branch)     \* [node] advertises their current head

\* [sys] advertises the current [head] of [branch] on [chain]
Ad_sys_current_head(chain, branch) ==
    LET height == network_info.height[chain][branch]
        msg    == [ type |-> "Current_head", params |-> [ branch |-> branch, height |-> height ] ]
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain] = Broadcast(@, sys, chain, msg) ]
       /\ UNCHANGED node_info

\* [sys] advertises the current head of some branch on some chain
Advertise_sys_head ==
    \E chain \in activeChains :
        \E branch \in activeBranches[chain] :
           /\ network_info.height[chain][branch] >= 0 \* there is a block on [branch] of [chain]
           /\ activeNodes[chain] # {}                 \* there are active nodes on [chain]
           /\ Ad_sys_current_head(chain, branch)      \* [sys] advertises current head

=============================================================================
