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

\* A [node] advertises the current [branch] of [chain]
Ad_current_branch(node, chain) ==
    LET branch == Head(node_info.branches[node][chain])
        msg    == Msg(node, "Current_branch", [ chain |-> chain, branch |-> branch ])
    IN
      /\ BroadcastToActive(node, chain, msg)
      /\ UNCHANGED node_info

\* An active node on some chain advertises their current branch
Advertise_branch ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            /\ node_info.branches[from][chain] # <<>> \* [from] knows about a [branch] on [chain]
            /\ activeNodes[chain] \ {from} # {}       \* there are other active nodes on [chain]
            /\ Ad_current_branch(from, chain)         \* [from] advertises their current branch

\* A [node] advertises the current [head] of [branch] on [chain]
Ad_current_head(node, chain, branch) ==
    LET height == Head(node_info.blocks[node][chain][branch]).header.height
        msg    == Msg(node, "Current_head", [ chain |-> chain, branch |-> branch, height |-> height ])
    IN
        /\ BroadcastToActive(node, chain, msg)
        /\ UNCHANGED node_info

\* An active node on some chain advertises their current head
Advertise_head ==
    \E chain \in activeChains :
        \E branch \in activeBranches[chain],
           from \in activeNodes[chain] :
            /\ node_info.blocks[from][chain][branch] # <<>> \* [node] knows about a block on [branch] of [chain]
            /\ activeNodes[chain] \ {from} # {}             \* there are other active nodes on [chain]
            /\ Ad_current_head(from, chain, branch)         \* [node] advertises their current head

=============================================================================
