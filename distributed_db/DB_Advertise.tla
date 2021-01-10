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

\* TODO
\* Advertise messages can serve as responses to specific requests, i.e. one recipient,
\* or they can be broadcast to all active nodes on a chain

\* A [node] advertises the current [branch] of [chain]
Ad_current_branch(node, chain) ==
    LET branch == Head(node_info.branches[node][chain])
        msg    == Msg(node, "Current_branch", [ chain |-> chain, branch |-> branch ])
    IN
      /\ network_info' = BroadcastToActive(node, chain, msg)
      /\ UNCHANGED node_info

\* An active node on some chain advertises their current branch
Advertise_branch ==
    \E chain \in 1..network_info.chains :
        \E node \in network_info.active[chain] :
            /\ node_info.branches[node][chain] # <<>> \* [node] knows about a [branch] on [chain]
            /\ Ad_current_branch(node, chain)         \* [node] advertises their current branch

\* A [node] advertises the current [head] of [branch] on [chain]
Ad_current_head(node, chain, branch) ==
    LET height == Head(node_info.blocks[node][chain][branch]).header.height
        msg    == Msg(node, "Current_head", [ chain |-> chain, branch |-> branch, height |-> height ])
    IN
        /\ network_info' = BroadcastToActive(node, chain, msg)
        /\ UNCHANGED node_info

\* An active node on some chain advertises their current head
Advertise_head ==
    \E chain \in 1..network_info.chains :
        \E branch \in 0..network_info.branch[chain],
           node \in network_info.active[chain] :
            /\ node_info.blocks[node][chain][branch] # <<>> \* [node] knows about a block on [branch] of [chain]
            /\ Ad_current_head(node, chain, branch)         \* [node] advertises their current head

\* [node] must have a block on [chain] [branch] in order to advertise
\* Headers in node_info.headers are NOT advertised because "they have not been validated yet"
Ad_current_header(node, chain, branch) ==
    LET header == Head(node_info.blocks[node][chain][branch]).header
        msg    == Msg(node, "Current_header", [ chain |-> chain, branch |-> branch, header |-> header ])
    IN
        /\ network_info' = BroadcastToActive(node, chain, msg)
        /\ UNCHANGED node_info

\* An active node on some chain advertises their current header
Advertise_header ==
    \E chain \in 1..network_info.chains :
        \E branch \in 0..network_info.branch[chain],
           node \in network_info.active[chain] :
            /\ node_info.blocks[node][chain][branch] # <<>> \* [node] knows about a block on [branch] of [chain]
            /\ Ad_current_header(node, chain, branch)       \* [node] advertises their current header

=============================================================================
