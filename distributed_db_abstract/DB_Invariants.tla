----------------------------- MODULE DB_Invariants -----------------------------

CONSTANTS numChains, sizeBound

VARIABLES
    blocks, branch, chains, height,
    node_active, node_blocks, node_branches, node_headers, node_height

INSTANCE DB_Defs

(**************)
(* Properties *)
(**************)

\* If a node remains active on [chain], then eventually they will learn about all the blocks
\* on all the branches of [chain]
ActiveNodesEventuallySync == \A chain \in Chains :
    active[chain] ~> \A b \in branchSet[chain] : node_blocks[chain][b] = blocks[chain][b]

--------------------------------------------------------------------------------

(**************)
(* Invariants *)
(**************)

\* network_info & node_info are in agreement
ActiveAgreement == \A chain \in activeChains :
    active[chain]  =>
        \* branches
        /\ node_branches[chain] /= <<>> => current_branch[chain] <= branch[chain]
        \* blocks
        /\ \A b \in branchSet[chain] : isSubSeq(node_blocks[chain][b], blocks[chain][b])
        \* height
        /\ \A b \in branchSet[chain] : node_height[chain][b] <= height[chain][b]

================================================================================
