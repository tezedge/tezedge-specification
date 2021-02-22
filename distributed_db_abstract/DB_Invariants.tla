----------------------------- MODULE DB_Invariants -----------------------------

EXTENDS DB_Defs

(**************)
(* Properties *)
(**************)

\* If node remains active on [chain], then eventually they will learn about all the blocks
\* on all the branches of [chain]
EventuallySyncs(chain) == <>[](\A b \in Branches : node_blocks[chain][b] = blocks[chain][b])

--------------------------------------------------------------------------------

(**************)
(* Invariants *)
(**************)

\* network and node are in agreement
Agreement == \A chain \in activeChains :
    \* branches
    /\ node_branches[chain] /= <<>> => current_branch[chain] <= branch[chain]
    \* blocks
    /\ \A b \in branchSet[chain] : isSubSeq(node_blocks[chain][b], blocks[chain][b])
    \* height
    /\ \A b \in branchSet[chain] : node_height[chain][b] <= height[chain][b]

================================================================================
