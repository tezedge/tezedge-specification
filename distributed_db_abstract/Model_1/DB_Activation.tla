--------------------------- MODULE DB_Activation ----------------------------

EXTENDS DB_Defs

(*******************************)
(* Activate/Deactivate actions *)
(*******************************)

\* node becomes active on [chain]
Activate( chain) ==
    /\ node_active' = node_active \cup {chain}
    /\ UNCHANGED <<blocks, branch, chains, height>>
    /\ UNCHANGED <<node_blocks, node_branches, node_headers, node_height>>

\* if node is inactive on some chain, node can become active
Activation ==
    \E chain \in activeChains :
        /\ chain \notin node_active
        /\ Activate(chain)

\* node becomes inactive on [chain]
Deactivate(chain) ==
    /\ node_active' = node_active \ {chain}
    /\ UNCHANGED <<blocks, branch, chains, height>>
    /\ UNCHANGED <<node_blocks, node_branches, node_headers, node_height>>

\* if node is inactive on some chain, node can become inactive
Deactivation ==
    \E chain \in activeChains :
        /\ chain \in node_active
        /\ Deactivate(chain)

=============================================================================
