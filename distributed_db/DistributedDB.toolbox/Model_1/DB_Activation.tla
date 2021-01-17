--------------------------- MODULE DB_Activation ----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE Utils

(*******************************)
(* Activate/Deactivate actions *)
(*******************************)

\* An inactive [node] becomes active on [chain]
Activate(node, chain) ==
    /\ network_info' = [ network_info EXCEPT !.active[chain] = @ \cup {node} ]
    /\ node_info' = [ node_info EXCEPT !.active[node] = @ \cup {chain} ]

\* An inactive node on some chain becomes active
Activation ==
    \E chain \in activeChains :
        \E node \in Nodes \ activeNodes[chain] : Activate(node, chain)

\* An active node becomes inactive on given chain
Deactivate(node, chain) ==
    /\ network_info' = [ network_info EXCEPT !.active[chain] = @ \ {node} ]
    /\ node_info' = [ node_info EXCEPT !.active[node] = @ \ {chain} ]

\* An active node on some chain becomes inactive
Deactivation ==
    \E chain \in activeChains :
        \E node \in activeNodes[chain] : Deactivate(node, chain)

=============================================================================
