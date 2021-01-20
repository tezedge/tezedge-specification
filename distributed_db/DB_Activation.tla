--------------------------- MODULE DB_Activation ----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages
LOCAL INSTANCE Utils

(*******************************)
(* Activate/Deactivate actions *)
(*******************************)

\* [node] becomes active on [chain]
\* [node] immediately receives current system branch on [chain]
Activate(node, chain) ==
    LET msg == SysMsg("Sys_current_branch", [ branch |-> network_info.branch[chain] ])
    IN /\ network_info' = [ network_info EXCEPT !.active[chain] = @ \cup {node} ]
       /\ node_info' = [ node_info EXCEPT
            !.active[node] = @ \cup {chain},    \* [node] becomes active on [chain]
            !.messages[node][chain] = <<msg>> ] \* [node] receives current system branch

\* An inactive node on some chain becomes active
Activation ==
    \E chain \in activeChains :
        \E node \in Nodes \ activeNodes[chain] : Activate(node, chain)

\* [node] becomes inactive on [chain]
\* [node] immediately drops all [chain] messages
Deactivate(node, chain) ==
    /\ network_info' = [ network_info EXCEPT !.active[chain] = @ \ {node} ]
    /\ node_info' = [ node_info EXCEPT
         !.active[node] = @ \ {chain},    \* [node] becomes inactive on [chain]
         !.messages[node][chain] = <<>> ] \* [node] drops all [chain] messages

\* An active node on some chain becomes inactive
Deactivation ==
    \E chain \in activeChains :
        \E node \in activeNodes[chain] : Deactivate(node, chain)

=============================================================================
