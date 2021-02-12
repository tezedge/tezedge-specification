----------------------------- MODULE HL_Properties -----------------------------

CONSTANTS NumNodes, NumJoins, ValidStates, peerThreshold, connectionThreshold, sizeBound

VARIABLES state, secured, mailbox, recv, sent, joined, peers, phase

INSTANCE HL_Utils

(***********************)
(* Liveness properties *)
(***********************)

\* Every joining node joins the network
AllNodesJoined == joining = joined

AllNodesHaveJoined == <>[]AllNodesJoined

\* All nodes have the same state
AllNodesSameState ==
    /\ \A j \in joined, n \in nodes : state.node[n] \in ToSet(state.join[j])
    /\ \A i, j \in joined : ToSet(state.join[i]) = ToSet(state.join[j])

AllNodesHaveSameState == []<>AllNodesSameState

================================================================================
