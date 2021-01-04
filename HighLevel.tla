----------------------------- MODULE HighLevel ------------------------------

(********************************************************************************)
(* This is high-level model of the handshaking and bootstrapping processes      *)
(* used in the Tezos P2P layer. A node that wishes to join the network will     *)
(* request peers from the DNS and then make secure connections with established *)
(* nodes in order to download the current state of the Tezos blockchain.        *)
(* Joining nodes will only get state from established nodes they have a secure  *)
(* connection with.                                                             *)
(********************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS nodes, ValidStates, joining, peerThreshold, connectionThreshold

(**************************************************************************)
(* Constants:                                                             *)
(* - nodes: set of nodes who are connected to the network                 *)
(* - ValidStates: set of all valid states                                 *)
(* - joining: set of nodes who want to join the network                   *)
(* - peerThreshold: number of peers need before handshaking               *)
(* - connectionThreshold: number of connections need before bootstrapping *)
(**************************************************************************)

VARIABLES state, joined, peers, phase, secured

vars == <<state, joined, peers, phase, secured>>

\* peerThreshold defines the lower bound of peers required
\* connectionThreshold defines the lower bound of secure connections required
ASSUME (peerThreshold \in Nat) /\ (peerThreshold > 0)
ASSUME (connectionThreshold \in Nat) /\ (connectionThreshold > 0)
ASSUME connectionThreshold <= peerThreshold

(**********************************************************************************)
(* Variables:                                                                     *)
(* - state: record of each node's view of the blockchain state                    *)
(* - joined: set of nodes joining that have successfully joined the Tezos network *)
(* - peers: tuple of the set of peers each joining node obtains from the DNS      *)
(* - phase: tuple of the phase each node is in                                    *)
(* - secured: record of tuples of nodes' sets of secure connections               *)
(**********************************************************************************)

(*************************************************************************************)
(* The nodes are already connected to the network and have a valid blockchain state. *)
(* The joining set represents nodes that are joining the network. They must do:      *)
(*  - Init: get peers from DNS                                                       *)
(*  - Handshake: once peers have been obtained, make secure connections with peers   *)
(*  - Bootstrap: once connections have been made, request state from these peers     *)
(*  - Join: once a valid state has been obtained, join the network                   *)
(*************************************************************************************)

---------------------------------------------------------------------------------------------

(* Sets - helper functions *)
\* Choose an element in the set S
Pick(S) == CHOOSE s \in S : TRUE

\* Subsets of S which contain at least n elements
SubsetsOfSmallestSize(S, n) == { s \in SUBSET S : Cardinality(s) >= n }

\* Choose a subset of S which contains at least n elements
PickOfSize(S, n) == CHOOSE s \in SubsetsOfSmallestSize(S, n) : TRUE

\* S and T are disjoint
disjoint(S, T) == S \cap T = {}

(* Sequences - helper functions *)
\* Set of non-empty sequences of elements of S
NonEmptySeq(S) == Seq(S) \ {<<>>}

\* Set of elements in the sequence s
ToSet(s) == { s[i] : i \in DOMAIN s }

\* Choose a singleton sequence of Seq(S)
PickOneSeq(S) == Pick({ <<t>> : t \in ValidStates })

---------------------------------------------------------------------------------------------

(* Phases *)

(* Joining nodes in init only request peers from DNS. *)
(* Joining nodes in handshaking only attempt to make connections with peers (established nodes). *)
(* Handshaking nodes are peerSaturated. *)
(* Joining nodes in bootstrapping only request state from connected established nodes. *)
(* Bootstrapping nodes are peerSaturated and connectionSaturated. *)

init == { j \in joining : phase[j] = "init" }

handshaking == { j \in joining : phase[j] = "handshake" }

bootstrapping == { j \in joining : phase[j] = "bootstrap" }

PossiblePhases == { "init", "handshake", "bootstrap", "joined" }

(* Peers *)
peerSaturated(j) == Cardinality(peers[j]) >= peerThreshold

connected(j, n) ==
    /\ n \in secured.join[j]
    /\ j \in secured.node[n]

connections(j) == { n \in nodes : connected(j, n) }

connectionSaturated(j) == Cardinality(connections(j)) >= connectionThreshold

connectionSaturatedFrom(n, S) == Cardinality(secured.node[n]) >= connectionThreshold

saturatedAndBootstrapped(j) ==
    /\ j \in bootstrapping
    /\ peerSaturated(j)
    /\ connectionSaturated(j)
    /\ state.join[j] # <<>>

hasSeenMostRecentStateFrom(j, n) == Head(state.node[n]) \in ToSet(state.join[j])

--------------------------------------------------------------------------------

(* Invariants *)

(* All init nodes have no peers. *)
(* All non-init nodes are peer saturated. *)
PeersOK ==
    /\ \A j \in init: peers[j] = {}
    /\ \A j \in handshaking \cup bootstrapping \cup joined:
        /\ peers[j] # {}
        /\ peerSaturated(j)
    /\ peers \in [ joining -> SUBSET nodes ]

(* Joining nodes can only be in one of the four specified phases: "init","handshake","bootstrap","joined". *)
(* Each joining node can be in only one phase at a time. *)
MutuallyDisjointPhases ==
    /\ disjoint(init, handshaking)
    /\ disjoint(init, bootstrapping)
    /\ disjoint(init, joined)
    /\ disjoint(handshaking, bootstrapping)
    /\ disjoint(handshaking, joined)
    /\ disjoint(bootstrapping, joined)

PhaseOK ==
    /\ joining = init \cup handshaking \cup bootstrapping \cup joined
    /\ MutuallyDisjointPhases
    /\ \A j \in joining: phase[j] = "joined" <=> j \in joined
    /\ phase \in [ joining -> PossiblePhases ]

(* Established and joining nodes must have a seq of valid states. *)
(* Established and joined nodes must have a non-empty seq of valid states. *)
(* Init and handshaking nodes must have an empty seq of states. *)
InitHandshakeEmptyStateOK ==
    \A j \in init \cup handshaking: state.join[j] = <<>>

BootstrapStateOK ==
    \A j \in bootstrapping:
        state.join[j] # <<>> => \E n \in nodes: hasSeenMostRecentStateFrom(j, n)

JoinedStateOK ==
    \A j \in joined:
        /\ state.join[j] # <<>>
        /\ \E n \in nodes: hasSeenMostRecentStateFrom(j, n)

StateOK ==
    /\ InitHandshakeEmptyStateOK
    /\ BootstrapStateOK
    /\ JoinedStateOK
    /\ state \in [ join: [ joining -> Seq(ValidStates)]
                 , node: [ nodes -> NonEmptySeq(ValidStates) ] ]

(* Established nodes must have sufficiently many connections to other established and non-init nodes. *)
(* Bootstrapping and joined nodes are connection saturated. *)
SecuredJoinOK ==
    /\ \A j \in init: secured.join[j] = {}
    /\ \A j \in handshaking: secured.join[j] \subseteq nodes
    /\ \A j \in bootstrapping \cup joined:
        /\ secured.join[j] # {}
        /\ connectionSaturated(j)

SecuredNodeOK ==
    \A n \in nodes:
        /\ secured.node[n] # {}
        /\ connectionSaturatedFrom(n, (nodes \ {n}) \cup (joining \ init))

SecuredOK ==
    /\ SecuredJoinOK
    /\ SecuredNodeOK
    /\ secured \in [ join: [ joining -> SUBSET nodes ]
                   , node: [ nodes -> SUBSET (nodes \cup (joining \ init)) ] ]

(* Type invariant *)
TypeOK ==
    /\ PeersOK
    /\ PhaseOK
    /\ StateOK
    /\ SecuredOK

---------------------------------------------------------------------------------

(* Actions *)

(* Requesting peers from the DNS *)
(* Joining nodes in the "init" phase request peers and transition to the "handshake" phase *)
RequestPeers(j) ==
    /\ j \in init
    /\ phase' = [phase EXCEPT ![j] = "handshake"]
    /\ peers' = [peers EXCEPT ![j] = PickOfSize(nodes, peerThreshold)]
    /\ UNCHANGED << state, joined, secured >>

(* Once peers have been obtained (i.e. the joining node is in the "handshake" phase and they are peerSaturated), *)
(* these joining nodes attempt to handshake with their peers *)
Handshake(j, n) ==
    /\ j \in handshaking
    /\ n \in peers[j]
    /\ ~connected(j, n)
    /\ ~connectionSaturated(j)
    /\ secured' = [secured EXCEPT !.join[j] = @ \cup {n}, !.node[n] = @ \cup {j}]
    /\ UNCHANGED << state, joined, peers, phase >>

(* Once a handshaking node is connectionSaturated, they start bootstrapping *)
Transition(j) ==
    /\ j \in handshaking
    /\ connectionSaturated(j)
    /\ phase' = [phase EXCEPT ![j] = "bootstrap"]
    /\ UNCHANGED << state, joined, peers, secured >>

(* Once a joining node is bootstrapping, they can request state from their connections *)
Bootstrap(j, n) ==
    /\ j \in bootstrapping
    /\ connected(j, n)
    /\ ~hasSeenMostRecentStateFrom(j, n)
    /\ state' = [state EXCEPT !.join[j] = state.node[n] \o @]
    /\ UNCHANGED << joined, peers, phase, secured >>

(* Once a joining node has sufficiently many peers and connections and has bootstrapped state, *)
(* they are ready and able to join the network *)
Join(j) ==
    /\ saturatedAndBootstrapped(j)
    /\ phase' = [phase EXCEPT ![j] = "joined"]
    /\ joined' = joined \union {j}
    /\ UNCHANGED << state, peers, secured >>

-------------------------------------------------------------------------------------------------------------

(* Spec *)

(***************************************************************************************************)
(* Initialize the model with:                                                                      *)
(* - all joining nodes are in the "init" phase                                                     *)
(* - all joining nodes have no peers                                                               *)
(* - no joining node has joined                                                                    *)
(* - all joining nodes have empty state and all established nodes have a valid state               *)
(* - all joining nodes have no secure connections and all established nodes have sufficiently many *)
(*   connections to other established nodes                                                        *)
(***************************************************************************************************)
Init ==
    /\ phase = [ j \in joining |-> "init" ]
    /\ peers = [ j \in joining |-> {} ]
    /\ joined = {}
    /\ state =
        [ join |-> [ j \in joining |-> <<>> ]
        , node |-> LET start == PickOneSeq(ValidStates) IN [ n \in nodes |-> start ] ]
    /\ secured =
        [ join |-> [ j \in joining |-> {} ]
        , node |-> [ n \in nodes |-> PickOfSize(nodes \ {n}, connectionThreshold) ] ]
    /\ TypeOK

(* Next actions *)

(*********************************************************************)
(* Joining nodes can:                                                *)
(* - InitRequestPeers: request peers from DNS                        *)
(* - HandshakesHappen: handshake with peers                          *)
(* - TransitionHappen: get ready to bootstrap                        *)
(* - GettingBootstrap: download state from peer(s)                   *)
(* - BootstrapperJoin: join the network                              *)
(*********************************************************************)

InitRequestPeers == \E j \in init: RequestPeers(j)

HandshakesHappen == \E j \in handshaking: \E n \in peers[j]: Handshake(j, n)

TransitionHappen == \E j \in handshaking: Transition(j)

GettingBootstrap == \E j \in bootstrapping: \E n \in peers[j]: Bootstrap(j, n)

BootstrapperJoin == \E j \in bootstrapping: Join(j)

Next ==
    \/ InitRequestPeers
    \/ HandshakesHappen
    \/ TransitionHappen
    \/ GettingBootstrap
    \/ BootstrapperJoin

(* Weak fairness of Next actions *)
WFairness ==
    /\ WF_vars(InitRequestPeers)
    /\ WF_vars(HandshakesHappen)
    /\ WF_vars(TransitionHappen)
    /\ WF_vars(GettingBootstrap)
    /\ WF_vars(BootstrapperJoin)

(**********************************************)
(* Spec:                                      *)
(* - Initialized with Init                    *)
(* - WF of Next actions                       *)
(* - Next are the only non-stuttering actions *)
(**********************************************)
Spec == Init /\ WFairness /\ [][Next]_vars

------------------------------------------------------------------------

(* Properties & Theorems *)

(* Properties *)
\* Every joining node joins the network
AllNodesJoined == joining = joined

\* All nodes have the same state
AllNodesHaveSameState ==
    /\ \A j \in joining: \A n \in nodes: state.join[j] = state.node[n]
    /\ \A i,j \in joining: state.join[i] = state.join[j]
    /\ \A m,n \in nodes: state.node[m] = state.node[n]

(***********************************************************************)
(* Eventually all joining nodes will join the network                  *)
(* Eventually all nodes will have the same view of the blockchain      *)
(***********************************************************************)

THEOREM Safety == Spec => []TypeOK

THEOREM Liveness == Spec => <>[](AllNodesJoined /\ AllNodesHaveSameState)

=============================================================================
