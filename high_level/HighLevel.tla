----------------------------- MODULE HighLevel ------------------------------

(********************************************************************************)
(* This is a high-level model of the handshaking and bootstrapping processes    *)
(* used in the Tezos P2P layer. A node that wishes to join the network will     *)
(* request peers from the DNS and then make secure connections with established *)
(* nodes in order to download the current state of the Tezos blockchain.        *)
(* Joining nodes will only get state from established nodes they have a secure  *)
(* connection with.                                                             *)
(********************************************************************************)

EXTENDS Utils

CONSTANTS NumNodes,             \* number of established nodes
          NumJoins,             \* number of joining nodes
          ValidStates,          \* set of valid states
          peerThreshold,        \* number of peers needed before handshaking
          connectionThreshold,  \* number of connections needed before bootstrapping
          sizeBound             \* bound on size of recv, sent, and mailbox queues

(**********************************************************************************)
(* Variables:                                                                     *)
(* - state: record of each node's view of the blockchain state                    *)
(* - secured: record of tuples of nodes' sets of secure connections               *)
(* - mailbox: queue of messages sent to the given node                            *)
(* - recv: queue of messages received by the given node                           *)
(* - sent: queue of messages sent by the given node                               *)
(* - joined: set of joining nodes that have successfully joined the Tezos network *)
(* - peers: tuple of the set of peers each joining node obtains from the DNS      *)
(* - phase: tuple of the phase each joining node is in                            *)
(**********************************************************************************)

VARIABLE state
    \* state \in [ join : [ joining -> Seq(ValidStates) ], node : [ nodes -> ValidStates ] ]
    \* join : seq of states for the given joining node
    \* node : current state of the given established node

VARIABLE secured
    \* secured \in [ join : [ joining -> SUBSET nodes ], node : [ nodes -> SUBSET joining ] ]
    \* set of nodes with which the given node has a secure connection
    \* As a simplification, established nodes only connect to joining nodes.

VARIABLE mailbox
    \* mailbox \in [ join : [ joining -> Seq(NodeMsgs) ], node : [ nodes -> Seq(JoinMsgs) ] ]
    \* queue of messages sent to the given node, either deleted once they are received or dropped

VARIABLE recv
    \* recv \in [ join : [ joining -> Seq(NodeMsgs) ], node : [ nodes -> Seq(JoinMsgs) ] ]
    \* sequence of messages received by the given node, deleted as they are handled

VARIABLE sent
    \* sent \in [ join : [ joining -> Seq(PartialNodeMsgs) ], node : [ nodes -> Seq(JoinMsgs) ] ]
    \* queue of sent messages by the given node

VARIABLES joined,   \* set of joining nodes who have successfully bootstrapped
          peers,    \* set of peers for the given joining node
          phase     \* current phase of the given joining node

vars == <<state, joined, peers, phase, secured, mailbox, recv, sent>>

---------------------------------------------------------------------------------

\* peerThreshold defines the lower bound of peers required
\* connectionThreshold defines the lower bound of secure connections required
ASSUME peerThreshold \in Nat /\ peerThreshold > 0
ASSUME connectionThreshold \in Nat /\ connectionThreshold > 0
ASSUME connectionThreshold <= peerThreshold
ASSUME peerThreshold <= NumNodes
ASSUME connectionThreshold < NumNodes

LOCAL INSTANCE HL_Utils
LOCAL INSTANCE HL_Actions

TypeOK == INSTANCE HL_TypeOK
Properties == INSTANCE HL_Properties

(**************************************************************************************)
(* Initial predicate:                                                                 *)
(* - all joining nodes are in the init phase                                          *)
(* - all joining nodes have no peers                                                  *)
(* - no joining node has joined                                                       *)
(* - all joining nodes have empty state and all established nodes have a valid state  *)
(* - all joining and established nodes have no secure connections                     *)
(* - no messages have been sent                                                       *)
(* - no messages have been received                                                   *)
(* - no messages are sent                                                             *)
(**************************************************************************************)

Init ==
    \E st \in ValidStates :
    /\ phase = [ j \in joining |-> "init" ]
    /\ peers = [ j \in joining |-> {} ]
    /\ joined = {}
    /\ state =
        [ join |-> [ j \in joining |-> <<>> ]
        , node |-> [ n \in nodes   |-> st ] ]
    /\ secured =
        [ join |-> [ j \in joining |-> {} ]
        , node |-> [ n \in nodes   |-> {} ] ]
    /\ mailbox =
        [ join |-> [ j \in joining |-> <<>> ]
        , node |-> [ n \in nodes   |-> <<>> ] ]
    /\ recv =
        [ join |-> [ j \in joining |-> <<>> ]
        , node |-> [ n \in nodes   |-> <<>> ] ]
    /\ sent =
        [ join |-> [ j \in joining |-> <<>> ]
        , node |-> [ n \in nodes   |-> <<>> ] ]

---------------------------------------------------------------------------------------

(********************************************************************)
(* Next actions                                                     *)
(* *Joining nodes*                                                  *)
(* - InitRequestPeers: request peers from DNS                       *)
(* - HandshakesHappen: handshake with peers                         *)
(* - TransitionHappen: get ready to bootstrap                       *)
(* - GettingBootstrap: download state from connections(s)           *)
(* - BootstrapperJoin: join the network                             *)
(* - Receive: receive a message that was sent to them               *)
(* - Handle: react to a received message                            *)
(* - Send_again: if a message has not been responded to, send again *)
(* - Drop: a message sent to them is dropped before being received  *)
(*                                                                  *)
(* *Established nodes*                                              *)
(* - Receive: receive a message that was sent to them               *)
(* - Handle: react to a received message                            *)
(* - Advertise: send current state to bootstrapping connections     *)
(* - Send_again: if an expected message has not arrived, send again *)
(* - Drop: a message sent to them is dropped before being received  *)
(********************************************************************)

Next ==
    \/ InitRequestPeers
    \/ HandshakesHappen
    \/ TransitionHappen
    \/ GettingBootstrap
    \/ BootstrapperJoin
    \/ Handle
    \/ Receive
\*    \/ Advertise

(***********************)
(* Fairness conditions *)
(***********************)

Fairness ==
    /\ WF_peers(InitRequestPeers)
    /\ WF_secured(HandshakesHappen)
    /\ WF_phase(TransitionHappen)
    /\ WF_state(GettingBootstrap)
    /\ WF_phase(BootstrapperJoin)
    /\ SF_mailbox(Handle)
    /\ SF_recv(Receive)
\*    /\ SF_vars(Advertise)

(***********************)
(* Liveness conditions *)
(***********************)

Liveness ==
    /\ []<><<Receive>>_recv
    /\ []<><<Handle>>_mailbox

(*****************)
(* Specification *)
(*****************)

Spec == Init /\ Fairness /\ Liveness /\ [][Next]_vars

---------------------------------------------------------------------------------------

THEOREM Safety == Spec => []TypeOK!TypeOK

(* Eventually, it will always be the case that all joining nodes have joined the network *)
THEOREM Liveness1 == Spec => Properties!AllNodesHaveJoined

(* All nodes have the same state inifinitely many times *)
THEOREM Liveness2 == Spec => Properties!AllNodesHaveSameState

=============================================================================
