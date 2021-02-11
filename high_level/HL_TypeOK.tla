------------------------------- MODULE HL_TypeOK -------------------------------

CONSTANTS NumNodes, NumJoins, ValidStates, peerThreshold, connectionThreshold, sizeBound

VARIABLES state, secured, mailbox, recv, sent, joined, peers, phase

LOCAL INSTANCE HL_Utils

(***************************************)
(* Type Invariants & Safety Properties *)
(***************************************)

ok(var) ==
    /\ DOMAIN var = { "join", "node" }
    /\ DOMAIN var.join = joining
    /\ DOMAIN var.node = nodes

(*************************************************)
(* All init joining nodes have no peers.         *)
(* All non-init joining nodes are peerSaturated. *)
(* Only established nodes can be peers.          *)
(*************************************************)

PeersOK ==
    /\ DOMAIN peers = joining
    /\ \A j \in init : peers[j] = {}
    /\ \A j \in handshaking \cup bootstrapping \cup joined : peerSaturated(j)
    /\ \A j \in joining : peers[j] \subseteq nodes

\* Joining nodes can be in one and only one of the four specified phases at a time.
PhasePartition ==
    /\ disjoint(init, handshaking)
    /\ disjoint(init, bootstrapping)
    /\ disjoint(init, joined)
    /\ disjoint(handshaking, bootstrapping)
    /\ disjoint(handshaking, joined)
    /\ disjoint(bootstrapping, joined)
    /\ joining = init \cup handshaking \cup bootstrapping \cup joined

PhaseOK ==
    /\ PhasePartition
    /\ DOMAIN phase = joining
    /\ \A j \in joining : phase[j] = "joined" <=> j \in joined
    /\ \A j \in joining : phase[j] \in PossiblePhases

(**********************************************************************)
(* Established nodes have a valid state.                              *)
(* Init and handshaking nodes must have an empty sequenece of states. *)
(* Bootsrapping nodes may only get states from established nodes.     *)
(* Joined nodes must have gotten states from established nodes.       *)
(**********************************************************************)

InitHandshakeEmptyStateOK ==
    \A j \in init \cup handshaking : state.join[j] = <<>>

BootstrapStateOK ==
    \A j \in bootstrapping :
        state.join[j] /= <<>> => \E n \in nodes : hasSeenMostRecentStateFrom(j, n)

JoinedStateOK ==
    \A j \in joined:
        /\ state.join[j] /= <<>>
        /\ \E n \in nodes : hasSeenMostRecentStateFrom(j, n)

StateOK ==
    /\ ok(state)
    /\ InitHandshakeEmptyStateOK
    /\ BootstrapStateOK
    /\ JoinedStateOK
    /\ \A j \in joining :
         /\ Len(state.join[j]) <= sizeBound
         /\ Forall(state.join[j], isValidState)
    /\ \A n \in nodes : state.node[n] \in ValidStates

(**********************************************************************)
(* Joining nodes only make connections with established nodes.        *)
(* Init nodes have no connections.                                    *)
(* Handshaking nodes may be connected to established nodes.           *)
(* Bootstrapping and joined nodes are connection saturated.           *)
(* Established nodes may only be connected to non-init joining nodes. *)
(**********************************************************************)

SecuredJoinOK ==
    /\ \A j \in init : secured.join[j] = {}
    /\ \A j \in handshaking : secured.join[j] \subseteq nodes
    /\ \A j \in bootstrapping \cup joined : connectionSaturated(j)
    /\ \A j \in joining : secured.join[j] \subseteq nodes

SecuredOK ==
    /\ ok(secured)
    /\ SecuredJoinOK
    /\ \A n \in nodes : secured.node[n] \subseteq (joining \ init)

(************************************************************************************)
(* Init and handshaking nodes cannot have messages sent to them.                    *)
(* Bootstrapping and joined nodes can have at most sizeBound messages sent to them. *)
(* Established nodes can have at most sizeBound messages sent to them.              *)
(* Joining nodes only send messages to established nodes and vice versa.            *)
(************************************************************************************)

MailboxOK ==
    /\ ok(mailbox)
    /\ \A j \in init \cup handshaking : mailbox.join[j] = <<>>
    /\ \A j \in bootstrapping \cup joined : ok_mailbox(TRUE, j)
    /\ \A n \in nodes : ok_mailbox(FALSE, n)

(************************************************************************************************)
(* Init and handshaking nodes cannot receive any messages (because no one sends them messages). *)
(* Bootstrapping and joined nodes can receive at most sizeBound messages.                       *)
(* Established nodes can receive at most sizeBound messages.                                    *)
(* Joining nodes can only receive messages from established nodes and vice versa.               *)
(************************************************************************************************)

RecvOK ==
    /\ ok(recv)
    /\ \A j \in init \cup handshaking : recv.join[j] = <<>>
    /\ \A j \in bootstrapping \cup joined : ok_recv(TRUE, j)
    /\ \A n \in nodes : ok_recv(FALSE, n)

(**********************************************************************************************)
(* Init and handshaking nodes do not expect any messages (because they cannot send messages). *)
(* Bootstrapping and joined nodes can expect at most sizeBound messages.                      *)
(* Established nodes can expect at most sizeBound messages.                                   *)
(* Joining nodes can only expect (partial) messages from established nodes and vice versa.    *)
(**********************************************************************************************)

SentOK ==
    /\ ok(sent)
    /\ \A j \in init \cup handshaking : sent.join[j] = <<>>
    /\ \A j \in bootstrapping \cup joined : ok_sent(TRUE, j)
    /\ \A n \in nodes : ok_sent(FALSE, n)

\* full type invariant
TypeOK ==
    /\ PeersOK
    /\ PhaseOK
    /\ StateOK
    /\ SecuredOK
    /\ MailboxOK
    /\ RecvOK
    /\ SentOK

================================================================================
