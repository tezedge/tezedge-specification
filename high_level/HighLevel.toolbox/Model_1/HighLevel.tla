----------------------------- MODULE HighLevel ------------------------------

(********************************************************************************)
(* This is a high-level model of the handshaking and bootstrapping processes    *)
(* used in the Tezos P2P layer. A node that wishes to join the network will     *)
(* request peers from the DNS and then make secure connections with established *)
(* nodes in order to download the current state of the Tezos blockchain.        *)
(* Joining nodes will only get state from established nodes they have a secure  *)
(* connection with.                                                             *)
(* There is no notion of different chains or protocols in this model.           *)
(********************************************************************************)

EXTENDS Utils

(**************************************************************************)
(* Constants:                                                             *)
(* - NumNodes: number of nodes who are connected to the network           *)
(* - NumJoins: number of joining nodes                                    *)
(* - ValidStates: set of all valid states                                 *)
(* - peerThreshold: number of peers need before handshaking               *)
(* - connectionThreshold: number of connections need before bootstrapping *)
(* - sizeBound: bound on the size of sets and queues used in the model    *)
(**************************************************************************)

CONSTANTS NumNodes,             \* number of established nodes
          NumJoins,             \* number of joining nodes
          ValidStates,          \* set of valid states
          peerThreshold,        \* threshold of peers to exceed before handshaking
          connectionThreshold,  \* threshold of connections to exceed before
                                \* a joining node moves to the bootstrapping phase
          sizeBound             \* bound on size of recv queue, sent, and expect sets

(**********************************************************************************)
(* Variables:                                                                     *)
(* - state: record of each node's view of the blockchain state                    *)
(* - secured: record of tuples of nodes' sets of secure connections               *)
(* - sent: set of messages sent to the given node                                 *)
(* - recv: sequence of messages received by the given node                        *)
(* - expect:                *)
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
    \* join : set of nodes with which the given joining node has a secure connection
    \* node : set of nodes with which the given established node has a secure connection

VARIABLE sent
    \* sent \in [ join : [ joining -> SUBSET NodeMsgs ], node : [ nodes -> SUBSET JoinMsgs ] ]
    \* join : set of messages sent to the given joining node, deleted once they are received
    \* node : set of messages sent to the given establlished node, deleted once they are received

VARIABLE recv
    \* recv \in [ join : [ joining -> Seq(NodeMsgs) ], node : [ nodes -> Seq(JoinMsgs) ] ]
    \* join : seq of messages received by the given joining node, deleted as they are used
    \* node : seq of messages received by the given established node, deleted as they are used

VARIABLE expect
    \* expect \in [ join : [ joining -> SUBSET PartialNodeMsgs ], node : [ nodes -> SUBSET JoinMsgs ] ]
    \* join : set of expected responses to messages sent by the given joining node
    \* node : set of expected responses to messages sent by the given established node

VARIABLES joined,   \* set of joining nodes who have joined successfully
          peers,    \* set of peers for the given joining node
          phase     \* current phase of the given joining node

vars == <<state, joined, peers, phase, secured, sent, recv, expect>>

nodes == 1..NumNodes

joining == 1..NumJoins

\* peerThreshold defines the lower bound of peers required
\* connectionThreshold defines the lower bound of secure connections required
ASSUME (peerThreshold \in Nat) /\ (peerThreshold > 0)
ASSUME (connectionThreshold \in Nat) /\ (connectionThreshold > 0)
ASSUME connectionThreshold <= peerThreshold
ASSUME peerThreshold <= NumNodes
ASSUME connectionThreshold < NumNodes

(*************************************************************************************)
(* The nodes are already connected to the network and have a valid blockchain state. *)
(* They do not request state from anyone, they share their state with joining nodes. *)
(* The joining nodes represent the nodes that are joining the network.               *)
(* They must do:                                                                     *)
(*  - RequestPeers: get peers from DNS                                               *)
(*  - Handshake: once peers have been obtained, make secure connections with peers   *)
(*  - Transition: once connections have been made, start bootstrapping               *)
(*  - Bootstrap: request state from connections                                      *)
(*  - Join: once a valid state has been obtained, join the network                   *)
(*************************************************************************************)

---------------------------------------------------------------------------------------------

(* Sets - helper functions *)
\* Subsets of S which contain at least n elements
SubsetsOfSmallestSize(S, n) == { s \in SUBSET S : Cardinality(s) >= n }

\* Choose a subset of S which contains at least n elements
PickOfSize(S, n) == Pick(SubsetsOfSmallestSize(S, n))

\* S and T are disjoint
disjoint(S, T) == S \cap T = {}

(* Sequences - helper functions *)
\* Set of non-empty sequences of elements of S
NonEmptySeq(S) == Seq(S) \ {<<>>}

\* Choose a singleton sequence of Seq(S)
PickOneSeq(S) == Pick({ <<t>> : t \in ValidStates })

\* Check that the sent set is not full
check_sent(label, m) ==
    CASE label = "join" /\ m \in joining -> Cardinality(sent.join[m]) < sizeBound
      [] label = "node" /\ m \in nodes   -> Cardinality(sent.node[m]) < sizeBound

\* Check that the recv queue is not full
check_recv(label, m) ==
    CASE label = "join" /\ m \in joining -> Len(recv.join[m]) < sizeBound
      [] label = "node" /\ m \in nodes   -> Len(recv.node[m]) < sizeBound

\* Check that the expect set is not full
check_expect(label, m) ==
    CASE label = "join" /\ m \in joining -> Cardinality(expect.join[m]) < sizeBound
      [] label = "node" /\ m \in nodes   -> Cardinality(expect.node[m]) < sizeBound

\*
ok_sent(label, m) ==
    CASE label = "join" /\ m \in joining -> Cardinality(sent.join[m]) <= sizeBound
      [] label = "node" /\ m \in nodes   -> Cardinality(sent.node[m]) <= sizeBound

\*
ok_recv(label, m) ==
    CASE label = "join" /\ m \in joining -> Len(recv.join[m]) <= sizeBound
      [] label = "node" /\ m \in nodes   -> Len(recv.node[m]) <= sizeBound

\*
ok_expect(label, m) ==
    CASE label = "join" /\ m \in joining -> Cardinality(expect.join[m]) <= sizeBound
      [] label = "node" /\ m \in nodes   -> Cardinality(expect.node[m]) <= sizeBound

---------------------------------------------------------------------------------------------

(* Phases of joining nodes *)

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

hasSeenMostRecentStateFrom(j, n) == state.node[n] \in ToSet(state.join[j])

---------------------------------------------------------------------------------

(* Messages *)

Msg(from, msg) == [ from |-> from, msg |-> msg ]

\* Messages sent by joing nodes
JoinMsgTypes == { "Get_current_state", "Ack_current_state" }

JoinMsgs == [ from : joining, msg : JoinMsgTypes ]

\* Messages sent by established nodes
NodeMsgTypes == { "Current_state" }

PartialNodeMsgs == [ from : nodes, msg : NodeMsgTypes ]

NodeMsgs == [ from : nodes, msg : Pairs(NodeMsgTypes, ValidStates) ]

\* All messages
Messages == JoinMsgs \cup NodeMsgs \cup PartialNodeMsgs

---------------------------------------------------------------------------------

(***********************)
(* Handshaking Actions *)
(***********************)

(* Requesting peers from the DNS *)
(* Joining nodes in the "init" phase request peers and transition to the "handshake" phase *)
(* This step is atomic in this model *)
RequestPeers(j) ==
    /\ phase' = [ phase EXCEPT ![j] = "handshake" ]
    /\ peers' = [ peers EXCEPT ![j] = PickOfSize(nodes, peerThreshold) ]
    /\ UNCHANGED <<expect, joined, recv, secured, sent, state>>

(* Once peers have been obtained (i.e. the joining node is in the "handshake" phase *)
(* and they are peerSaturated), these joining nodes attempt to handshake with their peers *)
Handshake(j, n) ==
    /\ ~connected(j, n)
    /\ ~connectionSaturated(j)
    /\ secured' = [ secured EXCEPT !.join[j] = @ \cup {n}, !.node[n] = @ \cup {j} ]
    /\ UNCHANGED <<expect, joined, peers, phase, recv, sent, state>>

(* Once a handshaking node is connectionSaturated, they can start bootstrapping *)
Transition(j) ==
    /\ connectionSaturated(j)
    /\ phase' = [ phase EXCEPT ![j] = "bootstrap" ]
    /\ UNCHANGED <<expect, joined, peers, recv, secured, sent, state>>


(*************************)
(* Bootstrapping Actions *)
(*************************)

(* Once a joining node is bootstrapping, they can request state from their connections *)
Bootstrap(j, n) ==
    /\ connected(j, n)                          \* j and n are connected
    /\ ~hasSeenMostRecentStateFrom(j, n)        \* j has not seen the most recent state from n
    /\ check_expect("join", j)                  \* j can send a message
    /\ LET msg == Msg(j, "Get_current_state")   \* j requests the current state from n
           exp == Msg(n, "Current_state")       \* j expects to get a `Current_state` message from n
       IN
         /\ sent' =
              [ sent EXCEPT !.node[n] =
                  IF check_sent("node", n)      \* if n can receive a message
                  THEN @ \cup {msg}             \* then they do
                  ELSE @ ]                      \* else, nothing happens
         /\ expect' = [ expect EXCEPT !.join[j] = @ \cup {exp} ]
    /\ UNCHANGED <<joined, peers, phase, recv, secured, state>>

(* If a message has been sent to a node and they can receive it, they do *)
Receive_node(n) ==
    /\ check_recv("node", n)            \* the node can receive a message
    /\ sent.node[n] # {}                \* messages have been sent to the node
    /\ LET msg  == Pick(sent.node[n])
           from == msg.from
           type == msg.msg
       IN
         /\ recv' = [ recv EXCEPT !.node[n] = Append(@, msg) ]  \* append msg to the end of recv queue
         /\ sent' = [ sent EXCEPT !.node[n] = @ \ {msg} ]       \* delete msg from sent
         /\ expect' =
              [ expect EXCEPT !.node[n] =                       \* if expected, delete from expect
                  CASE type = "Ack_current_state" -> @ \ {Msg(from, type)}
                    [] OTHER -> @ ]                             \* else, do nothing
    /\ UNCHANGED <<joined, peers, phase, secured, state>>

Receive_join(j) ==
    /\ check_recv("join", j)            \* the node can receive a message
    /\ sent.join[j] # {}                \* messages have been sent to the node
    /\ LET msg == Pick(sent.join[j])
           from == msg.from
           type == msg.msg[1]
       IN
         /\ recv' = [ recv EXCEPT !.join[j] = Append(@, msg) ]  \* append msg to the end of recv queue
         /\ sent' = [ sent EXCEPT !.join[j] = @ \ {msg} ]       \* delete msg from sent
         /\ expect' =
              [ expect EXCEPT !.join[j] =                       \* if expected, delete from expect
                  CASE type = "Current_state" -> @ \ {Msg(from, type)}
                    [] OTHER -> @ ]                             \* else, do nothing
    /\ UNCHANGED <<joined, peers, phase, secured, state>>

(* Joining node incorporates state message into state *)
Handle_join(j) ==
    /\ recv.join[j] # <<>>              \* the node has received messages
    /\ check_expect("join", j)          \* the node can send a message
    /\ LET msg == Head(recv.join[j])
           st  == msg.msg[2]
       IN
         /\ state' = [ state EXCEPT !.join[j] = Append(@, st) ]
         /\ recv' = [ recv EXCEPT !.join[j] = Tail(@) ]
    /\ UNCHANGED <<expect, joined, peers, phase, secured, sent>>

(* Established node responds to a message from a joining node *)
Handle_node(n) ==
    /\ recv.node[n] # <<>>              \* the node has received messages
    /\ check_expect("node", n)          \* the node can send a message
    /\ LET msg == Head(recv.node[n])
           to  == msg.from
           req == msg.msg
           st  == state.node[n]
       IN
         /\ CASE req = "Get_current_state" -> sent' =
              [ sent EXCEPT !.join[to] =
                  CASE check_sent("join", to) -> @ \cup {Msg(n, <<"Current_state", st>>)}
                    [] OTHER -> @ ]
         /\ expect' = [ expect EXCEPT !.node[n] = @ \cup {Msg(to, "Ack_current_state")} ]
    /\ UNCHANGED <<joined, peers, phase, recv, secured, state>>

(* An established node can advertise their state to their bootstrapping connections *)
(* Since these messages are not specifically requested by the bootstrapping nodes,
   nothing is added to the established node's expect set *)
Advertise_state(n) ==
    /\ secured.node[n] \cap bootstrapping # {}
    /\ LET conns == secured.node[n] \cap bootstrapping
           msg   == Msg(n, <<"Current_state", state.node[n]>>)
       IN
         sent' = [ sent EXCEPT !.join =
             [ j \in joining |->
                 CASE /\ j \in conns
                      /\ check_sent("join", j)    \* if the intended recipient can receive a message
                      -> sent.join[j] \cup {msg}  \* then the message is sent to them
                   [] OTHER -> sent.join[j] ] ]   \* otherwise, nothing happens
    /\ UNCHANGED <<expect, joined, peers, phase, recv, secured, state>>

(* If a node is expecting a message, they can send the corresponding message again *)
Send_again_join(j) ==
    /\ expect.join[j] # {}
    /\ LET exp  == Pick(expect.join[j])
           to   == exp.from
           type == exp.msg
       IN
         CASE type = "Current_state" ->
           sent' = [ sent EXCEPT !.node[to] =
             CASE check_sent("node", to) -> @ \cup {Msg(j, "Get_current_state")}
               [] OTHER -> @ ]
    /\ UNCHANGED <<expect, joined, peers, phase, recv, secured, state>>

Send_again_node(n) ==
    /\ expect.node[n] # {}
    /\ LET exp  == Pick(expect.node[n])
           to   == exp.from
           type == exp.msg
           curr == state.node[n]
       IN
         CASE type = "Ack_current_state" ->
           sent' = [ sent EXCEPT !.join[to] =
             CASE check_sent("join", to) -> @ \cup {Msg(n, <<"Current_state", curr>>)}
               [] OTHER -> @ ]
    /\ UNCHANGED <<expect, joined, peers, phase, recv, secured, state>>

(* Messages can be dropped only before they are received *)
Drop_join(j) ==
    /\ sent.join[j] # {}
    /\ sent' = [ sent EXCEPT !.join[j] = @ \ {Pick(@)} ] \* an rbitrary message is dropped
    /\ UNCHANGED <<expect, joined, peers, phase, recv, secured, state>>

Drop_node(n) ==
    /\ sent.node[n] # {}
    /\ sent' = [ sent EXCEPT !.node[n] = @ \ {Pick(@)} ] \* an rbitrary message is dropped
    /\ UNCHANGED <<expect, joined, peers, phase, recv, secured, state>>

(* Once a joining node has sufficiently many peers and connections and *)
(* has bootstrapped state, they are ready and able to join the network *)
Join(j) ==
    /\ phase' = [ phase EXCEPT ![j] = "joined" ]
    /\ joined' = joined \union {j}
    /\ UNCHANGED <<expect, peers, recv, secured, sent, state>>

--------------------------------------------------------------------------------

(* Invariants *)

(* All init nodes have no peers. *)
(* All non-init nodes are peer saturated. *)
PeersOK ==
    /\ \A j \in init : peers[j] = {}
    /\ \A j \in handshaking \cup bootstrapping \cup joined :
        /\ peers[j] # {}
        /\ peerSaturated(j)
    /\ peers \in [ joining -> SUBSET nodes ]

(* Joining nodes can only be in one of the four specified phases: "init","handshake","bootstrap","joined". *)
(* Each joining node can be in only one phase at a time. *)
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
    /\ \A j \in joining : phase[j] = "joined" <=> j \in joined
    /\ phase \in [ joining -> PossiblePhases ]

(* Established nodes must have a valid state.                                  *)
(* Init and handshaking nodes must have an empty sequenece of states.          *)
(* Bootsrapping nodes can have an empty or non-empty sequence of valid states. *)
(* Joined nodes must have a non-empty seq of valid states.                     *)
InitHandshakeEmptyStateOK ==
    \A j \in init \cup handshaking : state.join[j] = <<>>

BootstrapStateOK ==
    \A j \in bootstrapping :
        state.join[j] # <<>> => \E n \in nodes : hasSeenMostRecentStateFrom(j, n)

JoinedStateOK ==
    \A j \in joined:
        /\ state.join[j] # <<>>
        /\ \E n \in nodes : hasSeenMostRecentStateFrom(j, n)

StateOK ==
    /\ InitHandshakeEmptyStateOK
    /\ BootstrapStateOK
    /\ JoinedStateOK
    /\ state \in [ join : [ joining -> Seq(ValidStates) ]
                 , node : [ nodes   -> ValidStates ] ]

(* Init nodes have no secure connections. *)
(* Handshaking nodes may only be connected to established nodes. *)
(* Bootstrapping and joined nodes are connection saturated to established nodes. *)
(* Established nodes must have sufficiently many connections to other established and non-init nodes. *)
SecuredJoinOK ==
    \* init
    /\ \A j \in init : secured.join[j] = {}
    \* handshaking
    /\ \A j \in handshaking : secured.join[j] \subseteq nodes
    \* bootstrapping and joined
    /\ \A j \in bootstrapping \cup joined : connectionSaturated(j)

SecuredOK ==
    /\ SecuredJoinOK
    /\ secured \in [ join : [ joining -> SUBSET nodes ]
                   , node : [ nodes   -> SUBSET (joining \ init) ] ]

SentOK ==
    /\ sent \in [ join : [ joining -> SUBSET NodeMsgs ]
                , node : [ nodes   -> SUBSET JoinMsgs ] ]
    /\ \A j \in init \cup handshaking : sent.join[j] = {}
    /\ \A j \in bootstrapping \cup joined : ok_sent("join", j)
    /\ \A n \in nodes : ok_sent("node", n)

RecvOK ==
    /\ recv \in [ join : [ joining -> Seq(NodeMsgs) ]
                , node : [ nodes   -> Seq(JoinMsgs) ] ]
    /\ \A j \in init \cup handshaking : recv.join[j] = <<>>
    /\ \A j \in bootstrapping \cup joined : ok_recv("join", j)
    /\ \A n \in nodes : ok_recv("node", n)

ExpectOK ==
    /\ expect \in [ join : [ joining -> SUBSET PartialNodeMsgs ]
                  , node : [ nodes   -> SUBSET JoinMsgs ] ]
    /\ \A j \in init \cup handshaking : expect.join[j] = {}
    /\ \A j \in bootstrapping \cup joined : ok_expect("join", j)
    /\ \A n \in nodes : ok_expect("node", n)

(* Type invariant *)
TypeOK ==
    /\ PeersOK
    /\ PhaseOK
    /\ StateOK
    /\ SecuredOK
    /\ SentOK
    /\ RecvOK
    /\ ExpectOK

---------------------------------------------------------------------------------------

(* Initial predicate *)

(**************************************************************************************)
(* Initialize the model with:                                                         *)
(* - all joining nodes are in the "init" phase                                        *)
(* - all joining nodes have no peers                                                  *)
(* - no joining node has joined                                                       *)
(* - all joining nodes have empty state and all established nodes have a valid state  *)
(* - all joining and established nodes have no secure connections                     *)
(* - no messages have been sent                                                       *)
(* - no messages have been received                                                   *)
(* - no messages are expected                                                         *)
(**************************************************************************************)
Init ==
    /\ phase = [ j \in joining |-> "init" ]
    /\ peers = [ j \in joining |-> {} ]
    /\ joined = {}
    /\ state =
        [ join |-> [ j \in joining |-> <<>> ]
        , node |-> [ n \in nodes   |-> Pick(ValidStates) ] ]
    /\ secured =
        [ join |-> [ j \in joining |-> {} ]
        , node |-> [ n \in nodes   |-> {} ] ]
    /\ sent =
        [ join |-> [ j \in joining |-> {} ]
        , node |-> [ n \in nodes   |-> {} ] ]
    /\ recv =
        [ join |-> [ j \in joining |-> <<>> ]
        , node |-> [ n \in nodes   |-> <<>> ] ]
    /\ expect =
        [ join |-> [ j \in joining |-> {} ]
        , node |-> [ n \in nodes   |-> {} ] ]

(* Next actions *)

(********************************************************************)
(* Joining nodes can:                                               *)
(* - InitRequestPeers: request peers from DNS                       *)
(* - HandshakesHappen: handshake with peers                         *)
(* - TransitionHappen: get ready to bootstrap                       *)
(* - GettingBootstrap: download state from connections(s)           *)
(* - BootstrapperJoin: join the network                             *)
(* - Receive: receive a message that was sent to them               *)
(* - Handle: react to a received message                            *)
(* - Send_again: if an expected message has not arrived, send again *)
(* - Drop: a message sent to them is dropped before being received  *)
(*                                                                  *)
(* Established nodes can:                                           *)
(* - Receive: receive a message that was sent to them               *)
(* - Handle: react to a received message                            *)
(* - Advertise: send current state to bootstrapping connections     *)
(* - Send_again: if an expected message has not arrived, send again *)
(* - Drop: a message sent to them is dropped before being received  *)
(********************************************************************)

\* An init node requests peers from the DNS
InitRequestPeers == \E j \in init : RequestPeers(j)

\* A handshaking node makes a secure connection with a peer
HandshakesHappen ==
    \E j \in handshaking :
        \E n \in peers[j] : Handshake(j, n)

\* A connectionSaturated handshaking node transitions to bootstrapping
TransitionHappen == \E j \in handshaking : Transition(j)

\* A bootstrapping node can request state from a connection
GettingBootstrap ==
    \E j \in bootstrapping :
        \E n \in secured.join[j] : Bootstrap(j, n)

\* Once a bootstrapping node has successfully bootstrapped, they can join the network
BootstrapperJoin ==
    \E j \in bootstrapping :
        /\ saturatedAndBootstrapped(j)
        /\ Join(j)

\* If a message has been sent to a node, they can receive it
Receive ==
    \/ \E j \in bootstrapping : Receive_join(j)
    \/ \E n \in nodes : Receive_node(n)

\* If a node has received a message, they can respond to it
Handle ==
    \/ \E j \in bootstrapping : Handle_join(j)
    \/ \E n \in nodes : Handle_node(n)

\* An established node can advertise their state to their connections
Advertise == \E n \in nodes : Advertise_state(n)

\* If an expected response has not been received, send original message again
Send_again ==
    \/ \E j \in bootstrapping : Send_again_join(j)
    \/ \E n \in nodes : Send_again_node(n)

\* Either an established or joining node drops a message
Drop ==
    \/ \E j \in joining : Drop_join(j)
    \/ \E n \in nodes : Drop_node(n)

\* Nothing left to do as far as this model is concerned (not a "real" deadlock)
Nothing ==
    /\ joining = joined
    /\ UNCHANGED vars

Next ==
    \/ InitRequestPeers
    \/ HandshakesHappen
    \/ TransitionHappen
    \/ GettingBootstrap
    \/ BootstrapperJoin
    \/ Handle
    \/ Receive
    \/ Advertise
    \/ Send_again
    \/ Drop
    \/ Nothing

(* Weak fairness of Next actions *)
WFairness ==
    /\ WF_vars(InitRequestPeers)
    /\ WF_vars(HandshakesHappen)
    /\ WF_vars(TransitionHappen)
    /\ WF_vars(GettingBootstrap)
    /\ WF_vars(BootstrapperJoin)
    /\ WF_vars(Handle)
    /\ WF_vars(Receive)
    /\ WF_vars(Advertise)
    /\ WF_vars(Send_again)
    /\ WF_vars(Drop)

(**********************************************)
(* Spec:                                      *)
(* - Initialized with Init                    *)
(* - WF of Next actions                       *)
(* - Next are the only non-stuttering actions *)
(**********************************************)
Spec == Init /\ WFairness /\ [][Next]_vars

------------------------------------------------------------------------

(* Invariants *)

\* Every joining node joins the network
AllNodesJoined == joining = joined

\* All nodes have the same state
AllNodesHaveSameState ==
    /\ \A j \in joined, n \in nodes : state.node[n] \in ToSet(state.join[j])
    /\ \A i, j \in joined : ToSet(state.join[i]) = ToSet(state.join[j])

(***********************************************************************)
(* Eventually all joining nodes will join the network                  *)
(* Eventually all nodes will have the same view of the blockchain      *)
(***********************************************************************)

THEOREM Safety == Spec => []TypeOK

THEOREM Liveness == Spec => <>[](AllNodesJoined /\ AllNodesHaveSameState)

=============================================================================
