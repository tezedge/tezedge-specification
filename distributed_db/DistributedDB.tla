--------------------------- MODULE DistributedDB ---------------------------

EXTENDS Utils

CONSTANTS numNodes,   \* number of nodes
          numChains,  \* number of chains
          sizeBound   \* bound on many things

VARIABLE node_info
    \* active   : [ Nodes -> SUBSET Chains ]
    \* blocks   : [ Nodes -> [ Chains -> [ Branches -> Seq(Blocks) ] ] ]
    \* branches : [ Nodes -> [ Chains -> Seq(Branches) ] ]
    \* expect   : [ Nodes -> [ Chains -> SUBSET Messages ] ]
    \* headers  : [ Nodes -> [ Chains -> [ Branches -> SUBSET Headers ] ] ]
    \* messages : [ Nodes -> [ Chains -> Seq(Messages) ] ]
    \* offchain : [ Nodes -> Seq(SysMsgs) ]

VARIABLE network_info
    \* active : [ Chains -> SUBSET Nodes ]
    \* blocks : [ Chains -> [ Branches -> Seq(Blocks) ] ]
    \* branch : [ Chains -> Branches ]
    \* chains : Chains
    \* height : [ Chains -> [ Branches -> Heights ] ]
    \* recv   : [ Chains -> [ Nodes -> Seq(Messages) ] ]
    \* sent   : [ Chains -> [ Nodes -> SUBSET Messages ] ]

vars == <<network_info, node_info>>

----------------------------------------------------------------------------

LOCAL INSTANCE DB_Activation   \* Activation and Deactivation actions
LOCAL INSTANCE DB_Advertise    \* Advertisement actions
LOCAL INSTANCE DB_Defs         \* ubiquitous definitions
LOCAL INSTANCE DB_Handle       \* Message handling actions
LOCAL INSTANCE DB_Maintenance  \* Block production, new chain, new branch actions
LOCAL INSTANCE DB_Messages     \* Message constructors, functions, actions
LOCAL INSTANCE DB_Receive      \* Receive and drop actions
LOCAL INSTANCE DB_Request      \* Request actions

----------------------------------------------------------------------------

(*********************)
(* Initial predicate *)
(*********************)
Init ==
    /\ network_info =
         [ active   |-> [ c \in Chains |-> {} ]
         , blocks   |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ]
         , branch   |-> [ c \in Chains |-> 0 ]
         , chains   |-> 1
         , height   |-> [ c \in Chains |-> [ b \in Branches |-> -1 ] ]
         , recv     |-> [ c \in Chains |-> [ n \in Nodes |-> <<>> ] ]
         , sent     |-> [ c \in Chains |-> [ n \in Nodes |-> {} ] ] ]
    /\ node_info =
         [ active   |-> [ n \in Nodes |-> {} ]
         , blocks   |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> <<>> ] ] ]
         , branches |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
         , expect   |-> [ n \in Nodes |-> [ c \in Chains |-> {} ] ]
         , headers  |-> [ n \in Nodes |-> [ c \in Chains |-> [ b \in Branches |-> {} ] ] ]
         , messages |-> [ n \in Nodes |-> [ c \in Chains |-> <<>> ] ]
         , offchain |-> [ n \in Nodes |-> <<>> ] ]

----------------------------------------------------------------------------

(***********************************************************************************************)
(* Next actions                                                                                *)
(* - Activation: an inactive node becomes active on a chain                                    *)
(* - Deactivation: an active node becomes inactive on a chain                                  *)
(* - Advertise_branch: a node advertises their current branch                                  *)
(* - Advertise_head: a node advertises their current head height                               *)
(* - Handle_offchain_msg: a node reacts to an offchain message                                 *)
(* - Handle_onchain_msg: a node reacts to a message from another node                          *)
(* - Send_again: a node sends a message again because they have not gotten a response          *)
(* - Block_production: a new block is produced and broadcast to active nodes                   *)
(* - New_branch: a new branch is created and broadcast to active nodes                         *)
(* - New_chain: a new chain is created and broadcast to nodes offchain                         *)
(* - Receive: a message is received, i.e. added to the queue of messages the node can react to *)
(* - Drop: a message sent to a node is dropped and the node is none the wiser                  *)
(* - Drop_offchain: a message sent to a node offchain is dropped                               *)
(* - Get_current_branch_one: a node requests the current branch from another active node       *)
(* - Get_current_branch_all: a node requests the current branch from all other active nodes    *)
(* - Get_current_head_one: a node requests the current head from another active node           *)
(* - Get_current_head_all: a node requests the current head from all other active nodes        *)
(* - Get_block_header_one: a node requests a block header from another active node             *)
(* - Get_block_header_all: a node requests a block header from all other active nodes          *)
(* - Get_operations_one: a node requests a block's operations from another active node         *)
(* - Get_operations_all: a node requests a block's operations from all other active nodes      *)
(***********************************************************************************************)

Next ==
    \* Activation actions
    \/ Activation
    \/ Deactivation
    \* Advertise actions
    \/ Advertise_branch
    \/ Advertise_head
    \* Handle actions
    \/ Handle_offchain_msg
    \/ Handle_onchain_msg
    \/ Send_again
    \* Maintenance actions
    \/ Block_production
    \/ New_branch
    \/ New_chain
    \* Receive actions
    \/ Receive
    \/ Drop
    \/ Drop_offchain
    \* Request actions
    \/ Get_current_branch_one
    \/ Get_current_branch_all
    \/ Get_current_head_one
    \/ Get_current_head_all
    \/ Get_block_header_one
    \/ Get_block_header_all
    \/ Get_operations_one
    \/ Get_operations_all

(***********************)
(* Liveness conditions *)
(***********************)
\* TODO
Fairness == {}

----------------------------------------------------------------------------

(*****************)
(* Specification *)
(*****************)
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

(**************)
(* Invariants *)
(**************)

\* TODO

\* Avoid silliness
TypeOK ==
    /\ network_info \in
         [ active   : [ Chains -> SUBSET Nodes ]
         , branch   : [ Chains -> Branches ]
         , blocks   : [ Chains -> [ Branches -> Seq_n(Blocks, sizeBound) ] ]
         , chains   : Chains
         , height   : [ Chains -> [ Branches -> Heights \cup {-1} ] ]
         , recv     : [ Chains -> [ Nodes -> Seq_n(Messages \cup ExpectMsgs, sizeBound) ] ]
         , sent     : [ Chains -> [ Nodes -> Subsets_n(Messages \cup ExpectMsgs, sizeBound) ] ] ]
    /\ node_info \in
         [ active   : [ Nodes -> SUBSET Chains ]
         , blocks   : [ Nodes -> [ Chains -> [ Branches -> Seq_n(Blocks, sizeBound) ] ] ]
         , branches : [ Nodes -> [ Chains -> Seq_n(Branches, sizeBound) ] ]
         , expect   : [ Nodes -> [ Chains -> Subsets_n(ExpectMsgs, sizeBound) ] ]
         , headers  : [ Nodes -> [ Chains -> [ Branches -> Subsets_n(Headers, sizeBound) ] ] ]
         , messages : [ Nodes -> [ Chains -> Seq_n(FullMsgs \cup SysMsgs, sizeBound) ] ]
         , offchain : [ Nodes -> Seq_n(SysMsgs, sizeBound) ] ]

\* network_info & node_info are in agreement
ActiveAgreement ==
    \A node \in Nodes, chain \in Chains :
        \* actives
        /\ node \in network_info.active[chain] <=> chain \in node_info.active[node]
        \* messages
        /\ ToSet(network_info.recv[chain][node]) = ToSet(node_info.messages[node][chain])
        \* branches
        /\ node_info.branches[node][chain] # <<>> =>
             Head(node_info.branches[node][chain]) <= network_info.branch[chain]
        \* blocks
        /\ \A branch \in ToSet(node_info.branches[node][chain]) :
               isSubSeq(node_info.blocks[node][chain][branch], network_info.blocks[chain][branch])

----------------------------------------------------------------------------

(**************)
(* Properties *)
(**************)

\* Once a message is sent, it is eventually received by the intended recipient
\* A [msg] sent to a [node] ends up in recv[chain][node]
SentMessagesAreReceived ==
    \A chain \in Chains :
        \A node \in network_info.active[chain] :
            \A msg \in Messages :
                msg \in network_info.sent[chain][node] ~>
                  /\ msg \in ToSet(network_info.recv[chain][node])
                  /\ msg \in ToSet(node_info.messages[node][chain])

=============================================================================
