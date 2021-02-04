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
    \* headers  : [ Nodes -> [ Chains -> Seq(Headers) ] ]
    \* height   : [ Nodes -> [ Chains -> [ Branches -> Heights \cup {-1} ] ] ]
    \* messages : [ Nodes -> [ Chains -> Seq(Messages) ] ]

\* VARIABLES node_active,   \* Nodes -> SUBSET Chains
\*           node_blocks,   \* Nodes -> Chains -> Branches -> Seq(Blocks)
\*           node_branches, \* Nodes -> Chains -> Seq(Branches)
\*           headers,       \* Nodes -> Chains -> Branches -> Seq(Headers)
\*           node_height,   \* Nodes -> Chains -> Branches -> Heights \cup {-1}
\*           node_msgs,     \* Nodes -> Chains -> Seq(Messages)
\*           node_sent,     \* Nodes -> Chains -> Seq(Messages)
\*           state          \* ???

VARIABLE network_info
    \* active : [ Chains -> SUBSET Nodes ]
    \* blocks : [ Chains -> [ Branches -> Seq(Blocks) ] ]
    \* branch : [ Chains -> Branches ]
    \* chains : Chains
    \* height : [ Chains -> [ Branches -> Heights \cup {-1} ] ]
    \* sent   : [ Chains -> [ Nodes -> SUBSET Messages ] ]

\* VARIABLES net_active, \* Chains -> SUBSET Nodes
\*           net_blocks, \* Chains -> Branches -> Seq(Blocks)
\*           net_branch, \* Chains -> Branches
\*           chains,     \* Chains
\*           net_height, \* Chains -> Branches -> Heights \cup {-1}
\*           mailbox     \* Chains -> Nodes -> Seq(Messages)

\*node_vars == <<node_active, node_blocks, node_branches, headers, node_height, node_msgs, node_sent, state>>
\*net_vars == <<net_active, net_blocks, net_branch, chains, net_height, mailbox>>
\*vars == <<net_vars, node_vars>>

vars == <<network_info, node_info>>

----------------------------------------------------------------------------

LOCAL INSTANCE DB_Activation  \* Activation and Deactivation actions
LOCAL INSTANCE DB_Advertise   \* Advertisement actions
LOCAL INSTANCE DB_Defs        \* ubiquitous definitions
LOCAL INSTANCE DB_Handle      \* Message handling actions
LOCAL INSTANCE DB_Maintenance \* Block production, new chain, new branch actions
LOCAL INSTANCE DB_Messages    \* Message constructors, functions, actions
LOCAL INSTANCE DB_Receive     \* Receive and drop actions
LOCAL INSTANCE DB_Request     \* Request actions

DB_Init == INSTANCE DB_Init              \* initial states
DB_TypeOK == INSTANCE DB_TypeOK          \* type invariants
DB_Invariants == INSTANCE DB_Invariants  \* other invariants and properties

----------------------------------------------------------------------------

(*********************)
(* Initial predicate *)
(*********************)

Init == DB_Init!Init

----------------------------------------------------------------------------

(***********************************************************************************************)
(* Next actions                                                                                *)
(* - Activation: an inactive node becomes active on a chain                                    *)
(* - Deactivation: an active node becomes inactive on a chain                                  *)
(* - Advertise_branch: a node advertises their current branch                                  *)
(* - Advertise_head: a node advertises their current head height                               *)
(* - Handle_onchain_msg: a node reacts to a message from another node                          *)
(* - Send_again: a node sends a message again because they have not gotten a response          *)
(* - Block_production: a new block is produced and broadcast to active nodes                   *)
(* - New_branch: a new branch is created and broadcast to active nodes                         *)
(* - New_chain: a new chain is created and broadcast to nodes offchain                         *)
(* - Receive: a message is received, i.e. added to the queue of messages the node can react to *)
(* - Drop: a message sent to a node is dropped and the node is none the wiser                  *)
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
    \* Activation actions (nodes)
    \/ Activation
    \/ Deactivation
    \* Advertise actions (nodes & sys)
    \/ Advertise_branch
    \/ Advertise_sys_branch
    \/ Advertise_head
    \/ Advertise_sys_head
    \* Handle actions (nodes)
    \/ Handle_msg
    \/ Send_again
    \* Maintenance actions (sys)
    \/ Block_production
    \/ New_chain
    \/ New_branch
    \* Receive actions (nodes & sys)
    \/ Receive
    \/ Drop
    \* Request actions (nodes)
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

Fairness ==
    \* Weak fairness
    /\ WF_vars(Activation)
    /\ WF_vars(Block_production)
    /\ WF_vars(New_branch)
    /\ WF_vars(New_chain)
    \* Strong fairness
    /\ SF_vars(Advertise_branch)
    /\ SF_vars(Advertise_head)
    /\ SF_vars(Handle_msg)
    /\ SF_vars(Send_again)
    /\ SF_vars(Receive)
    /\ SF_vars(Get_current_branch_one)
    /\ SF_vars(Get_current_branch_all)
    /\ SF_vars(Get_current_head_one)
    /\ SF_vars(Get_current_head_all)
    /\ SF_vars(Get_block_header_one)
    /\ SF_vars(Get_block_header_all)
    /\ SF_vars(Get_operations_one)
    /\ SF_vars(Get_operations_all)
    \* Invariants
    

----------------------------------------------------------------------------

(*****************)
(* Specification *)
(*****************)

Spec == Init /\ Fairness /\ [][Next]_vars

=============================================================================
