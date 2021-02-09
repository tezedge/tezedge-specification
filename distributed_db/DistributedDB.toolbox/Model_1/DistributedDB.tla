--------------------------- MODULE DistributedDB ---------------------------

EXTENDS Utils

CONSTANTS numNodes,  \* number of nodes
          numChains, \* number of chains
          sizeBound  \* bound on many things

\* Node variables
VARIABLES node_active,   \* Nodes -> SUBSET Chains
          node_blocks,   \* Nodes -> Chains -> Branches -> Seq(Blocks)
          node_branches, \* Nodes -> Chains -> Seq(Branches)
          node_headers,  \* Nodes -> Chains -> Branches -> Seq(Headers)
          node_height,   \* Nodes -> Chains -> Branches -> Heights \cup {-1}
          node_incoming, \* Nodes -> Chains -> Seq(Messages)
          node_sent      \* Nodes -> Chains -> Seq(Messages)

\* Network variables
VARIABLES active,  \* Chains -> SUBSET Nodes
          blocks,  \* Chains -> Branches -> Seq(Blocks)
          branch,  \* Chains -> Branches
          chains,  \* Chains
          mailbox, \* Chains -> Nodes -> Seq(Messages)
          height,  \* Chains -> Branches -> Heights \cup {-1}
          sysmsgs  \* Chains -> Seq(Messages)

----------------------------------------------------------------------------

LOCAL INSTANCE DB_Activation  \* Activation and Deactivation actions
LOCAL INSTANCE DB_Advertise   \* Advertisement actions
LOCAL INSTANCE DB_Defs        \* ubiquitous definitions
LOCAL INSTANCE DB_Handle      \* Message handling actions
LOCAL INSTANCE DB_Maintenance \* Block production, new chain, new branch actions
Msgs == INSTANCE DB_Messages    \* Message constructors, functions, actions
LOCAL INSTANCE DB_Receive     \* Receive and drop actions
LOCAL INSTANCE DB_Request     \* Request actions

DB_Init == INSTANCE DB_Init              \* initial states
DB_TypeOK == INSTANCE DB_TypeOK          \* type invariants
DB_Invariants == INSTANCE DB_Invariants  \* other invariants and properties

----------------------------------------------------------------------------

(*********************)
(* Initial predicate *)
(*********************)

\* random initial state
\*Init == LET n == RandomElement(DB_Init!Init_options) IN DB_Init!Initialize[n]

Init == DB_Init!Init_empty

----------------------------------------------------------------------------

(***********************************************************************************************)
(* Next actions                                                                                *)
(* - Activation: an inactive node becomes active on a chain                                    *)
(* - Deactivation: an active node becomes inactive on a chain                                  *)
(* - Advertise_branch: a node advertises their current branch                                  *)
(* - Advertise_head: a node advertises their current head height                               *)
(* - Handle_msg: a node reacts to a message                                                    *)
(* - Send_again: a node sends a message again because they have not gotten a response          *)
(* - New_block: a new block is produced and the current head is broadcasted                    *)
(* - New_branch: a new branch is created and broadcasted                                       *)
(* - New_chain: a new chain is created                                                         *)
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
    \/ New_block
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

(**********************************)
(* Fairness & Liveness conditions *)
(**********************************)

Fairness ==
    \* Weak fairness
    /\ WF_blocks(New_block)  \* New_block is enabled as long as there is space for blocks
    /\ WF_branch(New_branch) \* New_branch is enabled as long as there is a chain with space for another branch
    /\ WF_chains(New_chain)  \* New_chain is enabled as long as we can have more chains
    \* Strong fairness
    /\ SF_<<active, node_active>>(Activation)
    /\ SF_<<sysmsgs, node_incoming>>(Handle_msg)
    /\ SF_<<sysmsgs, node_incoming>>(Receive)
    /\ SF_mailbox(Send_again)
    /\ SF_mailbox(Advertise_branch)
    /\ SF_mailbox(Advertise_head)
    /\ SF_mailbox(Get_curr_branch)
    /\ SF_mailbox(Get_curr_head)
    /\ SF_mailbox(Get_block_header)
    /\ SF_mailbox(Get_operations)

Liveness ==
    /\ []<><<Receive>>_vars          \* there will always be another Receive action
    /\ []<><<Advertise_branch>>_vars \* there will always be another Advertise_branch action
    /\ []<><<Advertise_head>>_vars   \* there will always be another Advertise_head action

----------------------------------------------------------------------------

(*****************)
(* Specification *)
(*****************)

Spec == Init /\ Fairness /\ Liveness /\ [][Next]_vars

=============================================================================
