-------------------------------- MODULE DB ---------------------------------

CONSTANTS
    numChains, \* number of chains
    sizeBound  \* bound on many things

\* Node variables
VARIABLES
    node_active,   \* SUBSET Chains
    node_blocks,   \* Chains -> Branches -> Seq(Blocks)
    node_branches, \* Chains -> Seq(Branches)
    node_headers,  \* Chains -> Branches -> Seq(Headers)
    node_height    \* Chains -> Branches -> Heights \cup {-1}

\* Network variables
VARIABLES
    blocks,  \* Chains -> Branches -> Seq(Blocks)
    branch,  \* Chains -> Branches
    chains,  \* Chains
    height   \* Chains -> Branches -> Heights \cup {-1}

vars == <<node_active, node_blocks, node_branches, node_headers, node_height, blocks, branch, chains, height>>

----------------------------------------------------------------------------

Activation  == INSTANCE DB_Activation  \* Activation and Deactivation actions
Defs        == INSTANCE DB_Defs        \* ubiquitous definitions
Handle      == INSTANCE DB_Handle      \* Message handling actions
Maintenance == INSTANCE DB_Maintenance \* Block production, new chain, new branch actions
Request     == INSTANCE DB_Request     \* Request actions
Initialize  == INSTANCE DB_Init        \* initial states
TypeOK      == INSTANCE DB_TypeOK      \* type invariants
Invariants  == INSTANCE DB_Invariants  \* other invariants and properties

----------------------------------------------------------------------------

(*********************)
(* Initial predicate *)
(*********************)

\* Simple "empty" initial
\*Init == DB_Init!Init_empty

\* Various initial states representing different "checkpoints" in the evolution of the model
Init == \E n \in Initialize!Init_options : Initialize!Initialize(n)

----------------------------------------------------------------------------

(***********************************************************************************************)
(* Next actions                                                                                *)
(* - Activation: an inactive node becomes active on a chain                                    *)
(* - Deactivation: an active node becomes inactive on a chain                                  *)
(* - Advertise_branch: a node advertises their current branch                                  *)
(* - Advertise_head: a node advertises their current head height                               *)
(* - Handle_msg: a node reacts to a message                                                    *)
(* - New_block: a new block is produced and the current head is broadcasted                    *)
(* - New_branch: a new branch is created and broadcasted                                       *)
(* - New_chain: a new chain is created                                                         *)
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
    \/ Activation!Activation
    \/ Activation!Deactivation
    \* Handle actions
    \/ Handle!Handle_msg
    \* Maintenance actions
    \/ Maintenance!New_block
    \/ Maintenance!New_chain
    \/ Maintenance!New_branch
    \* Request actions
    \/ Request!Get_current_branch
    \/ Request!Get_current_head
    \/ Request!Get_block_header
    \/ Request!Get_operations

(***********************)
(* Fairness conditions *)
(***********************)

Fairness ==
    /\ WF_vars(Maintenance!New_block)
    /\ WF_vars(Maintenance!New_branch)
    /\ WF_vars(Maintenance!New_chain)
    /\ SF_vars(Activation!Activation)
    /\ SF_vars(Handle!Handle_msg)
    /\ SF_vars(Advertise!Advertise_branch)
    /\ SF_vars(Advertise!Advertise_head)
    /\ SF_vars(Request!Get_curr_branch)
    /\ SF_vars(Request!Get_curr_head)
    /\ SF_vars(Request!Get_block_header)
    /\ SF_vars(Request!Get_operations)

----------------------------------------------------------------------------

(*****************)
(* Specification *)
(*****************)

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
