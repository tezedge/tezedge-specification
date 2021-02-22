-------------------------------- MODULE DB ---------------------------------

EXTENDS DB_Defs

\* CONSTANTS
\*     numChains, \* number of chains
\*     sizeBound  \* bound on many things

\* \* Node variables
\* VARIABLES
\*     node_active,   \* SUBSET Chains
\*     node_blocks,   \* Chains -> Branches -> Seq(Blocks)
\*     node_branches, \* Chains -> Seq(Branches)
\*     node_headers,  \* Chains -> Branches -> Seq(Headers)
\*     node_height    \* Chains -> Branches -> Heights \cup {-1}

\* \* Network variables
\* VARIABLES
\*     blocks,  \* Chains -> Branches -> Seq(Blocks)
\*     branch,  \* Chains -> Branches
\*     chains,  \* Chains
\*     height   \* Chains -> Branches -> Heights \cup {-1}

network_vars == <<blocks, branch, chains, height>>
node_vars == <<node_active, node_blocks, node_branches, node_headers, node_height>>
vars == <<network_vars, node_vars>>

----------------------------------------------------------------------------

Activation  == INSTANCE DB_Activation  \* Activation and Deactivation actions
Defs        == INSTANCE DB_Defs        \* ubiquitous definitions
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

(**************************************************************)
(* Next actions                                               *)
(* - Activation: an inactive node becomes active on a chain   *)
(* - Deactivation: an active node becomes inactive on a chain *)
(* - Handle_msg: a node reacts to a message                   *)
(* - New_block: a new block is produced                       *)
(* - New_branch: a new branch is created                      *)
(* - New_chain: a new chain is created                        *)
(* - Get_current_branch: node retrieves the current branch    *)
(* - Get_current_head: node retrieves the current head        *)
(* - Get_block_header: node retrieves a block header          *)
(* - Get_operations: node retrieves a block's operations      *)
(**************************************************************)

Next ==
    \* Activation actions
    \/ Activation!Activation
    \/ Activation!Deactivation
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
    /\ SF_vars(Request!Get_current_branch)
    /\ SF_vars(Request!Get_current_head)
    /\ SF_vars(Request!Get_block_header)
    /\ SF_vars(Request!Get_operations)

----------------------------------------------------------------------------

(*****************)
(* Specification *)
(*****************)

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ Fairness

----------------------------------------------------------------------------

\* Temporal property
ActiveNodeEventuallySyncs == \A chain \in Chains :
    /\ []<>(active[chain])
    /\ []<><<Next>>_<<node_blocks, node_branches, node_headers, node_height>>
    => Invariants!EventuallySyncs(chain)

THEOREM Safe == Spec => []TypeOK!TypeOK

THEOREM Consistent == Spec => []Invariants!Agreement

THEOREM EventuallySynced == FairSpec => ActiveNodeEventuallySyncs

=============================================================================
