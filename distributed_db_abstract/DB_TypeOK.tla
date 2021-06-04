------------------------------- MODULE DB_TypeOK -------------------------------

(******************************)
(* Enumerable type invariants *)
(******************************)

EXTENDS DB_Defs

--------------------------------------------------------------------------------

\* Avoid silliness
(*********************************************************)
(* Network variables                                     *)
(* branch  : Chains -> Branches                          *)
(* blocks  : Chains -> Branches -> BoundedSeq(Blocks)    *)
(* chains  : Chains                                      *)
(* height  : Chains -> Branches -> Heights \cup {-1}     *)
(*********************************************************)

\* branch
BranchOK ==
    \A chain \in Chains :
        /\ DOMAIN branch = Chains
        /\ branch[chain] \in Branches \cup {-1}
        /\ chain \in activeChains => branch[chain] >= 0

\* blocks
BlocksOK ==
    \A chain \in Chains :
        \A b \in Branches :
            LET blks == blocks[chain][b]
            IN /\ DOMAIN blocks = Chains
               /\ DOMAIN blocks[chain] = Branches
               /\ Len(blks) <= sizeBound + 1                  \* height of each branch <= sizeBound
               /\ Forall(blks, isBlock)                       \* all blocks are valid
               /\ b \in activeBranches[chain] => blks /= <<>> \* active branches have blocks

\* chains
ChainsOK == chains \in Chains

\* height
HeightOK ==
    \A chain \in Chains :
        \A b \in Branches :
            /\ DOMAIN height = Chains
            /\ DOMAIN height[chain] = Branches
            /\ height[chain][b] \in Heights \cup {-1}
            /\ b \in activeBranches[chain] => height[chain][b] >= 0

\* check all fields of network_info
NetworkOK ==
    /\ BranchOK
    /\ BlocksOK
    /\ ChainsOK
    /\ HeightOK

--------------------------------------------------------------------------------

(*********************************************************************)
(* Node variables                                                    *)
(* node_active   : Nodes -> SUBSET Chains                            *)
(* node_blocks   : Nodes -> Chains -> Branches -> BoundedSeq(Blocks) *)
(* node_branches : Nodes -> Chains -> BoundedSeq(Branches)           *)
(* node_headers  : Nodes -> Chains -> BoundedSeq(Headers)            *)
(* node_height   : Nodes -> Chains -> Branches -> Heights \cup {-1}  *)
(*********************************************************************)

\* node_active
NodeActiveOK == node_active \subseteq Chains

\* node_blocks
NodeBlocksOK ==
    \A chain \in Chains :
        \A b \in Branches :
            LET blks == node_blocks[chain][b] IN
            /\ DOMAIN node_blocks = Chains
            /\ DOMAIN node_blocks[chain] = Branches
            /\ Len(blks) <= sizeBound + 1 \* height of each block <= sizeBound
            /\ Forall(blks, isBlock)      \* all blocks are valid

\* node_branches
NodeBranchesOK ==
    \A chain \in Chains :
        LET branches == node_branches[chain] IN
        /\ DOMAIN node_branches = Chains
        /\ current_branch[chain] <= sizeBound \* branches <= sizeBound
        /\ checkBranches(branches, chain)           \* check that all branches are valid

\* node_headers
NodeHeadersOK ==
    \A chain \in Chains :
        LET headers == node_headers[chain] IN
        /\ DOMAIN node_headers = Chains
        /\ Len(headers) <= sizeBound * (sizeBound + 1) \* bounded list of headers
        /\ Forall(headers, isHeader) \* all headers are valid headers

\* node_height
NodeHeightsOK ==
    \A chain \in Chains :
        \A b \in Branches :
            LET hgt == node_height[chain][b] IN
            /\ DOMAIN node_height = Chains
            /\ DOMAIN node_height[chain] = Branches
            /\ hgt >= -1
            /\ hgt <= height[chain][b] \* node heights do not exceed system heights

\* check all fields of node_info
NodeOK ==
    /\ NodeActiveOK
    /\ NodeBlocksOK
    /\ NodeBranchesOK
    /\ NodeHeadersOK
    /\ NodeHeightsOK

--------------------------------------------------------------------------------

\* Type invariant
TypeOK ==
    /\ NetworkOK
    /\ NodeOK

================================================================================
