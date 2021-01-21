-------------------------- MODULE DB_Maintenance ---------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages
LOCAL INSTANCE Utils

----------------------------------------------------------------------------

(***********************)
(* Maintenance actions *)
(***********************)

\* Block production
Produce_block(chain, branch, num_ops) ==
    LET height == network_info.height[chain][branch] + 1 \* next block height on branch
        ops    == mkOps(height, num_ops)                 \* block operations
        header == Header(chain, branch, height, num_ops)
        block  == Block(header, ops)
    IN \* add the new block to [branch] on [chain]
       /\ network_info' = [ network_info EXCEPT
            !.blocks[chain][branch] = <<block>> \o @, \* add [block] to [branch]
            !.height[chain][branch] = @ + 1 ]         \* increase height of [branch]
       /\ UNCHANGED node_info

\* A block is produced on an existing branch of an existing chain
Block_production ==
    \E chain \in activeChains :
        \E branch \in activeBranches[chain], num_ops \in Op_nums :
            /\ currentHeight[chain, branch] < sizeBound \* another block can be produced on [branch]
            /\ Produce_block(chain, branch, num_ops)    \* create a new block on [chain] [branch]

\* Start a new branch on an existing [chain]
New_branch_on(chain) ==
    /\ network_info' = [ network_info EXCEPT !.branch[chain] = @ + 1 ]
    /\ UNCHANGED node_info

\* A new branch is created on an existing chain
New_branch ==
    \E chain \in activeChains :
        /\ activeNodes[chain] # {}                \* there are active nodes on [chain]
        /\ network_info.branch[chain] < sizeBound \* we have not reached the max [branch] on [chain]
        /\ New_branch_on(chain)                   \* create a new branch on [chain]

\* A new chain is created and a corresponding message is broadcast to all nodes offchain
\* [sys] is active on [chain]
New_chain ==
    /\ network_info.chains < numChains \* another chain can be added
    /\ LET chain == network_info.chains + 1
       IN /\ network_info' = [ network_info EXCEPT
               !.active[chain] = {sys},
               !.chains = chain ]
          /\ UNCHANGED node_info

=============================================================================
