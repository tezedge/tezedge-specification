-------------------------- MODULE DB_Maintenance ---------------------------

EXTENDS DB_Defs

----------------------------------------------------------------------------

(***********************)
(* Maintenance actions *)
(***********************)

\* Block production
Produce_block(chain, b, num_ops) ==
    LET hgt    == height[chain][b] + 1 \* next block height on branch
        header == Header(chain, b, hgt)
        block  == Block(header, num_ops)
    IN \* add the new block to branch [b] on [chain]
       /\ blocks' = [ blocks EXCEPT ![chain][b] = Cons(block, @) ] \* add [block] to branch [b]
       /\ height' = [ height EXCEPT ![chain][b] = hgt ]            \* increase height of branch [b]
       /\ UNCHANGED <<branch, chains>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers, node_height>>

\* A block is produced on an existing branch of an existing chain
New_block ==
    \E chain \in activeChains :
        \E b \in activeBranches[chain] :
            LET num_ops == RandomElement(Op_nums) IN
            /\ height[chain][b] < sizeBound     \* another block can be produced on branch [b]
            /\ Produce_block(chain, b, num_ops) \* create a new block on [chain] branch [b]

\* Start a new branch on an existing [chain] with genesis block
New_branch_on(chain) ==
    LET b   == branch[chain] + 1
        blk == Block(Header(chain, b, 0), 0)
    IN /\ blocks' = [ blocks EXCEPT ![chain][b] = <<blk>> ]
       /\ branch' = [ branch EXCEPT ![chain] = b ]
       /\ height' = [ height EXCEPT ![chain][b] = 0 ]
       /\ UNCHANGED chains
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers, node_height>>

\* A new branch is created on an existing chain
New_branch ==
    \E chain \in activeChains :
        /\ branch[chain] < sizeBound \* we have not reached the max branch [b] on [chain]
        /\ New_branch_on(chain)      \* create a new branch on [chain]

\* A new [chain] is created with branch 0 and genesis block and [sys] is active on [chain]
New_chain ==
    /\ chains < numChains \* another chain can be added
    /\ LET chain == chains + 1
           blk   == Block(Header(chain, 0, 0), 0)
       IN /\ blocks' = [ blocks EXCEPT ![chain][0] = <<blk>> ]
          /\ branch' = [ branch EXCEPT ![chain] = 0 ]
          /\ chains' = chain
          /\ height' = [ height EXCEPT ![chain][0] = 0 ]
          /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers, node_height>>

=============================================================================
