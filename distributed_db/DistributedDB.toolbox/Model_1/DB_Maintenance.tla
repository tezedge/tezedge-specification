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

(* Block production/notification *)

\* Block production and notification
Produce_block(chain, branch, num_ops) ==
    LET height == network_info.height[chain][branch] + 1 \* next block height on branch
        ops    == mkOps(height, num_ops)                 \* block operations
        header == Header(chain, branch, height, num_ops)
        block  == Block(header, ops)
    IN
      \* add the new block to the [branch] on [chain]
      \* send new [block] to all active [node]s on [chain]
      network_info' = [ network_info EXCEPT
        !.blocks[chain][branch] = <<block>> \o @, \* add [block] to [branch]
        !.height[chain][branch] = @ + 1,          \* increase height of [branch]
        !.sent[chain] = [ n \in Nodes |->         \* send New_block message to active nodes on [chain]
            LET msg  == SysMsg("New_block", [ block |-> block ])
                curr == @[n]
            IN   \* only send to them if they have space
              CASE n \in activeNodes[chain] -> checkAdd(curr, msg)
                [] OTHER -> curr ] ]

\* A block is produced on an existing branch of an existing chain
Block_production ==
    \E chain \in activeChains :
        \E branch \in activeBranches[chain], num_ops \in Op_nums :
            /\ activeNodes[chain] # {}                        \* there are active nodes on [chain]
            /\ network_info.height[chain][branch] < sizeBound \* another block can be produced on [branch]
            /\ Produce_block(chain, branch, num_ops)          \* create a new block on [chain] [branch]
            /\ UNCHANGED node_info

\* Start a new branch on an existing [chain]
New_branch_on(chain) ==
    network_info' = [ network_info EXCEPT
      !.branch[chain] = @ + 1,          \* increase branch number on [chain]
      !.sent[chain] = [ n \in Nodes |-> \* broadcast New_branch to active nodes on [chain]
            LET msg  == SysMsg("New_branch", [ branch |-> network_info.branch[chain] + 1 ])
                curr == @[n]
            IN
              CASE n \in network_info.active[chain] -> checkAdd(curr, msg)
                [] OTHER -> curr ] ]

\* A new branch is created on some chain
New_branch ==
    \E chain \in Chains :
        /\ activeNodes[chain] # {}                \* there are active nodes on [chain]
        /\ network_info.branch[chain] < sizeBound \* we have not reached the max [branch] on [chain]
        /\ New_branch_on(chain)                   \* create a new branch on [chain]
        /\ UNCHANGED node_info

\* A new chain is created and a corresponding message is broadcast to all nodes offchain
New_chain ==
    /\ network_info.chains < numChains      \* another chain can be added
    /\ LET chain == network_info.chains + 1
           msg   == SysMsg("New_chain", [ chain |-> chain ])
       IN
         /\ network_info' = [ network_info EXCEPT !.chains = chain ]
         \* broadcast to all nodes who can receive an offchain message
         /\ node_info' = [ node_info EXCEPT !.offchain = [ n \in Nodes |-> checkAppend(@[n], msg) ] ]

=============================================================================
