-------------------------- MODULE DB_Maintanence ---------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages
LOCAL INSTANCE Utils

----------------------------------------------------------------------------

(***********************)
(* Maintanence actions *)
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
      /\ network_info' = [ network_info EXCEPT
           !.blocks[chain][branch] = <<block>> \o @,
           !.sent[chain] = [ n \in Nodes |->
               LET msg  == SysMsg("New_block", [ block |-> block ])
                   curr == @[n]
               IN
                 CASE n \in network_info.active[chain] -> checkAdd(curr, msg) \* can only send to them if they have space
                   [] OTHER -> curr ] ]
      /\ UNCHANGED node_info

\* A block is produced on an existing branch of an existing chain
Block_production ==
    \E chain \in 1..network_info.chains :
        \E branch \in 0..network_info.branch[chain], num_ops \in Op_nums :
            /\ network_info.height[chain][branch] < sizeBound
            /\ Produce_block(chain, branch, num_ops)

\* Start a new branch on an existing [chain]
New_branch_for(chain) ==
    /\ network_info' = [ network_info EXCEPT
         !.branch[chain] = @ + 1,
         !.sent[chain] = [ n \in Nodes |->
               LET branch == network_info.branch[chain] + 1 \* new branch id
                   msg    == SysMsg("New_branch", [ branch |-> branch ])
                   curr   == @[n]
               IN
                 CASE n \in network_info.active[chain] -> checkAdd(curr, msg)
                   [] OTHER -> curr ] ]
    /\ UNCHANGED node_info

\* A new branch is created on some chain
New_branch ==
    \E chain \in Chains :
        /\ network_info.active[chain] # {}        \* there are active nodes on [chain]
        /\ network_info.branch[chain] < sizeBound \* we have not reached the max [branch] on [chain]
        /\ New_branch_for(chain)

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
