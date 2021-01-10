----------------------------- MODULE DB_Handle ------------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

LOCAL INSTANCE DB_Activation
LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages
LOCAL INSTANCE Utils

----------------------------------------------------------------------------

(******************)
(* Handle actions *)
(******************)

current_branch[ node \in Nodes, chain \in Chains ] ==
    LET branches == node_info.branches[node][chain] IN
    CASE branches = <<>> -> -1
      [] OTHER -> Head(branches)

current_height[ node \in Nodes, chain \in Chains, branch \in Branches ] ==
    LET blocks == node_info.blocks[node][chain][branch] IN
    CASE blocks = <<>> -> -1
      [] OTHER -> Head(blocks).header.height

\* [node] must be active on block.header.chain
updateBlocks(node, block) ==
    LET chain_block  == block.header.chain
        branch_block == block.header.branch
        height_block == block.header.height
        branch_node  == current_branch[node, chain_block]
        height_node  == current_height[node, chain_block, branch_block]
    IN  {} \* TODO get relevant info
    \* if [node] knows about [branch_block], then ???
    \* if [node] does not know about [branch], then get branch info
    \* TODO

updateBranches(node, chain, branch) ==
    LET expected == current_branch[node, chain] + 1
    IN
      CASE branch = expected ->
           node_info' = [ node_info EXCEPT !.branches[node][chain] = <<branch>> \o @ ]
        [] branch > expected -> {} \* TODO get missing branches
        [] OTHER -> UNCHANGED <<network_info, node_info>>

\* [node] handles the onchain system message [msg]
Handle_sys(node, chain, msg) ==
    LET type   == msg.type
        params == msg.params
    IN
      /\ CASE type = "New_block"  /\ DOMAIN params = { "block" }  -> updateBlocks(node, params.block)
           [] type = "New_branch" /\ DOMAIN params = { "branch" } -> updateBranches(node, chain, params.branch)
      /\ Consume(node_info, chain, node, msg)

Handle_sys_msg ==
    \E chain \in 1..network_info.chains :
        \E node \in network_info.active[chain] :
            /\ node_info.messages[node][chain] # <<>> \* [node] has a message on [chain]
            /\ LET msg == Head(node_info.messages[node][chain])
               IN
                 /\ isSysMsg[msg]                \* [msg] is a system message
                 /\ Handle_sys(node, chain, msg) \* handle the system message

\* [node] handles an offchain [msg]
\* only [New_chain] messages should appear offchain
Handle_offchain(node, msg) ==
    LET type   == msg.type
        params == msg.params
    IN
      /\ CASE type = "New_chain"  /\ DOMAIN params = { "chain" } -> Activate(node, params.chain)
      /\ node_info' = [ node_info EXCEPT !.offchain = Tail(@) ]

\* A node handles an offchain message
Handle_offchain_msg ==
    \E node \in Nodes :
        /\ node_info.offchain[node] # <<>> \* [node] has an offchain message
        /\ LET msg == Head(node_info.offchain[node])
           IN
             Handle_offchain(node, msg) \* handle the offchain message

\* TODO
\*Handle_node(node, chain, msg)
Handle_node_msg == {}

\* Responses
\* Get_current_head: response to Current_branch
\* Get_block_header: response to Current_head
\* Get_operations  : response to Block_header

\* Acknowledgements
\* Ack_current_branch: repsonse to Current_branch
\* Ack_current_head  : response to Current_head
\* Ack_block_header  : response to Current_header & Block_header
\* Ack_operations    : response to Operations

=============================================================================
