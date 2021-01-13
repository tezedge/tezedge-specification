----------------------------- MODULE DB_Handle ------------------------------

(*********************************************************************************)
(* This module contains the actions a node uses to respond to received messages. *)
(*********************************************************************************)

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

LOCAL INSTANCE DB_Activation
LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages
LOCAL INSTANCE DB_Request
LOCAL INSTANCE Utils

----------------------------------------------------------------------------

(******************)
(* Handle helpers *)
(******************)

current_branch[ node \in Nodes, chain \in Chains ] ==
    LET branches == node_info.branches[node][chain]
    IN
      CASE branches = <<>> -> -1
        [] OTHER -> Head(branches)

current_height[ node \in Nodes, chain \in Chains, branch \in Branches ] ==
    LET blocks == node_info.blocks[node][chain][branch]
    IN
      CASE blocks = <<>> -> -1
        [] OTHER -> Head(blocks).header.height

\* [node] updates blocks
\* node \in network_info.active[block_chain]
updateBlocks(node, block) ==
    LET block_chain  == block.header.chain
        block_branch == block.header.branch
        block_height == block.header.height
        node_exp_br  == current_branch[node, block_chain] + 1
        node_exp_ht  == current_height[node, block_chain, block_branch] + 1
    IN
      CASE block_branch \in ToSet(node_info.branches[node][block_chain]) -> \* [node] knows about [block_branch]
           CASE block_height = node_exp_ht -> \* [node] knows about the predecessor of [block]
                node_info' =
                  [ node_info EXCEPT !.blocks[node][block_chain][block_branch] = checkCons(block, @) ]
             [] block_height > node_exp_ht -> \* [node] seems to be missing some blocks on [block_branch]
                \* remember the header if possible
                /\ node_info' = [ node_info EXCEPT !.headers[node][block_chain] = checkAdd(@, block.header) ]
                \* request missing headers
                /\ Request_block_headers(node, block_chain, block_branch, node_exp_ht..block_height)
             [] OTHER -> UNCHANGED <<network_info, node_info>>
        \* [node] does not know about [block_branch]
        [] OTHER ->
           /\ Get_current_branch_n(node, block_chain) \* request current branch of [block_chain]
           /\ UNCHANGED node_info

\* assume start < end
missingBranches[ start, end \in Branches ] ==
    IF start = end
    THEN <<end>>
    ELSE <<end>> \o missingBranches[start, end - 1]

\* [node] updates branches on [chain]
updateBranches(node, chain, branch) ==
    LET expected == current_branch[node, chain] + 1
    IN
      CASE branch = expected ->
           /\ node_info' = [ node_info EXCEPT !.branches[node][chain] = checkCons(branch, @) ]
           /\ Get_current_head_n(node, chain, branch) \* request the current head of [branch] from all active peers
        [] branch > expected ->
           LET missing == missingBranches[expected, branch]
           IN
              /\ node_info' = [ node_info EXCEPT !.branches[node][chain] = missing \o @ ] \* add missing branches
              /\ Request_branch_heads(node, chain, expected..branch) \* request missing branch heads
        [] OTHER -> UNCHANGED <<network_info, node_info>>

\* [node] reacts to info about a block at [height] on [chain] [branch]
updateHeights(node, chain, branch, height) ==
    LET node_br  == current_branch[node, chain]
        expected == current_height[node, chain, branch] + 1
    IN
      CASE \* [node] knows about [branch]
           branch <= node_br ->
                \* [node] requests the corresponding block header
           CASE height = expected -> Get_block_header_n(node, chain, branch, height)
                \* [node] requests the missing block headers
             [] height > expected -> Request_block_headers(node, chain, branch, expected..height)
                \* otherwise [node] does nothing
             [] OTHER -> UNCHANGED <<network_info, node_info>>
        \* [node] does not know about [branch]
        [] OTHER -> UNCHANGED <<network_info, node_info>>

\* [node] reacts to a block [header] on [chain] [branch]
updateHeaders(node, chain, branch, header) ==
    LET height   == header.height
        expected == current_height[node, chain, branch] + 1
    IN
      CASE \* [node] records the block header and requests the operations
           height = expected ->
           /\ node_info' = [ node_info EXCEPT !.headers[node][chain][branch] = checkAdd(@, header) ]
           /\ Get_operations_n(node, chain, branch, height)
           \* [node] records the block header
        [] height > expected ->
           node_info' = [ node_info EXCEPT !.headers[node][chain][branch] = checkAdd(@, header) ]
           \* otherwise [node] does nothing
        [] OTHER -> UNCHANGED <<network_info, node_info>>

\* [node] reacts to operations for the block at [height] on [chain] [branch]
updateOperations(node, chain, branch, height, ops) ==
    LET expected == current_height[node, chain, branch] + 1
        headers  == node_info.headers[node][chain][branch]
    IN
      LET header == Header(chain, branch, height, Len(ops))
      IN  \* [node] knows about the corresponding block header on [chain] [branch] at [height]
        CASE header \in headers ->
                  \* if as expected, [node] adds the block to their [branch] on [chain]
             CASE height = expected ->
                  node_info' = [ node_info EXCEPT
                    !.headers[node][chain][branch] = @ \ {header},
                    !.blocks[node][chain][branch] = checkCons(Block(header, ops), @) ]
               [] OTHER -> UNCHANGED <<network_info, node_info>>
          [] OTHER -> UNCHANGED <<network_info, node_info>>

\* Handle advertised current branch
Handle_branch(node, chain, from, type, params) ==
    LET branch == params.branch
    IN
      /\ updateBranches(node, chain, branch)                      \* handle branch info
      /\ Send(from, chain, AckMsg(node, "Ack_current_branch"))    \* send acknowledgement
      /\ Consume(node_info, chain, node, Msg(from, type, params)) \* manage expectations

\* Handle advertised current head
Handle_head(node, chain, from, type, params) ==
    LET branch == params.branch
        height == params.height
    IN
      /\ updateBranches(node, chain, branch)                      \* handle branch info
      /\ updateHeights(node, chain, branch, height)               \* handle height info
      /\ Send(from, chain, AckMsg(node, "Ack_current_head"))      \* send acknowledgement
      /\ Consume(node_info, chain, node, Msg(from, type, params)) \* manage expectations

\* Handle advertised block header
Handle_header(node, chain, from, type, params) ==
    LET branch == params.branch
        height == params.height
        header == params.header
        node_ht == current_height[node, chain, branch]
        msg     ==
          CASE height <= node_ht -> AckMsg(node, "Ack_block_header")
            [] OTHER -> ErrorMsg(node, "Err_block_header", [ branch |-> branch, height |-> height ])
    IN
      /\ updateBranches(node, chain, branch)                      \* handle branch info
      /\ updateHeights(node, chain, branch, height)               \* handle height info
      /\ updateHeaders(node, chain, branch, header)               \* handle header info
      /\ Send(from, chain, msg)                                   \* send acknowledgement or error
      /\ Consume(node_info, chain, node, Msg(from, type, params)) \* manage expectations

\* Handle advertised operations
Handle_ops(node, chain, from, type, params) ==
    LET branch  == params.branch
        height  == params.height
        ops     == params.ops
        node_ht == current_height[node, chain, branch]
        msg     ==
          CASE height <= node_ht -> AckMsg(node, "Ack_operations")
            [] OTHER -> ErrorMsg(node, "Err_operations", [ branch |-> branch, height |-> height ])
    IN
      /\ updateBranches(node, chain, branch)                      \* handle branch info
      /\ updateHeights(node, chain, branch, height)               \* handle height info
      /\ updateOperations(node, chain, branch, height, ops)       \* handle operations info
      /\ Send(from, chain, msg)                                   \* send acknowledgement or error
      /\ Consume(node_info, chain, node, Msg(from, type, params)) \* manage expectations

----------------------------------------------------------------------------

(******************)
(* Handle actions *)
(******************)

(*********************)
(* Offchain messages *)
(*********************)

\* [node] handles an offchain [msg]
Handle_offchain(node, msg) ==
    LET type   == msg.type
        params == msg.params
    IN
      /\ CASE type = "New_chain" /\ DOMAIN params = { "chain" } ->
         LET chain == params.chain
         IN
           /\ Activate(node, chain)             \* activate the new chain
           /\ Get_current_branch_n(node, chain) \* request current branch from all active peers
           /\ node_info' = [ node_info EXCEPT !.offchain[node][chain] = Tail(@) ] \* consume offchain message

\* A node handles an offchain message
Handle_offchain_msg ==
    \E node \in Nodes :
        /\ node_info.offchain[node] # <<>> \* [node] has an offchain message
        /\ LET msg == Head(node_info.offchain[node])
           IN Handle_offchain(node, msg)   \* [node] handles an offchain message

(********************)
(* Onchain messages *)
(********************)

\* Handle system message
\* [node] handles a system message on [chain]
Handle_sys(node, chain, type, params) ==
    /\ CASE type = "New_block" /\ DOMAIN params = { "block" }  ->
            updateBlocks(node, params.block)
         [] type = "New_branch" /\ DOMAIN params = { "branch" } ->
            updateBranches(node, chain, params.branch)
    /\ Consume(node_info, chain, node, SysMsg(type, params))

\* A node handles some system message
Handle_sys_msg ==
    \E chain \in 1..network_info.chains :
        \E node \in network_info.active[chain] :
            /\ node_info.messages[node][chain] # <<>> \* [node] has a message on [chain]
            /\ LET msg == Head(node_info.messages[node][chain])
               IN
                 /\ isSysMsg[msg]                                 \* [msg] is a system message
                 /\ Handle_sys(node, chain, msg.type, msg.params) \* handle the system message

\* Handle acknowledgement message
\* [node] handles an ack [msg] on [chain]
Handle_ack(node, chain, msg) == node_info' = [ node_info EXCEPT !.expect[node][chain] = @ \ {msg} ]

\* Handle advertise message
Handle_advertise(node, chain, from, type, params) ==
    CASE /\ type = "Current_branch"
         /\ DOMAIN params = { "branch" } -> Handle_branch(node, chain, from, type, params)
      [] /\ type = "Current_head"
         /\ DOMAIN params = { "branch", "height" } -> Handle_head(node, chain, from, type, params)
      [] /\ type = "Block_header"
         /\ DOMAIN params = { "branch", "height", "header" } -> Handle_header(node, chain, from, type, params)
      [] /\ type = "Operations"
         /\ DOMAIN params = { "branch", "height", "ops" } -> Handle_ops(node, chain, from, type, params)

\* Send current branch
Send_branch(from, chain, to) ==
    LET msg == Msg(from, "Current_branch", [ branch |-> current_branch[from, chain] ])
    IN Send(to, chain, msg)

\* Send current head
Send_head(from, chain, to, params) ==
    LET branch == params.branch
        msg    == Msg(from, "Current_head", [ branch |-> branch, height |-> current_height[from, chain, branch] ])
    IN Send(to, chain, msg)

\* Send block header
Send_header(from, chain, to, params) ==
    LET branch == params.branch
        height == params.height
        blocks == node_info.blocks[from][chain][branch]
    IN
      CASE \* [from] has seen the requested block
           height \in { block.header.height : block \in ToSet(blocks) } ->
           LET pred[ h \in Heights ] == [ b \in Blocks |-> b.header.height = h ] 
               header == Select(blocks, pred[height]).header
               msg    == Msg(from, "Block_header", [ branch |-> branch, height |-> height, header |-> header ])
           IN Send(to, chain, msg)
           \* [from] has not seen the requested block
        [] OTHER -> Send(to, chain, ErrorMsg(from, "Err_block_header", params))

\* Send block operations
Send_operations(from, chain, to, params) ==
    LET branch == params.branch
        height == params.height
        blocks == node_info.blocks[from][chain][branch]
    IN
      CASE \* [from] has seen the requested block
           height \in { block.header.height : block \in ToSet(blocks) } ->
           LET pred[ h \in Heights ] == [ b \in Blocks |-> b.header.height = h ] 
               ops == Select(blocks, pred[height]).ops
               msg == Msg(from, "Operations", [ branch |-> branch, height |-> height, ops |-> ops ])
           IN Send(to, chain, msg)
           \* [from] has not seen the requested block
        [] OTHER -> Send(to, chain, ErrorMsg(from, "Err_operations", params))

\* Handle a request message
Handle_request(node, chain, from, type, params) ==
    /\ node_info' = [ node_info EXCEPT !.messages[node][chain] = Tail(@) ]         \* consume message
    /\ CASE type = "Get_current_branch" /\ DOMAIN params = { "chain" } ->
            /\ Send_branch(node, chain, from)                                      \* send current branch
            /\ Expect(from, chain, AckMsg(from, "Ack_current_branch"))             \* expect acknowledgement
         [] type = "Get_current_head" /\ DOMAIN params = { "branch" } ->
            /\ Send_head(node, chain, from, params)                                \* send current head
            /\ Expect(from, chain, AckMsg(from, "Ack_current_head"))               \* expect acknowledgement
         [] type = "Get_block_header" /\ DOMAIN params = { "branch", "height" } ->
            /\ Send_header(node, chain, from, params)                              \* send block header or error
            /\ Expect(from, chain, AckMsg(from, "Ack_block_header"))               \* expect acknowledgement
         [] type = "Get_operations" /\ DOMAIN params = { "branch", "height" } ->
            /\ Send_operations(node, chain, from, params)                          \* send operations or error
            /\ Expect(from, chain, AckMsg(from, "Ack_operations"))                 \* expect acknowledgement

\* [node] handles [msg] on [chain]
Handle_onchain(node, chain, msg) ==
    LET type   == msg.type
        params == msg.params
    IN
      CASE \* System messages
           type \in SysMsgTypes -> Handle_sys(node, chain, type, params)
           \* Request messages
        [] type \in ReqMsgTypes -> Handle_request(node, chain, msg.from, type, params)
           \* Advertise messages
        [] type \in AdMsgTypes  -> Handle_advertise(node, chain, msg.from, type, params)
           \* Acknowledgment messages
        [] type \in AckMsgTypes -> Handle_ack(node, chain, msg)

\* A node handles an onchain message on some chain
Handle_onchain_msg ==
    \E chain \in 1..network_info.chains :
        \E node \in network_info.active[chain] :
            /\ node_info.messages[node][chain] # <<>>
            /\ LET msg == Head(node_info.messages[node][chain])
               IN Handle_onchain(node, chain, msg)

----------------------------------------------------------------------------

(**************)
(* Send again *)
(**************)

\* [node] has not received an expected response
Send_another_time(node, chain, msg) ==
    /\ {}

\* A node sends an unrequited message again
Send_again ==
    \E chain \in 1..network_info.chains :
        \E node \in network_info.active[chain] :
            \E exp \in node_info.expect[node][chain] :
                Send(exp.from, chain, msg_of_expect[exp]) \* send corresponding msg again

=============================================================================
