----------------------------- MODULE DB_Handle ------------------------------

(**************************************************************)
(* A node uses these actions to respond to received messages. *)
(**************************************************************)

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

\* TODO
\* [node] requests missing branch head on [chain]
updateBranches_sent(sent, node, chain, branch) ==
    LET next_br == min_set(Branches \ branchSet[node, chain])
        msg     == [ type |-> "Get_current_head", params |-> [ branch |-> next_br ] ]
    IN IF branch \in branchSet[node, chain] \/ branch < 0
       THEN sent
       ELSE Broadcast(sent, node, chain, msg)

\* [node] updates branches on [chain]
updateBranches(branches, node, chain, branch) ==
    IF branch \in branchSet[node, chain] \/ branch < 0 \* if [node] can disregard [branch]
    THEN branches                                      \* then do nothing
    ELSE insertBranch(branch, branches)                \* else add [branch]

\* [node] reacts to info about a block at [height] on [branch] of [chain]
updateHeights(sent, node, chain, branch, height) ==
    LET next_br == min_set(Branches \ branchSet[node, chain])
        next_ht == min_set(Heights \ heightSet[node, chain, branch])
    IN IF height \in heightSet[node, chain, branch] \* [node] knows about a block at [height]
       THEN sent
       ELSE IF branch \notin branchSet[node, chain] \* [node] does not know about [branch]
            THEN updateBranches_sent(sent, node, chain, next_br) \* update branches
            ELSE LET msg == [ type |-> "Get_block_header",
                              params |-> [ branch |-> branch, height |-> next_ht ] ] 
                 IN Broadcast(sent, node, chain, msg)

\* [node] reacts to a block header at [height] on [branch] of [chain]
updateHeaders_sent(sent, node, chain, branch, height) ==
    LET exp_br == current_branch[node, chain] + 1
        exp_ht == current_height[node, chain, branch] + 1
    IN IF height \in blockHeights[node, chain, branch] \* [node] already knows about this block
       THEN sent
       ELSE IF height \in headerHeights[node, chain, branch] \* [node] has a header at [height]
            THEN LET msg == [ type |-> "Get_operations",
                              params |-> [ branch |-> branch, height |-> height ] ]
                 IN Broadcast(sent, node, chain, msg)             \* request operations
            ELSE updateHeights(sent, node, chain, branch, height) \* request current head or block header

\* [node] reacts to a block [header] on [chain] [branch]
updateHeaders(headers, node, chain, branch, height, num_ops) ==
    IF height \notin heightSet[node, chain, branch]
    \* [node] records the block header (and requests the operations)
    THEN checkInsertHeader(Header(chain, branch, height, num_ops), headers)
    ELSE headers

\* [node] reacts to operations for the block at [height] on [chain] [branch]
updateOperations(blocks, headers, node, chain, branch, height, ops) ==
    LET header == Header(chain, branch, height, Len(ops))
    IN \* [node] knows about the corresponding block header on [chain] [branch] at [height]
       IF header \in ToSet(headers)
       THEN \* [node] adds the block to their [branch] on [chain]
            checkInsertBlock(Block(header, ops), blocks)
       ELSE blocks

\* [node] handles advertised current [branch] on [chain] from [from]
Handle_branch(node, chain, from, type, params) ==
    LET branch == params.branch
        ack    == AckMsg(node, from, "Ack_current_branch")
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain] =
            LET ub == updateBranches_sent(@, node, chain, branch)             \* request current head
            IN [ ub EXCEPT ![from] = Send(ub[from], ack) ] ]                  \* send acknowledgment
       /\ node_info' = [ node_info EXCEPT
            !.branches[node][chain] = updateBranches(@, node, chain, branch), \* update branches
\*            !.expect[node][chain] = ManageExpect(@, from, type),              \* manage expectations
            !.messages[node][chain] = Tail(@) ]                               \* consume message

\* [node] handles advertised current head of [branch] on [chain] from [from]
Handle_head(node, chain, from, type, params) ==
    LET branch == params.branch
        height == params.height
        ack    == AckMsg(node, from, "Ack_current_head")
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain] =
            LET uh == updateHeights(@, node, chain, branch, height) \* request block header or current head
            IN [ uh EXCEPT ![from] = Send(uh[from], ack) ] ]        \* send acknowledgment
       /\ node_info' = [ node_info EXCEPT
            !.branches[node][chain] = updateBranches(@, node, chain, branch), \* update branches
\*            !.expect[node][chain] = ManageExpect(@, from, type),              \* manage expectations
            !.height[node][chain][branch] = max[@, height],                   \* update height
            !.messages[node][chain] = Tail(@) ]                               \* consume message

\* [node] handles advertised block [header] on [branch] of [chain] from [from]
Handle_header(node, chain, from, type, params) ==
    LET branch  == params.branch
        height  == params.height
        header  == params.header
        num_ops == header.num_ops
        ack     == AckMsg(node, from, "Ack_block_header")
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain] =
            LET uh == updateHeaders_sent(@, node, chain, branch, height) \* request current head, header, or ops
            IN [ uh EXCEPT ![from] = Send(uh[from], ack) ] ]             \* send acknowledgment
       /\ node_info' = [ node_info EXCEPT
            !.branches[node][chain] = updateBranches(@, node, chain, branch),                \* update branches
\*            !.expect[node][chain] = ManageExpect(@, from, type),                             \* manage expectations
            !.headers[node][chain] = updateHeaders(@, node, chain, branch, height, num_ops), \* update headers
            !.messages[node][chain] = Tail(@) ]                                              \* consume message

\* [node] handles advertised [ops] on [branch] of [chain] from [from]
Handle_ops(node, chain, from, type, params) ==
    LET branch  == params.branch
        height  == params.height
        ops     == params.ops
        header  == Header(chain, branch, height, Len(ops))
        headers == updateHeaders(node_info.headers[node][chain], node, chain, branch, height, Len(ops))
        ack     == AckMsg(node, from, "Ack_operations")
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain] =
            LET uh == updateHeaders_sent(@, node, chain, branch, height) \* request info
            IN [ uh EXCEPT ![from] = Send(uh[from], ack) ] ]             \* send ack
       /\ node_info' = [ node_info EXCEPT
            !.blocks[node][chain][branch] =
                updateOperations(@, headers, node, chain, branch, height, ops), \* update blocks
            !.branches[node][chain] = updateBranches(@, node, chain, branch),   \* update branches
\*            !.expect[node][chain] = ManageExpect(@, from, type),                \* manage expectations
            !.headers[node][chain] = Remove(headers, header),                   \* update headers
            !.messages[node][chain] = Tail(@) ]                                 \* consume message

----------------------------------------------------------------------------

(******************)
(* Handle actions *)
(******************)

\* [node] handles an ack [msg] on [chain]
Handle_ack(node, chain, msg) ==
    IF node = sys
    THEN
      /\ network_info' = [ network_info EXCEPT !.sysmsgs[chain] = Tail(@) ] \* consume message
      /\ UNCHANGED node_info
    ELSE
      /\ node_info' = [ node_info EXCEPT
           !.expect[node][chain] = @ \ {msg},  \* remove expectation
           !.messages[node][chain] = Tail(@) ] \* consume message
      /\ UNCHANGED network_info

\* Handle advertise message
Handle_advertise(node, chain, from, type, params) ==
    CASE /\ DOMAIN params = { "branch" }
         /\ type = "Current_branch" -> Handle_branch(node, chain, from, type, params)
      [] /\ DOMAIN params = { "branch", "height" }
         /\ type = "Current_head" -> Handle_head(node, chain, from, type, params)
      [] /\ DOMAIN params = { "branch", "height", "header" }
         /\ type = "Block_header" -> Handle_header(node, chain, from, type, params)
      [] /\ DOMAIN params = { "branch", "height", "ops" }
         /\ type = "Operations" -> Handle_ops(node, chain, from, type, params)

\* what was expected given the error
of_error(err) ==
    LET from   == err.from
        to     == err.to
        type   == err.type
        params == err.error
        ack_of_err[ e \in ErrMsgTypes ] ==
          CASE e = "Err_block_header" -> "Block_header"
            [] e = "Err_operations" -> "Operations"
    IN Msg(to, from, ack_of_err[type], params)

\* [node] handles an error [err] on [chain]
Handle_err(node, chain, err) ==
    /\ node_info' = [ node_info EXCEPT
         !.expect[node][chain] = @ \ of_error(err), \* remove expectation
         !.messages[node][chain] = Tail(@) ]        \* consume message
    /\ UNCHANGED network_info

\* [from] sends current branch to [to] on [chain]
Send_branch(from, chain, to) ==
    LET msg == Msg(from, to, "Current_branch", [ branch |-> current_branch[from, chain] ])
\*        ack == AckMsg(from, "Ack_current_branch")
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain][to] = Send(@, msg) ] \* [from] sends current branch
       /\ node_info' = [ node_info EXCEPT
            !.messages[from][chain] = Tail(@) ] \* [from] consumes message
\*            !.expect[from][chain] = Expect(@, to, ack) ] \* [from] expects ack from [to]

\* [sys] sends current branch to [to] on [chain]
Send_branch_sys(chain, to) ==
    LET msg == Msg(sys, to, "Current_branch", [ branch |-> network_info.branch[chain] ])
    IN /\ network_info' = [ network_info EXCEPT
            !.sent[chain][to] = Send(@, msg), \* [sys] sends current branch
            !.sysmsgs[chain] = Tail(@) ]      \* [sys] consumes message
       /\ UNCHANGED node_info

\* [from] sends current head to [to] on [chain]
Send_head(from, chain, to, params) ==
    LET branch == params.branch
        msg    == Msg(from, to, "Current_head",
                     [ branch |-> branch, height |-> current_height[from, chain, branch] ])
\*        ack    == AckMsg(from, "Ack_current_head")
    IN /\ network_info' = [ network_info EXCEPT !.sent[chain][to] = Send(@, msg) ] \* [from] sends current head
       /\ node_info' = [ node_info EXCEPT
            !.messages[from][chain] = Tail(@) ] \* [from] consumes message
\*            !.expect[from][chain] = Expect(@, to, ack) ] \* expect ack from [to]

\* [sys] sends current head to [to] on [chain]
Send_head_sys(chain, to, params) ==
    LET branch == params.branch
        msg    == Msg(sys, to, "Current_head",
                     [ branch |-> branch, height |-> currentHeight[chain, branch] ])
    IN /\ network_info' = [ network_info EXCEPT
            !.sent[chain][to] = Send(@, msg), \* [sys] sends current head
            !.sysmsgs[chain] = Tail(@) ]      \* [sys] consumes message
       /\ UNCHANGED node_info

\* [from] sends requested block header or error to [to] on [chain]
Send_header(from, chain, to, params) ==
    LET branch == params.branch
        height == params.height
        blocks == node_info.blocks[from][chain][branch]
    IN CASE \* [from] has seen a block at the requested [height]
            height \in { block.header.height : block \in ToSet(blocks) } ->
              LET atHeight(b) == b.header.height = height
                  header == Select(blocks, atHeight).header
                  msg_ps == [ branch |-> branch, height |-> height, header |-> header ]
                  msg    == Msg(from, to, "Block_header", msg_ps)
\*                  ack    == AckMsg(to, "Ack_block_header")
              IN /\ network_info' = [ network_info EXCEPT !.sent[chain][to] = Send(@, msg) ]
                 /\ node_info' = [ node_info EXCEPT
\*                      !.expect[from][chain] = Expect(@, to, ack), \* [from] expects ack from [to]
                      !.messages[from][chain] = Tail(@) ]         \* [from] consumes message
         [] OTHER -> \* [from] has not seen a block at [height]
              LET err == ErrMsg(from, to, "Err_block_header", params)
              IN /\ network_info' = [ network_info EXCEPT !.sent[chain][to] = Send(@, err) ] \* send error
                 /\ node_info' = [ node_info EXCEPT !.messages[from][chain] = Tail(@) ]      \* consume

\* [sys] sends requested block header or error to [to] on [chain]
Send_header_sys(chain, to, params) ==
    LET branch == params.branch
        height == params.height
        blocks == network_info.blocks[chain][branch]
    IN /\ CASE \* [sys] has seen a block at the requested [height]
               height <= currentHeight[chain, branch] ->
                 LET atHeight(b) == b.header.height = height
                     header == Select(blocks, atHeight).header
                     msg_ps == [ branch |-> branch, height |-> height, header |-> header ]
                     msg    == Msg(sys, to, "Block_header", msg_ps)
                 IN network_info' = [ network_info EXCEPT
                      !.sent[chain][to] = Send(@, msg), \* [sys] sends block header
                      !.sysmsgs[chain] = Tail(@) ]      \* [sys] consumes message
            [] OTHER -> \* [sys] has not seen a block at [height]
                 LET err == ErrMsg(sys, to, "Err_block_header", params) 
                 IN network_info' = [ network_info EXCEPT
                      !.sent[chain][to] = Send(@, err), \* [sys] sends error
                      !.sysmsgs[chain] = Tail(@) ]      \* [sys] consumes message
       /\ UNCHANGED node_info

\* [from] sends requested block operations or error to [to] on [chain]
Send_operations(from, chain, to, params) ==
    LET branch == params.branch
        height == params.height
        blocks == node_info.blocks[from][chain][branch]
    IN CASE \* [from] has seen the requested block
            height \in { block.header.height : block \in ToSet(blocks) } ->
            LET atHeight(b) == b.header.height = height
                ops == Select(blocks, atHeight).ops
                msg == Msg(from, to, "Operations", [ branch |-> branch, height |-> height, ops |-> ops ])
\*                ack == AckMsg(to, "Ack_operations")
            IN
              /\ network_info' = [ network_info EXCEPT !.sent[chain][to] = Send(@, msg) ]     \* [from] sends operations
              /\ node_info' = [ node_info EXCEPT
\*                   !.expect[from][chain] = Expect(@, to, ack), \* [from] expects ack from [to]
                   !.messages[from][chain] = Tail(@) ]         \* [from] consumes message
            \* [from] has not seen the requested block
         [] OTHER ->
              LET err == ErrMsg(from, to, "Err_operations", params)
              IN /\ network_info' = [ network_info EXCEPT !.sent[chain][to] = Send(@, err) ] \* send error
                 /\ node_info' = [ node_info EXCEPT !.messages[from][chain] = Tail(@) ]      \* consume

\* [sys] sends requested block operations or error to [to] on [chain]
Send_operations_sys(chain, to, params) ==
    LET branch == params.branch
        height == params.height
        blocks == network_info.blocks[chain][branch]
    IN /\ CASE \* [from] has seen the requested block
               height \in { block.header.height : block \in ToSet(blocks) } ->
                 LET atHeight(b) == b.header.height = height
                     ops == Select(blocks, atHeight).ops
                     msg == Msg(sys, to, "Operations", [ branch |-> branch, height |-> height, ops |-> ops ])
                 IN network_info' = [ network_info EXCEPT
                      !.sent[chain][to] = Send(@, msg), \* [sys] sends operations
                      !.sysmsgs[chain] = Tail(@) ]      \* [sys] consumes message
            [] OTHER -> \* [sys] has not seen a block at [height]
                 LET err == ErrMsg(sys, to, "Err_operations", params)
                 IN network_info' = [ network_info EXCEPT
                      !.sent[chain][to] = Send(@, err), \* [sys] sends error
                      !.sysmsgs[chain] = Tail(@) ]      \* [sys] consumes message
       /\ UNCHANGED node_info

\* Handle a request message
Handle_request(node, chain, from, type, params) ==
    CASE DOMAIN params = { "chain" } /\ type = "Get_current_branch" ->
           ifSys(node, Send_branch_sys(chain, from), Send_branch(node, chain, from))
      [] DOMAIN params = { "branch" } /\ type = "Get_current_head" ->
           ifSys(node, Send_head_sys(chain, from, params), Send_head(node, chain, from, params))
      [] DOMAIN params = { "branch", "height" } /\ type = "Get_block_header" ->
           ifSys(node,
             Send_header_sys(chain, from, params),
             Send_header(node, chain, from, params))
      [] DOMAIN params = { "branch", "height" } /\ type = "Get_operations" ->
           ifSys(node,
             Send_operations_sys(chain, from, params),
             Send_operations(node, chain, from, params))

\* [node] handles [msg] on [chain]
Handle(node, chain, msg) ==
    LET type == msg.type
    IN CASE \* Request messages
            type \in ReqMsgTypes -> Handle_request(node, chain, msg.from, type, msg.params)
            \* Advertise messages
         [] type \in AdMsgTypes  -> Handle_advertise(node, chain, msg.from, type, msg.params)
            \* Acknowledgment messages
         [] type \in AckMsgTypes -> Handle_ack(node, chain, msg)
            \* Error messages
         [] type \in ErrMsgTypes -> Handle_err(node, chain, msg)

\* A node handles a message from an active node on some chain
Handle_active_msg ==
    \E chain \in activeChains :
        \E receiver \in activeNodes[chain] :
            \E sender \in activeSysNodes[chain] \ {receiver} : 
                LET msgs == node_info.messages[receiver][chain]
                IN /\ msgs /= <<>>                       \* [receiver] has a message on [chain]
                   /\ LET msg == Head(msgs)
                      IN /\ sender = msg.from            \* [sender] is active on [chain]
                         /\ Handle(receiver, chain, msg) \* [receiver] handles a message on [chain]

Handle_inactive_msg ==
    \* An active node drops a message from an inactive node on some chain
    \/ \E chain \in activeChains :
           \E receiver \in activeNodes[chain] :
               \E sender \in Nodes \ activeNodes[chain] :
                   LET msgs == node_info.messages[receiver][chain]
                   IN /\ msgs /= <<>>
                      /\ sender = Head(msgs).from
                      /\ node_info' = [ node_info EXCEPT !.messages[receiver][chain] = Tail(@) ]
                      /\ UNCHANGED network_info
    \* [sys] drops a message from an inactive node on some chain
    \/ \E chain \in activeChains :
          \E sender \in Nodes \ activeNodes[chain] :  \* [sender] is inactive on [chain]
              LET msgs == network_info.sysmsgs[chain]
              IN /\ msgs /= <<>>
                 /\ sender = Head(msgs).from
                 /\ network_info' = [ network_info EXCEPT !.sysmsgs[chain] = Tail(@) ]
                 /\ UNCHANGED node_info

\* [sys] handles a message from an active node on some chain
Sys_handle_msg ==
    \E chain \in activeChains :
        \E sender \in activeNodes[chain] : 
            LET msgs == network_info.sysmsgs[chain]
            IN /\ msgs /= <<>>                    \* [sys] has a message on [chain]
               /\ LET msg == Head(msgs)
                  IN /\ sender = msg.from        \* [sender] is active on [chain]
                     /\ msg.type \in ReqMsgTypes \* message is a request
                     /\ Handle(sys, chain, msg)  \* [sys] handles a message on [chain]

\* Handle message action
Handle_msg ==
    \/ Handle_active_msg   \* an active node handles a message from an active node
    \/ Handle_inactive_msg \* an active node handles a message from an inactive node
    \/ Sys_handle_msg      \* system handles a message from a node

----------------------------------------------------------------------------

(**************)
(* Send again *)
(**************)

\* A node sends a message, for which they have not seen a response, again
Send_again ==
    \E chain \in activeChains :
        \E node \in activeNodes[chain] :
            \E exp \in node_info.expect[node][chain] :
                /\ network_info' = [ network_info EXCEPT
                     !.sent[chain][exp.from] = Send(@, exp) ] \* send corresponding msg again
                /\ UNCHANGED node_info

=============================================================================
