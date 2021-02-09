----------------------------- MODULE DB_Handle ------------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES node_active, node_blocks, node_branches, node_headers, node_height, node_incoming, node_sent,
          active, blocks, branch, chains, mailbox, height, sysmsgs

LOCAL INSTANCE DB_Activation
LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages
LOCAL INSTANCE DB_Request
LOCAL INSTANCE Utils

----------------------------------------------------------------------------

\* [node] handles advertised current branch [b] on [chain] from [from]
Handle_branch(node, peer, chain, b) ==
    LET ack == AckMsg(node, peer, "Ack_current_branch")
        bgb == PartialMsg("Get_current_branch", [ chain |-> chain ])
        acb == Msg(node, peer, "Current_branch", [ branch |-> current_branch[node, chain] ])
        gch == Msg(node, peer, "Get_current_head", [ branch |-> b ])
        bgh == PartialMsg("Get_current_head", [ branch |-> b ])
        mlb == [ mailbox EXCEPT ![chain][peer] = checkAppend(@, ack) ]
    IN /\ CASE b < 0 ->
               IF current_branch[node, chain] < 0
               THEN \* send [peer] ack & broadcast Get_current_branch
                 /\ mailbox' = [ mlb EXCEPT ![chain] = Broadcast(@, node, chain, bgb) ]
                 /\ UNCHANGED <<node_sent, node_branches>>
               ELSE \* send [peer] ack & send [peer] Current_branch
                 /\ mailbox' = [ mlb EXCEPT ![chain][peer] = checkAppend(@, acb) ]
                 /\ node_sent' = [ node_sent EXCEPT ![node][chain] = checkCons(acb, @) ]
                 /\ UNCHANGED node_branches
            [] b \in branchSet[node, chain] -> \* send [peer] ack & send [peer] Get_current_head
               /\ mailbox' = [ mlb EXCEPT ![chain][peer] = checkAppend(@, gch) ]
               /\ node_sent' = [ node_sent EXCEPT ![node][chain] = checkCons(gch, @) ]
               /\ UNCHANGED node_branches
            [] OTHER -> \* send [peer] ack & broadcast Get_current_head
               /\ mailbox' = [ mlb EXCEPT ![chain] = Broadcast(@, node, chain, bgh) ]
               /\ node_branches' = [ node_branches EXCEPT ![node][chain] = insertBranch(b, @) ]
               /\ UNCHANGED node_sent
       \* everything except mailbox, node_branches, node_incoming, node_sent are unchanged
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_blocks, node_headers, node_height>>

\* [node] handles advertised current head of branch [b] on [chain] from [from]
Handle_head(node, peer, chain, b, h) ==
    LET ack == AckMsg(node, peer, "Ack_current_head")
        bgh == PartialMsg("Get_current_head", [ branch |-> b ])
        ach == Msg(node, peer, "Current_head",
                  [ branch |-> b, height |-> current_height[node, chain, b] ])
        bgb == PartialMsg("Get_block_header", [ branch |-> b, height |-> h ])
        gop == Msg(node, peer, "Get_operations", [ branch |-> b, height |-> h])
        gbh == Msg(node, peer, "Get_block_header", [ branch |-> b, height |-> h])
        mlb == [ mailbox EXCEPT ![chain][peer] = checkAppend(@, ack) ]
    IN /\ CASE h < 0 ->
               IF current_height[node, chain, b] < 0
               THEN IF b \notin branchSet[node, chain]
                    THEN \* send [peer] ack, insert branch & broadcast Get_current_head
                      /\ mailbox' = [ mlb EXCEPT ![chain] = Broadcast(@, node, chain, bgh) ]
                      /\ node_branches' = [ node_branches EXCEPT ![node][chain] = insertBranch(b, @) ]
                      /\ UNCHANGED <<node_height, node_sent>>
                    ELSE \* send [peer] ack & broadcast Get_current_head
                      /\ mailbox' = [ mlb EXCEPT ![chain] = Broadcast(@, node, chain, bgh) ]
                      /\ UNCHANGED <<node_branches, node_height, node_sent>>
               ELSE \* send [peer] ack & send [peer] Current_head
                 /\ mailbox' = [ mlb EXCEPT ![chain][peer] = checkAppend(@, ach) ]
                 /\ node_sent' = [ node_sent EXCEPT ![node][chain] = checkCons(ach, @) ]
                 /\ UNCHANGED <<node_branches, node_height>>
            [] b \notin branchSet[node, chain] ->
               \* send [peer] ack, upadate branches and height & broadcast Get_block_header
               /\ mailbox' = [ mlb EXCEPT ![chain] = Broadcast(@, node, chain, bgb) ]
               /\ node_branches' = [ node_branches EXCEPT ![node][chain] = insertBranch(b, @) ]
               /\ node_height' = [ node_height EXCEPT ![node][chain][b] = h ]
               /\ UNCHANGED node_sent
            [] current_height[node, chain, b] < h ->
               \* send [peer] ack, upadate height & broadcast Get_block_header
               /\ mailbox' = [ mlb EXCEPT ![chain] = Broadcast(@, node, chain, bgb) ]
               /\ node_height' = [ node_height EXCEPT ![node][chain][b] = h ]
               /\ UNCHANGED <<node_branches, node_sent>>
            [] OTHER ->
               CASE h \in blockHeights[node, chain, b] ->
                    \* send [peer] ack
                    /\ mailbox' = mlb
                    /\ UNCHANGED <<node_branches, node_height, node_sent>>
                 [] h \in headerHeights[node, chain, b] ->
                    \* send [peer] ack & send [peer] Get_operations
                    /\ mailbox' = [ mlb EXCEPT ![chain][peer] = checkAppend(@, gop) ]
                    /\ node_sent' = [ node_sent EXCEPT ![node][chain] = checkCons(gop, @) ]
                    /\ UNCHANGED <<node_branches, node_height>>
                 [] OTHER ->
                    \* send [peer] ack & broadcast Get_block_header
                    /\ mailbox' = [ mlb EXCEPT ![chain] = Broadcast(@, node, chain, bgb) ]
                    /\ UNCHANGED <<node_branches, node_height, node_sent>>
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_blocks, node_headers>>

\* nodes only receive Block_header advertisements upon request
\* [node] handles the advertised [header] on branch [b] of [chain] from [from]
Handle_header(node, peer, chain, hdr) ==
    LET b   == hdr.branch
        h   == hdr.height
        ack == AckMsg(node, node, "Ack_block_header")
        bgo == PartialMsg("Get_operations", [ branch |-> b, height |-> h ])
        mlb == [ mailbox EXCEPT ![chain][peer] = checkAppend(@, ack) ]
    IN \* send [peer] ack & broadcast Get_operations
       /\ mailbox' = [ mlb EXCEPT ![chain] = Broadcast(@, node, chain, bgo) ] \* 
       /\ node_headers' = [ node_headers EXCEPT ![node][chain] = checkInsertHeader(hdr, @) ] \* update headers
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_branches, node_blocks, node_height, node_sent>>

\* nodes only receive Operations advertisements upon request
\* [node] handles advertised [ops] on [branch] of [chain] from [from]
Handle_ops(node, peer, chain, b, h, ops) ==
    LET hdr == Header(chain, b, h)
        ack == AckMsg(node, peer, "Ack_operations")
        blk == Block(hdr, ops)
    IN /\ mailbox' = [ mailbox EXCEPT ![chain][peer] = checkAppend(@, ack) ]            \* send ack
       /\ node_blocks' = [ node_blocks EXCEPT ![node][chain][b] = insertBlock(blk, @) ] \* update blocks
       /\ node_headers' = [ node_headers EXCEPT ![node][chain] = Remove(@, hdr) ]       \* update headers
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_branches, node_height, node_sent>>

\* node or sys handles an ack [msg] on [chain]
Handle_ack(node, chain, msg) ==
    IF node = sys
    THEN UNCHANGED vars
    ELSE /\ ManageSent(node, chain, msg)
         /\ UNCHANGED <<active, blocks, branch, chains, height, mailbox, sysmsgs>>
         /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers, node_height>>

\* Handle advertise message
Handle_adv(node, chain, from, type, params) ==
    CASE /\ DOMAIN params = { "branch" }
         /\ type = "Current_branch" -> Handle_branch(node, from, chain, params.branch)
      [] /\ DOMAIN params = { "branch", "height" }
         /\ type = "Current_head" -> Handle_head(node, from, chain, params.branch, params.height)
      [] /\ DOMAIN params = { "branch", "height", "header" }
         /\ type = "Block_header" -> Handle_header(node, from, chain, params.header)
      [] /\ DOMAIN params = { "branch", "height", "ops" }
         /\ type = "Operations" -> Handle_ops(node, from, chain, params.branch, params.height, params.ops)

\* [node] handles an error msg on [chain]
Handle_err(node, chain, err) ==
    /\ ManageSent(node, chain, err)
    /\ UNCHANGED <<active, blocks, branch, chains, height, mailbox, sysmsgs>>
    /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers, node_height>>

\* [from] sends current branch to [to] on [chain]
Send_branch(from, chain, to) ==
    LET msg == Msg(from, to, "Current_branch", [ branch |-> current_branch[from, chain] ])
    IN /\ Send(from, chain, msg)
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers, node_height>>

\* [sys] sends current branch to [to] on [chain]
Send_branch_sys(chain, to) ==
    LET msg == Msg(sys, to, "Current_branch", [ branch |-> branch[chain] ])
    IN /\ Send(sys, chain, msg)
       /\ UNCHANGED <<active, blocks, branch, chains, height>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                      node_height, node_incoming, node_sent>>

\* [from] sends current head to [to] on [chain]
Send_head(from, chain, to, params) ==
    LET b   == params.branch
        msg == Msg(from, to, "Current_head",
                  [ branch |-> b, height |-> current_height[from, chain, b] ])
    IN /\ Send(from, chain, msg)
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers, node_height>>

\* [sys] sends current head to [to] on [chain]
Send_head_sys(chain, to, params) ==
    LET b   == params.branch
        msg == Msg(sys, to, "Current_head",
                  [ branch |-> b, height |-> height[chain][b] ])
    IN /\ Send(sys, chain, msg)
       /\ UNCHANGED <<active, blocks, branch, chains, height>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                      node_height, node_incoming, node_sent>>

\* [from] sends requested block header or error to [to] on [chain]
Send_header(from, chain, to, params) ==
    LET b == params.branch
        h == params.height
        blks == node_blocks[from][chain][b]
    IN CASE \* [from] has seen a block at the requested height [h]
            h \in { block.header.height : block \in ToSet(blks) } ->
              LET atHeight(blk) == blk.header.height = h
                  hdr == Select(blks, atHeight).header
                  mps == [ branch |-> b, height |-> h, header |-> hdr ]
                  msg == Msg(from, to, "Block_header", mps)
              IN /\ Send(from, chain, msg)
                 /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
                 /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers, node_height>>
            \* [from] has not seen a block at height [h]
         [] OTHER ->
              LET err == ErrMsg(from, to, "Err_block_header", params)
              IN /\ SendNoRecord(from, chain, err)
                 /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
                 /\ UNCHANGED <<node_active, node_blocks, node_branches,
                                node_headers, node_height, node_sent>>

\* [sys] sends requested block header or error to [to] on [chain]
Send_header_sys(chain, to, params) ==
    LET b == params.branch
        h == params.height
        blks == blocks[chain][b]
    IN /\ CASE \* [sys] has seen a block at the requested height [h]
               h <= height[chain][b] ->
                 LET atHeight(blk) == blk.header.height = h
                     hdr == Select(blks, atHeight).header
                     mps == [ branch |-> b, height |-> h, header |-> hdr ]
                     msg == Msg(sys, to, "Block_header", mps)
                 IN SendNoRecord(sys, chain, msg)
               \* [sys] has not seen a block at height [h]
            [] OTHER ->
                 LET err == ErrMsg(sys, to, "Err_block_header", params) 
                 IN SendNoRecord(sys, chain, err)
       /\ UNCHANGED <<active, blocks, branch, chains, height>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                      node_height, node_incoming, node_sent>>

\* [from] sends requested block operations or error to [to] on [chain]
Send_operations(from, chain, to, params) ==
    LET b == params.branch
        h == params.height
        blks == node_blocks[from][chain][b]
    IN CASE \* [from] has seen the requested block
            h \in { block.header.height : block \in ToSet(blks) } ->
              LET atHeight(blk) == blk.header.height = h
                  ops == Select(blks, atHeight).ops
                  msg == Msg(from, to, "Operations", [ branch |-> b, height |-> h, ops |-> ops ])
              IN /\ Send(sys, chain, msg)
                 /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
                 /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers, node_height>>
            \* [from] has not seen a block at height [h]
         [] OTHER ->
              LET err == ErrMsg(from, to, "Err_operations", params)
              IN /\ SendNoRecord(sys, chain, err)
                 /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
                 /\ UNCHANGED <<node_active, node_blocks, node_branches,
                                node_headers, node_height, node_sent>>

\* [sys] sends requested block operations or error to [to] on [chain]
Send_operations_sys(chain, to, params) ==
    LET b == params.branch
        h == params.height
        blks == blocks[chain][b]
    IN /\ CASE \* [sys] has seen the requested block
               h \in { block.header.height : block \in ToSet(blks) } ->
                 LET atHeight(blk) == blk.header.height = h
                     ops == Select(blks, atHeight).ops
                     msg == Msg(sys, to, "Operations", [ branch |-> b, height |-> h, ops |-> ops ])
                 IN Send(sys, chain, msg)
               \* [sys] has not seen a block at height [h]
            [] OTHER ->
                 LET err == ErrMsg(sys, to, "Err_operations", params)
                 IN SendNoRecord(sys, chain, err)
       /\ UNCHANGED <<active, blocks, branch, chains, height>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                      node_height, node_incoming, node_sent>>

\* Handle a request message
Handle_req(node, chain, from, type, params) ==
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
    IN /\ CASE \* Request messages
               type \in ReqMsgTypes -> Handle_req(node, chain, msg.from, type, msg.params)
               \* Advertise messages
            [] type \in AdvMsgTypes -> Handle_adv(node, chain, msg.from, type, msg.params)
               \* Acknowledgment messages
            [] type \in AckMsgTypes -> Handle_ack(node, chain, msg)
               \* Error messages
            [] type \in ErrMsgTypes -> Handle_err(node, chain, msg)
       /\ Consume(node, chain)

\* A node handles a message from an active node on some chain
Handle_active_msg ==
    \E chain \in activeChains :
        \E rcvr \in activeNodes[chain] :
            \E sndr \in active[chain] \ {rcvr} : 
                LET msgs == node_incoming[rcvr][chain]
                IN /\ msgs /= <<>>                   \* [rcvr] has a message on [chain]
                   /\ LET msg == Head(msgs)
                      IN /\ sndr = msg.from          \* [sndr] is active on [chain]
                         /\ Handle(rcvr, chain, msg) \* [rcvr] handles a message on [chain]

Handle_inactive_msg ==
    \* An active node drops a message from an inactive node on some chain
    \/ \E chain \in activeChains :
           \E rcvr \in activeNodes[chain] :
               \E sndr \in inactiveNodes[chain] :
                   LET msgs == node_incoming[rcvr][chain]
                   IN /\ msgs /= <<>>
                      /\ sndr = Head(msgs).from
                      /\ Consume(rcvr, chain)
                      /\ UNCHANGED <<active, blocks, branch, chains, height, mailbox, sysmsgs>>
                      /\ UNCHANGED <<node_active, node_blocks, node_branches,
                                     node_headers, node_height, node_sent>>
    \* [sys] drops a message from an inactive node on some chain
    \/ \E chain \in activeChains :
          \E sndr \in inactiveNodes[chain] :  \* [sndr] is inactive on [chain]
              LET msgs == sysmsgs[chain]
              IN /\ msgs /= <<>>
                 /\ sndr = Head(msgs).from
                 /\ Consume(sys, chain)
                 /\ UNCHANGED <<active, blocks, branch, chains, height, mailbox>>
                 /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                                node_height, node_incoming, node_sent>>

\* [sys] handles a message from an active node on some chain
Sys_handle_msg ==
    \E chain \in activeChains :
        \E sndr \in activeNodes[chain] : 
            LET msgs == sysmsgs[chain]
            IN /\ msgs /= <<>>                    \* [sys] has a message on [chain]
               /\ LET msg == Head(msgs)
                  IN /\ sndr = msg.from        \* [sender] is active on [chain]
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
            \E msg \in sentSet[node, chain] :
                /\ SendNoRecord(node, chain, msg)
                /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
                /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers, node_height, node_incoming, node_sent>>

=============================================================================
