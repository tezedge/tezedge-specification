---------------------------- MODULE DB_Request -----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages
LOCAL INSTANCE Utils

----------------------------------------------------------------------------

(*******************)
(* Request actions *)
(*******************)

(* Messages are sent to a set where the receipient can receive or drop them later *)

(**********************)
(* Get_current_branch *)
(**********************)
\* [from] requests the current branch of [chain] from active peer [to]
Get_current_branch_1(from, chain, to) ==
    LET msg == Msg(from, "Get_current_branch", [ chain |-> chain ])
    IN
      /\ network_info' = Send(to, chain, msg) \* send [msg] to [to]
      /\ node_info' = Expect(to, chain, msg)  \* register expected response if possible

\* A node requests the current branch on a chain from an active peer who can have a message sent to them
Get_current_branch_one ==
    \E from \in Nodes, chain \in Chains :
        \E to \in network_info.active[chain] \ {from} :
            /\ checkSent[chain][to]                  \* check that [to] can have a message sent to them
            /\ Get_current_branch_1(from, chain, to) \* send Get_current_branch request

\* [from] requests the current branch of [chain] from all active peers
\* Request message is sent to all active nodes on [chain] who can have a message sent to them
Get_current_branch_n(from, chain) ==
    LET msg == Msg(from, "Get_current_branch", [ chain |-> chain ])
    IN
      /\ network_info' = BroadcastToActive(from, chain, msg) \* no expect message for a braodcast
      /\ UNCHANGED node_info

\* A node requests the current branch of some chain from all active peers on the chain
Get_current_branch_all ==
    \E from \in Nodes :
        \E chain \in node_info.active[from] :
            /\ network_info.active[chain] \ {from} # {} \* there are other active nodes on [chain]
            /\ Get_current_branch_n(from, chain)        \* [from] can request their current branches

(********************)
(* Get_current_head *)
(********************)
\* [from] requests the current head of [branch] from an active peer [to] on [chain]
Get_current_head_1(from, chain, branch, to) ==
    LET msg == Msg(from, "Get_current_head", [ branch |-> branch ])
    IN
      /\ network_info' = Send(to, chain, msg) \* send [msg] to [to]
      /\ node_info' = Expect(to, chain, msg)  \* register expected response if possible

\* A node who knows about branches on a chain requests the current head from one active peer on that chain
Get_current_head_one ==
    \E from \in Nodes :
        \E chain \in node_info.active[from] :
            \E to \in network_info.active[chain] \ {from} :
                LET branches == node_info.branches[from][chain]
                IN
                  /\ branches # <<>>                                     \* [from] knows about a branch on [chain]
                  /\ checkSent[chain][to]                                \* check if a message can be sent to [to]
                  /\ Get_current_head_1(from, chain, Head(branches), to) \* request current head from [to]

\* [from] requests the current head of [branch] from all active peers on [chain]
Get_current_head_n(from, chain, branch) ==
    LET msg == Msg(from, "Get_current_head", [ branch |-> branch ])
    IN
      /\ network_info' = BroadcastToActive(from, chain, msg) \* no expect message for a braodcast
      /\ UNCHANGED node_info

\* A node who knows about branches on a chain requests the current head from all active peers on that chain
Get_current_head_all ==
    \E from \in Nodes :
        \E chain \in node_info.active[from] :
            LET branches == node_info.branches[from][chain]
            IN
              /\ branches # <<>>                                 \* [from] knows about a branch on [chain]
              /\ network_info.active[chain] \ {from} # {}        \* there are other active nodes on [chain]
              /\ Get_current_head_n(from, chain, Head(branches)) \* request current head from all active nodes

(********************)
(* Get_block_header *)
(********************)
\* [from] requests the header of the block on [branch] at [height] from an active peer [to] on [chain]
Get_block_header_1(from, chain, branch, height, to) ==
    LET msg == Msg(from, "Get_block_header", [ branch |-> branch, height |-> height ])
    IN
      /\ network_info' = Send(to, chain, msg) \* [from] sends the [msg] to [to]
      /\ node_info' = Expect(to, chain, msg)  \* register expected response if possible

\* A node requests a block header on some branch at some height from an active peer on some chain
Get_block_header_one ==
    \E from \in Nodes :
        \E chain \in node_info.active[from] :
            \E to \in network_info.active[chain] \ {from} :
                LET branches == node_info.branches[from][chain]
                IN
                  /\ branches # <<>>      \* [from] knows about a branch on [chain]
                  /\ checkSent[chain][to] \* a message can be sent to [to]
                  /\ LET branch == Head(branches)
                         height ==
                           LET blocks == node_info.blocks[from][chain][branch]
                           IN
                             CASE blocks = <<>> -> 0                      \* if no blocks are known, get the first
                               [] OTHER -> Head(blocks).header.height + 1 \* request the next header
                     IN
                       Get_block_header_1(from, chain, branch, height, to)  \* request header from [to]

\* [from] requests the header of the block on [branch] at [height] from all active peers on [chain]
Get_block_header_n(from, chain, branch, height) ==
    LET msg == Msg(from, "Get_block_header", [ branch |-> branch, height |-> height ])
    IN
      /\ network_info' = BroadcastToActive(from, chain, msg) \* no expect message for a braodcast
      /\ UNCHANGED node_info
 
\* A node requests the header of the block on some branch at some height from all active peers on some chain
Get_block_header_all ==
    \E from \in Nodes :
        \E chain \in node_info.active[from] :
            LET branches == node_info.branches[from][chain]
            IN
              /\ branches # <<>>                          \* [from] knows about a branch on [chain]
              /\ network_info.active[chain] \ {from} # {} \* there are other active nodes on [chain]
              /\ LET branch == Head(branches)
                     height ==
                       LET blocks == node_info.blocks[from][chain][branch]
                       IN
                         CASE blocks = <<>> -> 0                      \* if no blocks are known, get the first
                           [] OTHER -> Head(blocks).header.height + 1 \* request the next header
                 IN
                   Get_block_header_n(from, chain, branch, height)    \* request header from [to]

(******************)
(* Get_operations *)
(******************)
\* The requester must have the block's header before requesting its operations
\* [from] requests the operations of the block on [branch] at [height] on [chain] from active peer [to]
Get_operations_1(from, chain, branch, height, to) ==
    LET msg == Msg(from, "Get_operations", [ branch |-> branch, height |-> height ])
    IN
      /\ network_info' = Send(to, chain, msg) \* send [msg] to [to]
      /\ node_info' = Expect(to, chain, msg)  \* register expected response if possible

\* A node requests the operations of a block on a chain from an active peer who can have a message sent to them
Get_operations_one ==
    \E from \in Nodes :
        \E chain \in node_info.active[from] :
            \E to \in network_info.active[chain] \ {from} :
                LET branches == node_info.branches[from][chain]
                IN
                  /\ branches # <<>>      \* [from] knows about a branch on [chain]
                  /\ checkSent[chain][to] \* a message can be sent to [to]
                  /\ LET branch  == Head(branches)
                         headers == node_info.headers[from][chain][branch]
                     IN
                       /\ headers # <<>>  \* [from] has a block's header and needs its operations
                       /\ LET height == Head(headers).height
                          IN
                            Get_operations_1(from, chain, branch, height, to) \* send Get_operations request

\* [from] requests the operations of the block on [branch] at [height] from all active peers on [chain]
\* Request message is sent to all active nodes on [chain] who can have a message sent to them
Get_operations_n(from, chain, branch, height) ==
    LET msg == Msg(from, "Get_operations", [ branch |-> branch, height |-> height ])
    IN
      /\ network_info' = BroadcastToActive(from, chain, msg) \* braodcast [msg] to active nodes on [chain]
      /\ UNCHANGED node_info

\* A node requests the operations of a block on a chain from all active peers who can have a message sent to them
Get_operations_all ==
    \E from \in Nodes :
        \E chain \in node_info.active[from] :
            LET branches == node_info.branches[from][chain]
            IN
              /\ branches # <<>>                          \* [from] knows about a branch on [chain]
              /\ network_info.active[chain] \ {from} # {} \* there are other active nodes on [chain]
              /\ LET branch  == Head(branches)
                         headers == node_info.headers[from][chain][branch]
                     IN
                       /\ headers # <<>>  \* [from] has a block's header and needs its operations
                       /\ LET height == Head(headers).height
                          IN
                            Get_operations_n(from, chain, branch, height)

----------------------------------------------------------------------------

\* Request multiple branch heads
\* used when a node receives a branch at a higher level than expected
Request_branch_heads(node, chain, branches) ==
    LET RECURSIVE Req_heads(_, _, _, _)
        Req_heads(n, c, bs, acc) ==
          CASE bs = {} -> acc
            [] OTHER ->
               LET b == Pick(bs)
                   m == Msg(n, "Get_current_head", [ branch |-> b ])
                   a == [ acc EXCEPT !.sent[chain] = [ to \in Nodes |->
                          LET curr == @[to]
                          IN
                            CASE to \in network_info.active[chain] \ {n} -> checkAdd(curr, m)
                              [] OTHER -> curr ] ]
               IN Req_heads(n, c, bs \ {b}, a)
    IN Req_heads(node, chain, branches, network_info)

\* Request multiple block headers
\* used when a node receives a block at a higher height than expected
Request_block_headers(node, chain, branch, block_heights) ==
    LET RECURSIVE Req_headers(_, _, _, _, _)
        Req_headers(n, c, b, heights, acc) ==
          CASE heights = {} -> acc
            [] OTHER ->
               LET h == Pick(heights)
                   m == Msg(n, "Get_block_header", [ branch |-> b, height |-> h ])
                   a == [ acc EXCEPT !.sent[chain] = [ to \in Nodes |->
                          LET curr == @[to]
                          IN
                            CASE to \in network_info.active[chain] \ {n} -> checkAdd(curr, m)
                              [] OTHER -> curr ] ]
               IN Req_headers(n, c, b, heights \ {h}, a)
    IN Req_headers(node, chain, branch, block_heights, network_info)

=============================================================================
