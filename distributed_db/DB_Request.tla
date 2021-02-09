---------------------------- MODULE DB_Request -----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES node_active, node_blocks, node_branches, node_headers, node_height, node_incoming, node_sent,
          active, blocks, branch, chains, mailbox, height, sysmsgs

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE DB_Messages
LOCAL INSTANCE Utils

----------------------------------------------------------------------------

(**********************)
(* Get_current_branch *)
(**********************)
\* [from] requests the current branch of [chain] from active peer [to]
Get_current_branch_1(from, chain, to) ==
    LET msg == Msg(from, to, "Get_current_branch", [ chain |-> chain ])
    IN /\ Send(from, chain, msg)
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches,
                      node_headers, node_height, node_incoming>>

\* A node requests the current branch on a chain from an active peer
Get_current_branch_one ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \E to \in active[chain] \ {from} :
                \* [from] doesn't know about an active branch on [chain]
                /\ branchSet[from, chain] /= activeBranches[chain]
                \* a message can be sent to [to]
                /\ checkMailbox[chain][to]
                \* [from] requests current branch of [chain] from [to]
                /\ Get_current_branch_1(from, chain, to)

\* [from] requests the current branch of [chain] from all active peers
\* Request message is sent to all active nodes on [chain] who can have a message sent to them
Get_current_branch_n(from, chain) ==
    LET msg == PartialMsg("Get_current_branch", [ chain |-> chain ])
    IN mailbox' = [ mailbox EXCEPT ![chain] = Broadcast(@, from, chain, msg) ]

\* A node requests the current branch of some chain from all active peers on the chain
Get_current_branch_all ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \* [from] doesn't know about an active branch on [chain]
            /\ branchSet[from, chain] /= activeBranches[chain]
            \* [from] requests current branches from all active nodes on [chain]
            /\ Get_current_branch_n(from, chain)
            /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
            /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                           node_height, node_incoming, node_sent>>

Get_curr_branch ==
    \/ Get_current_branch_one
    \/ Get_current_branch_all

(********************)
(* Get_current_head *)
(********************)
\* [from] requests the current head of branch [b] from an active peer [to] on [chain]
Get_current_head_1(from, chain, b, to) ==
    LET msg == Msg(from, to, "Get_current_head", [ branch |-> b ])
    IN /\ Send(from, chain, msg)
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches,
                      node_headers, node_height, node_incoming>>

\* A node who knows about a branch on a chain requests the current head from one active peer
Get_current_head_one ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \E to \in active[chain] \ {from} :
                /\ checkMailbox[chain][to] \* a message can be sent to [to]
                /\ \E b \in branchSet[from, chain] :
                       \* [from] has not seen evidence of a block on [b]
                       /\ node_height[from][chain][b] < height[chain][b]
                       \* [from] requests current head of [b] from [to]
                       /\ Get_current_head_1(from, chain, b, to)

\* [from] requests the current head of branch [b] from all active nodes on [chain]
Get_current_head_n(from, chain, b) ==
    LET msg == PartialMsg("Get_current_head", [ branch |-> b ])
    IN mailbox' = [ mailbox EXCEPT ![chain] = Broadcast(@, from, chain, msg) ]

\* A node who knows about branches on a chain requests the current head from all active peers on that chain
Get_current_head_all ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \E b \in branchSet[from, chain] :
               /\ node_height[from][chain][b] < height[chain][b]
               \* [from] requests current head of [b] from all active nodes on [chain]
               /\ Get_current_head_n(from, chain, b)
               /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
               /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                              node_height, node_incoming, node_sent>>

Get_curr_head ==
    \/ Get_current_head_one
    \/ Get_current_head_all

(********************)
(* Get_block_header *)
(********************)
\* [from] requests the header of the block branch [b] at [height] from an active peer [to] on [chain]
Get_block_header_1(from, chain, b, h, to) ==
    LET msg == Msg(from, to, "Get_block_header", [ branch |-> b, height |-> h ])
    IN /\ Send(from, chain, msg)
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches,
                      node_headers, node_height, node_incoming>>

\* A node requests a block header on some branch at some height from an active peer on some chain
Get_block_header_one ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \E to \in activeNodes[chain] \ {from} :
                /\ checkMailbox[chain][to] \* a message can be sent to [to]
                /\ \E b \in branchSet[from, chain] :
                       \* there are blocks which [from] has not seen
                       /\ currentHeights(chain, b) \ heightSet[from, chain, b] /= {}
                       /\ LET h == min_set(currentHeights(chain, b) \ heightSet[from, chain, b])
                          IN \* [from] knows about a block at height [h] but has not gotten a header
                             /\ h <= node_height[from][chain][b]
                             /\ Get_block_header_1(from, chain, b, h, to) \* request header from [to]

\* [from] requests the header of the block branch [b] at [height] from all active peers on [chain]
Get_block_header_n(from, chain, b, h) ==
    LET msg == PartialMsg("Get_block_header", [ branch |-> b, height |-> h ])
    IN mailbox' = [ mailbox EXCEPT ![chain] = Broadcast(@, from, chain, msg) ]
 
\* A node requests the header of a block on some branch at some height from all active peers on some chain
Get_block_header_all ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \E b \in branchSet[from, chain] :
                \* there are blocks which [from] has not seen
                /\ currentHeights(chain, b) \ heightSet[from, chain, b] /= {}
                /\ LET h == min_set(currentHeights(chain, b) \ heightSet[from, chain, b])
                   IN \* [from] knows about a block at height [h] but has not gotten a header
                      /\ h <= node_height[from][chain][b]
                      /\ Get_block_header_n(from, chain, b, h) \* request header from active
                      /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
                      /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                                     node_height, node_incoming, node_sent>>

Get_block_header ==
    \/ Get_block_header_one
    \/ Get_block_header_all

(******************)
(* Get_operations *)
(******************)
\* The requester must have the block's header before requesting its operations
\* [from] requests the operations of the block on [b] at [h] on [chain] from active peer [to]
Get_operations_1(from, chain, b, h, to) ==
    LET msg == Msg(from, to, "Get_operations", [ branch |-> b, height |-> h ])
    IN /\ Send(from, chain, msg)
       /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
       /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers, node_height, node_incoming>>

\* A node requests the operations of a block on a chain from an active peer who can have a message sent to them
Get_operations_one ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            \E to \in activeNodes[chain] \ {from} :
                /\ checkMailbox[chain][to] \* a message can be sent to [to]
                /\ LET headers == node_headers[from][chain]
                   IN /\ headers /= <<>>  \* [from] has a block's header and needs its operations
                      /\ LET b == Head(headers).branch
                             h == Head(headers).height
                         IN Get_operations_1(from, chain, b, h, to) \* send Get_operations request

\* [from] requests the operations of the block on branch [b] height [h] from all active peers on [chain]
\* Request message is sent to all active nodes on [chain] who can have a message sent to them
Get_operations_n(from, chain, b, h) ==
    LET msg == PartialMsg("Get_operations", [ branch |-> b, height |-> h ])
    IN mailbox' = [ mailbox EXCEPT ![chain] = Broadcast(@, from, chain, msg) ]

\* A node requests the operations of a block on a chain from all active peers who can have a message sent to them
Get_operations_all ==
    \E chain \in activeChains :
        \E from \in activeNodes[chain] :
            LET headers == node_headers[from][chain]
            IN /\ headers /= <<>>  \* [from] has a block's header and needs its operations
               /\ LET b == Head(headers).branch
                      h == Head(headers).height
                  IN /\ Get_operations_n(from, chain, b, h)
                     /\ UNCHANGED <<active, blocks, branch, chains, height, sysmsgs>>
                     /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers,
                                    node_height, node_incoming, node_sent>>

Get_operations ==
    \/ Get_operations_one
    \/ Get_operations_all

=============================================================================
