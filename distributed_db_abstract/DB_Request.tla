---------------------------- MODULE DB_Request -----------------------------

(**********************************)
(* Messages are implicitly passed *)
(**********************************)

CONSTANTS numChains, sizeBound

VARIABLES
    blocks, branch, chains, height,
    node_active, node_blocks, node_branches, node_headers, node_height

INSTANCE DB_Defs

----------------------------------------------------------------------------

(**********************)
(* Get_current_branch *)
(**********************)

\* node learns about the current branch of [chain]
Get_curr_branch(chain) ==
    /\ node_branches' = [ node_branches EXCEPT ![chain] = insertBranch(branch[chain], @) ]
    /\ UNCHANGED <<blocks, branch, chains, height>>
    /\ UNCHANGED <<node_active, node_blocks, node_headers, node_height>>

Get_current_branch ==
    \E chain \in activeChains :
        /\ active[chain]
        /\ Len(node_branches[chain]) < sizeBound
        /\ Get_curr_branch(chain)

(********************)
(* Get_current_head *)
(********************)

\* node learns about the current head of branch [b] on [chain]
Get_curr_head(chain, b) ==
    /\ node_height' = [ node_height EXCEPT ![chain][b] = height[chain][b] ]
    /\ UNCHANGED <<blocks, branch, chains, height>>
    /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers>>

Get_current_head ==
    \E chain \in activeChains :
        \E b \in activeBranches[chain] :
           /\ height[chain][b] >= 0
           /\ active[chain]
           /\ node_height[chain][b] /= height[chain][b]
           /\ Get_curr_head(chain, b)

(********************)
(* Get_block_header *)
(********************)

\* node learns about the header for the block at height [h] on branch [b] of [chain]
Get_block_header_(chain, b, h) ==
    /\ h \in { blk.header.height : blk \in ToSet(blocks[chain][b]) }
    /\ LET hdr == blockAtHeight(chain, b, h).header IN
        /\ node_headers' = [ node_headers EXCEPT ![chain][b] = insertHeader(hdr, @) ]
        /\ UNCHANGED <<blocks, branch, chains, height>>
        /\ UNCHANGED <<node_active, node_blocks, node_branches, node_height>>

\* A node requests a block header on some branch at some height from an active peer on some chain
Get_block_header ==
    \E chain \in activeChains :
        /\ active[chain]
        /\ \E b \in branchSet[chain] :
            \* there are blocks which node has not seen
            /\ currentHeights(chain, b) \ heightSet[chain, b] /= {}
            /\ LET h == min_set(currentHeights(chain, b) \ heightSet[chain, b]) IN
                \* [from] knows about a block at height [h] but has not gotten a header
                /\ h <= node_height[chain][b]
                /\ Get_block_header_(chain, b, h)

(******************)
(* Get_operations *)
(******************)

\* The requester must have the block's header before requesting its operations
\* [from] requests the operations of the block on [b] at [h] on [chain] from active peer [to]
Get_operations_1(from, chain, b, h, to) ==
    LET msg == Msg(from, to, "Get_operations", [ branch |-> b, height |-> h ])
    IN /\ msg \notin ToSet(mailbox[chain][to])
       /\ Send(from, chain, msg)
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

=============================================================================
