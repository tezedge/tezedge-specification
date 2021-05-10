---------------------------- MODULE DB_Request -----------------------------

(**********************************)
(* Messages are implicitly passed *)
(**********************************)

EXTENDS DB_Defs

(**********************)
(* Get_current_branch *)
(**********************)

\* node learns about the current branch of [chain]
get_current_branch(chain) ==
    /\ node_branches' = [ node_branches EXCEPT ![chain] = insertBranch(branch[chain], @) ]
    /\ UNCHANGED <<blocks, branch, chains, height>>
    /\ UNCHANGED <<node_active, node_blocks, node_headers, node_height>>

Get_current_branch ==
    \E chain \in activeChains :
        /\ active[chain]
        /\ Len(node_branches[chain]) < sizeBound
        /\ get_current_branch(chain)

(********************)
(* Get_current_head *)
(********************)

\* node learns about the current head of branch [b] on [chain]
get_current_head(chain, b) ==
    /\ node_height' = [ node_height EXCEPT ![chain][b] = height[chain][b] ]
    /\ UNCHANGED <<blocks, branch, chains, height>>
    /\ UNCHANGED <<node_active, node_blocks, node_branches, node_headers>>

Get_current_head ==
    \E chain \in activeChains :
        \E b \in activeBranches[chain] :
           /\ height[chain][b] >= 0
           /\ active[chain]
           /\ node_height[chain][b] /= height[chain][b]
           /\ get_current_head(chain, b)

(********************)
(* Get_block_header *)
(********************)

\* node learns about the header for the block at height [h] on branch [b] of [chain]
get_block_header(chain, b, h) ==
    /\ h \in { blk.header.height : blk \in ToSet(blocks[chain][b]) }
    /\ LET hdr == blockAtHeight(chain, b, h).header IN
        /\ node_headers' = [ node_headers EXCEPT ![chain] = insertHeader(hdr, @) ]
        /\ UNCHANGED <<blocks, branch, chains, height>>
        /\ UNCHANGED <<node_active, node_blocks, node_branches, node_height>>

\* node retrieves a block header on some branch at some height on some chain
Get_block_header ==
    \E chain \in activeChains :
        /\ active[chain]
        /\ \E b \in branchSet[chain] :
            \* there are blocks which node has not seen
            /\ currentHeights(chain, b) \ heightSet[chain, b] /= {}
            /\ LET h == min_set(currentHeights(chain, b) \ heightSet[chain, b]) IN
                /\ h <= node_height[chain][b]
                /\ get_block_header(chain, b, h)

(******************)
(* Get_operations *)
(******************)

\* node has a block header with height [h] on branch [b] of [chain]
get_operations(chain, hdr) ==
    LET b   == hdr.branch
        ops == blockAtHeight(chain, b, hdr.height).ops
        blk == Block(hdr, ops)
    IN
    /\ node_headers' = [ node_headers EXCEPT ![chain] = Tail(@) ]
    /\ node_blocks' = [ node_blocks EXCEPT ![chain][b] = insertBlock(blk, @) ]
    /\ UNCHANGED <<blocks, branch, chains, height>>
    /\ UNCHANGED <<node_active, node_branches, node_height>>

\* node retrieves the operations of a block for which they have a header
Get_operations ==
    \E chain \in activeChains :
        LET headers == node_headers[chain] IN
        /\ headers /= <<>>
        /\ get_operations(chain, Head(headers))

=============================================================================
