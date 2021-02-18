------------------------------ MODULE DB_Defs -------------------------------

EXTENDS Utils

CONSTANTS numChains, sizeBound

VARIABLES
    blocks, branch, chains, height,
    node_active, node_blocks, node_branches, node_headers, node_height

-----------------------------------------------------------------------------

(**********************************)
(* Definitions of ubiquitous sets *)
(**********************************)

\* static values
Chains == 1..numChains    \* chain ids

Branches == 0..sizeBound  \* branch ids

Heights == 0..sizeBound   \* block heights

Op_nums == 0..sizeBound   \* possible numbers of operations

\* dynamic values
activeChains == 1..chains

active[ chain \in Chains ] == chain \in node_active

activeBranches[ chain \in Chains ] == 0..branch[chain]

currentHeights(chain, b) == 0..height[chain][b]

branchSet[ chain \in Chains ] == ToSet(node_branches[chain])

\* set of all blocks node knows about on branch [b] of [chain]
blockSet(chain, b) == ToSet(node_blocks[chain][b])

headerSet(chain, b) == { h \in ToSet(node_headers[chain]) : h.branch = b }

\* heights of known blocks on branch [b] of [chain]
blockHeights[ chain \in Chains, b \in Branches ] == { blk.header.height : blk \in blockSet(chain, b) }

\* heights of the headers in node's list on branch [b] of [chain]
headerHeights[ chain \in Chains, b \in Branches ] == { h.height : h \in headerSet(chain, b) }

\* heights of known blocks and headers on branch [b] of [chain]
heightSet[ chain \in Chains, b \in Branches ] == blockHeights[chain, b] \cup headerHeights[chain, b]

\* set of all blocks that nodes know about on [chain]
allNodeBlocks(chain) == UNION { blockSet(chain, b) : b \in activeBranches[chain] }

\* set of all blocks on [chain]
allSysBlocks(chain) == UNION { ToSet(blocks[chain][b]) : b \in activeBranches[chain] }

-----------------------------------------------------------------------------

(***********************)
(* Blocks & Operations *)
(***********************)

\* The set of all block headers
Headers == [ height : Heights, chain : Chains, branch : Branches ]

\* The set of all block operations
Operations == Op_nums

\* The set of all blocks
Blocks == [ header : Headers, ops : Operations ]

\* Block "constructor"
Block(header, ops) == [ header |-> header, ops |-> ops ]

\* Header "constructor"
Header(chain, b, h) == [ chain |-> chain, branch |-> b, height |-> h ]

\* Operations "constructor"
mkOps(num_ops) == num_ops

\* header predicate
isHeader(h) == DOMAIN h = { "chain", "branch", "height" }

\* valid block predicate
isBlock(b) ==
    /\ DOMAIN b = { "header", "ops" }
    /\ isHeader(b.header)
    /\ b.ops \in Operations

\* selects a block on [b] of [chain] at [h]
\* set of blocks must be nonempty
blockAtHeight(chain, b, h) == Pick({ blk \in ToSet(blocks[chain][b]) : blk.header.height = h })

-----------------------------------------------------------------------------

(********************)
(* Helper functions *)
(********************)

\* get node's current branch on [chain]
current_branch[ chain \in Chains ] ==
    LET bs == node_branches[chain]
    IN CASE bs = <<>> -> -1
         [] OTHER -> Head(bs)

\* get node's current height on branch [b] of [chain]
current_height[ chain \in Chains, b \in Branches ] ==
    LET blks == node_blocks[chain][b]
    IN CASE blks = <<>> -> -1
         [] OTHER -> Head(blks).header.height

\* check that there is space for node to insert a header on [chain]
checkHeaders == [ chain \in Chains |-> Len(node_headers[chain]) < sizeBound ]

\* check that [queue] is not full before including the message at the end
checkAppend(queue, msg) ==
    CASE Len(queue) < sizeBound /\ msg \notin ToSet(queue) -> Append(queue, msg)
      [] OTHER -> queue

\* check that [stack] is not full before including [data] at the beginning
checkCons(data, stack) ==
    CASE Len(stack) < sizeBound /\ data \notin ToSet(stack) -> <<data>> \o stack
      [] OTHER -> stack

\* insert [header] into [headers]
\* smallest branches and heights first
insertHeader(header, headers) ==
    LET RECURSIVE aux(_, _, _)
        aux(h, hs, acc) ==
          CASE hs = <<>> -> Append(acc, h)
            [] OTHER ->
                 LET hd == Head(hs)
                 IN CASE h.branch < hd.branch -> acc \o Cons(h, hs)
                      [] OTHER ->
                         CASE h.branch /= hd.branch -> aux(h, Tail(hs), Append(acc, hd))
                           [] OTHER ->
                              CASE h.height < hd.height -> acc \o Cons(h, hs)
                                [] OTHER -> aux(h, Tail(hs), Append(acc, hd))
    IN CASE header \notin ToSet(headers) -> aux(header, headers, <<>>)
         [] OTHER -> headers

\* check that [headers] is not full before inserting [header]
checkInsertHeader(header, headers) ==
    CASE Len(headers) < sizeBound -> insertHeader(header, headers)
      [] OTHER -> headers

\* insert [blk] into [blks]
insertBlock(blk, blks) ==
    LET RECURSIVE aux(_, _, _)
        aux(b, bs, acc) ==
          CASE bs = <<>> -> Append(acc, b)
            [] OTHER ->
               LET hd        == Head(bs)
                   b_branch  == b.header.branch
                   b_height  == b.header.height
                   hd_branch == hd.header.branch
                   hd_height == hd.header.height
               IN
                 CASE b_branch > hd_branch -> acc \o <<b>> \o bs
                   [] OTHER ->
                      CASE b_branch /= hd_branch -> aux(b, Tail(bs), Append(acc, hd))
                        [] OTHER ->
                           CASE b_height > hd_height -> acc \o <<b>> \o bs
                             [] OTHER -> aux(b, Tail(bs), Append(acc, hd))
    IN CASE blk \notin ToSet(blks) -> aux(blk, blks, <<>>)
         [] OTHER -> blks

\* check that [blks] is not full before inserting [blk]
checkInsertBlock(blk, blks) ==
    CASE Len(blks) < sizeBound -> insertBlock(blk, blks)
      [] OTHER -> blks

\* insert a branch [b] into a sequence of [branches]
insertBranch(b, branches) ==
    LET RECURSIVE aux(_, _, _)
        aux(bb, bs, acc) ==
          CASE bs = <<>> -> Append(acc, bb)
            [] OTHER ->
                 LET hd == Head(bs)
                 IN CASE bb > hd -> acc \o <<bb>> \o bs
                      [] bb = hd -> acc \o bs
                      [] OTHER -> aux(bb, Tail(bs), Append(acc, hd))
    IN aux(b, branches, <<>>)

\* check that all [branches] are valid branches on [chain]
RECURSIVE checkBranches(_, _)
checkBranches(branches, chain) ==
    \/ branches = <<>>
    \/ /\ Head(branches) \in activeBranches[chain]
       /\ checkBranches(Tail(branches), chain)

=============================================================================
