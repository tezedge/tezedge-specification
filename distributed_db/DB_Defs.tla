------------------------------ MODULE DB_Defs -------------------------------

LOCAL INSTANCE Utils

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

-----------------------------------------------------------------------------

(**********************************)
(* Definitions of ubiquitous sets *)
(**********************************)

Nodes == 1..numNodes

Chains == 1..numChains

Branches == 0..sizeBound

Heights == 0..sizeBound

Op_nums == 0..sizeBound

activeChains == 1..network_info.chains

activeNodes[ chain \in Chains ] == network_info.active[chain]

activeBranches[ chain \in Chains ] == 0..network_info.branch[chain]

-----------------------------------------------------------------------------

(***********************)
(* Blocks & Operations *)
(***********************)

\* The set of all block headers
Headers == [ height : Heights, chain : Chains, branch : Branches, num_ops : Op_nums ]

\* The set of all block operations
Operations == UNION { [ 1..num_ops -> Pairs({h}, 1..num_ops) ] : h \in Heights, num_ops \in Op_nums }

\* The set of all blocks
Blocks == [ header : Headers, ops : Operations ]

\* Block "constructor"
Block(header, ops) == [ header |-> header, ops |-> ops ]

\* Header "constructor"
Header(chain, branch, height, num_ops) ==
    [ chain |-> chain, branch |-> branch, height |-> height, num_ops |-> num_ops ]

\* Operations "constructor"
mkOps(height, num_ops) == [ x \in 1..num_ops |-> <<height, x>> ]

\* header predicate
isHeader(h) == DOMAIN h = { "chain", "branch", "height", "num_ops" }

\* block predicate
isBlock(b) ==
    /\ DOMAIN b = { "header", "ops" }
    /\ isHeader(b.header)
    /\ b.ops = mkOps(b.header.height, b.header.num_ops)

\* selects a block on [branch] of [chain] at [height]
blockAtHeight(chain, branch, height) ==
    Pick({ b \in ToSet(network_info.blocks[chain][branch]) : b.header.height = height })

-----------------------------------------------------------------------------

(********************)
(* Helper functions *)
(********************)

\* get the current branch of [node] on [chain]
current_branch[ node \in Nodes, chain \in Chains ] ==
    LET branches == node_info.branches[node][chain]
    IN CASE branches = <<>> -> -1
         [] OTHER -> Head(branches)

\* get the current height of [node] on [branch] [chain]
current_height[ node \in Nodes, chain \in Chains, branch \in Branches ] ==
    LET blocks == node_info.blocks[node][chain][branch]
    IN CASE blocks = <<>> -> -1
         [] OTHER -> Head(blocks).header.height

\* check that [node]'s message queue on [chain] is not full
checkMessages[ node \in Nodes ] ==
    [ chain \in Chains |-> Len(node_info.messages[node][chain]) < sizeBound ]

\* check that there is space for [node] to register an expectation on [chain]
checkExpect[ node \in Nodes ] ==
    [ chain \in Chains |-> Cardinality(node_info.expect[node][chain]) < sizeBound ]

\* check that there is space to for [node] to insert a header on [chain]
checkHeaders[ node \in Nodes ] ==
    [ chain \in Chains |-> Len(node_info.headers[node][chain]) < sizeBound ]

\* check that there is space to send [node] a message [offchain]
checkOffchain[ node \in Nodes ] == Cardinality(node_info.offchain[node]) < sizeBound

\* check that there is space to send [node] a message on [chain]
checkSent[ chain \in Chains ] ==
    [ node \in Nodes |-> Cardinality(network_info.sent[chain][node]) < sizeBound ]

\* check that [set] is not full before including the message
checkAdd(set, msg) ==
    CASE Cardinality(set) < sizeBound -> set \cup {msg}
      [] OTHER -> set

\* send [msg] to all active nodes on [chain] except [from]
\* sent_chain \in [ Nodes -> SUBSET Messages ]
checkAddToActive(sent_chain, from, chain, msg) ==
    [ to \in Nodes |->
        CASE to \in activeNodes[chain] \ {from} -> checkAdd(sent_chain[to], msg)
          [] OTHER -> sent_chain[to] ]

\* system sends [msg] to active nodes on [chain]
checkSysAddToActive(sent, chain, msg) ==
    [ to \in Nodes |->
        CASE to \in activeNodes[chain] -> checkAdd(sent[to], msg)
          [] OTHER -> sent[to] ]

\* check that [set1] \cup [set2] is not full before unioning [set2] with [set1]
checkUnion(set1, set2) ==
    LET union == set1 \cup set2
    IN CASE Cardinality(union) <= sizeBound -> union
         [] OTHER -> set1

\* check that [queue] is not full before including the message at the end
checkAppend(queue, msg) ==
    CASE Len(queue) < sizeBound -> Append(queue, msg)
      [] OTHER -> queue

\* check that [stack] is not full before including [data] at the beginning
checkCons(data, stack) ==
    CASE Len(stack) < sizeBound -> <<data>> \o stack
      [] OTHER -> stack

\* insert [header] into [headers]
insertHeader(header, headers) ==
    LET RECURSIVE aux(_, _, _)
        aux(h, hs, acc) ==
          CASE hs = <<>> -> Append(acc, h)
            [] OTHER ->
               LET hd == Head(hs)
               IN
                 CASE h.branch > hd.branch -> acc \o <<h>> \o hs
                   [] OTHER ->
                      CASE h.branch # hd.branch -> aux(h, Tail(hs), Append(acc, hd))
                        [] OTHER ->
                           CASE h.height > hd.height -> acc \o <<h>> \o hs
                             [] OTHER -> aux(h, Tail(hs), Append(acc, hd))
    IN CASE header \notin ToSet(headers) -> aux(header, headers, <<>>)
         [] OTHER -> headers

\* check that [headers] is not full before inserting [header]
checkInsertHeader(header, headers) ==
    CASE Len(headers) < sizeBound -> insertHeader(header, headers)
      [] OTHER -> headers

\* insert [block] into [blocks]
insertBlock(block, blocks) ==
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
                      CASE b_branch # hd_branch -> aux(b, Tail(bs), Append(acc, hd))
                        [] OTHER ->
                           CASE b_height > hd_height -> acc \o <<b>> \o bs
                             [] OTHER -> aux(b, Tail(bs), Append(acc, hd))
    IN CASE blocks \notin ToSet(blocks) -> aux(block, blocks, <<>>)
         [] OTHER -> blocks

\* check that [blocks] is not full before inserting [block]
checkInsertBlock(block, blocks) ==
    CASE Len(blocks) < sizeBound -> insertBlock(block, blocks)
      [] OTHER -> blocks

\* check that all [branches] are valid branches on [chain]
RECURSIVE checkBranches(_, _)
checkBranches(branches, chain) ==
    \/ branches = <<>>
    \/ /\ Head(branches) \in activeBranches[chain]
       /\ checkBranches(Tail(branches), chain)

-----------------------------------------------------------------------------

(********************)
(* Sequences & Sets *)
(********************)

BoundedSeq(S) == Seq_n(S, sizeBound)

BoundedSubsets(S) == Subsets_n(S, sizeBound)

=============================================================================
