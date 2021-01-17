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

-----------------------------------------------------------------------------

(********************)
(* Helper functions *)
(********************)

\* get the current branch of [node] on [chain]
current_branch[ node \in Nodes, chain \in Chains ] ==
    LET branches == node_info.branches[node][chain]
    IN
      CASE branches = <<>> -> -1
        [] OTHER -> Head(branches)

\* get the current height of [node] on [branch] [chain]
current_height[ node \in Nodes, chain \in Chains, branch \in Branches ] ==
    LET blocks == node_info.blocks[node][chain][branch]
    IN
      CASE blocks = <<>> -> -1
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
checkAddToActive(from, chain, msg) ==
    [ to \in Nodes |->
        LET sent_to == network_info.sent[chain][to]
        IN
          CASE to \in activeNodes[chain] \ {from} -> checkAdd(sent_to, msg)
            [] OTHER -> sent_to ]

\* check that [set1] \cup [set2] is not full before unioning [set2] with [set1]
checkUnion(set1, set2) ==
    LET union == set1 \cup set2
    IN
      CASE Cardinality(union) <= sizeBound -> union
        [] OTHER -> set1

\* check that [queue] is not full before including the message at the end
checkAppend(queue, msg) ==
    CASE Len(queue) < sizeBound -> Append(queue, msg)
      [] OTHER -> queue

\* check that [stack] is not full before including the message at the beginning
checkCons(stack, msg) ==
    CASE Len(stack) < sizeBound -> <<msg>> \o stack
      [] OTHER -> stack

\* blah
insert(header, seq) ==
    LET RECURSIVE aux(_, _, _)
        aux(h, s, acc) ==
          CASE s = <<>> -> Append(acc, h)
            [] OTHER ->
               LET hd == Head(s)
               IN
                 CASE h.branch > hd.branch -> acc \o <<h>> \o s
                   [] OTHER ->
                      CASE h.branch # hd.branch -> aux(h, Tail(s), Append(acc, hd))
                        [] OTHER ->
                           CASE h.height > hd.height -> acc \o <<h>> \o s
                             [] OTHER -> aux(h, Tail(s), Append(acc, hd))
    IN
      CASE header \notin ToSet(seq) -> aux(header, seq, <<>>)
        [] OTHER -> seq

\* check that [seq] is not full before inserting [header]
checkInsert(seq, header) ==
    CASE Len(seq) < sizeBound -> insert(header, seq)
      [] OTHER -> seq

=============================================================================
