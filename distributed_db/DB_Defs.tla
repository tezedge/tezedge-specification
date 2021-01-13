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

\* check that [node]'s message queue on [chain] is not full
checkMessages[ node \in Nodes ] ==
    [ chain \in Chains |-> Len(node_info.messages[node][chain]) < sizeBound ]

\* check that there is space to register an expectation [node] a message on [chain]
checkExpect[ node \in Nodes ] ==
    [ chain \in Chains |-> Cardinality(node_info.expect[node][chain]) < sizeBound ]

\* check that there is space to send [node] a message [offchain]
checkOffchain[ node \in Nodes ] == Cardinality(node_info.offchain[node]) < sizeBound

\* check that there is space to receive a message on [chain]
checkRecv[ chain \in Chains ] ==
    [ node \in Nodes |-> Len(network_info.recv[chain][node]) < sizeBound ]

\* check that there is space to send [node] a message on [chain]
checkSent[ chain \in Chains ] ==
    [ node \in Nodes |-> Cardinality(network_info.sent[chain][node]) < sizeBound ]

\* check that [set] is not full before including the message
checkAdd(set, msg) ==
    CASE Cardinality(set) < sizeBound -> set \cup {msg}
      [] OTHER -> set

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

=============================================================================
