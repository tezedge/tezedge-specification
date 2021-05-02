---- MODULE Bootstrap_pipeline ----

EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS
    BAD_NODES,           \* nodes behaving arbitrarily
    GOOD_NODES,          \* nodes following the protocol
    BOOTSTRAPPING_NODES, \* nodes fetching headers and operations
    NODE_CHAINS,         \* each good and bad node's sequence of blocks
    MIN_PEERS,           \* minimum number of peers
    MAX_PEERS            \* maximum number of peers

VARIABLES
    blacklist,          \* each bootstrapping node's set of blacklisted peers
    peers,              \* each bootstrapping node's set of peers
    locators,           \* each bootstrapping node's list of steps
    fetched_headers,    \* each bootstrapping node's set of fetched headers (fetched from top to bottom)
    fetched_operations, \* each bootstrapping node's queue of fetched operations
    validated_blocks,   \* each bootstrapping node's list of validated blocks
    header_pipe         \* each bootstrapping node's queue of fetched headers

vars == <<blacklist, peers, locators, fetched_headers, fetched_operations, validated_blocks>>

----

ASSUME BAD_NODES \cap GOOD_NODES = {}
ASSUME DOMAIN NODE_CHAINS = BAD_NODES \cup GOOD_NODES

----

(***********)
(* Helpers *)
(***********)

Nodes == BAD_NODES \cup GOOD_NODES

PeerSets == { ps \in SUBSET Nodes : Cardinality(ps) >= MIN_PEERS /\ Cardinality(ps) <= MAX_PEERS }

All_nodes_have_peers == \A n \in BOOTSTRAPPING_NODES : peers[n] /= {}

NESeq(s) == Seq(s) \ {<<>>}

Headers == [
    level   : Nat,
    fitness : NESeq(Nat),
    op_hash : Nat,
    context : Nat
]

Locators == [ headers : NESeq(Headers), hashes : NESeq(Nat) ]

Steps == [
    block  : Nat \ {0},
    pred   : Nat,
    step   : Nat,
    strict : BOOLEAN
]

Operations == [ branch : Nat ]

Blocks == [ header : Headers, ops : Operations ]

genesis == [
    header |-> [ level  |-> 0, fitness |-> <<>>, op_hash |-> 0 ],
    ops    |-> [ branch |-> 0 ]
]

----

(***********)
(* Actions *)
(***********)

\* locator is a list of steps

\* fetch_step(head, caboose)
\* 1. check that locator is valid
\* 2. get block header associated to hash
\* 3. check if received header is acceptable
\* 4. loop on the predeessor of the current block

\* fetch_header
\* fetch_operations
\* validate_blocks
\* header_timeout
\* operation_timeout
\* other errors?
\* logging?

\* Block_validator
\* type result =
\*   | Already_commited
\*   | Outdated_block
\*   | Validated
\*   | Validation_error of error trace

\* block validity
\* type validity = Unkown | Known_valid | Known_invalid

\* intialize peers
init_peers(n) == \E ps \in PeerSets :
    /\ peers' = [ peers EXCEPT ![n] = ps ]
    /\ UNCHANGED <<blacklist, locators, fetched_headers, fetched_operations, validated_blocks>>

Init_peers == \E n \in BOOTSTRAPPING_NODES :
    /\ peers[n] = {}
    /\ init_peers(n)

----

(*********************)
(* Initial predicate *)
(*********************)

Init ==
    /\ blacklist          = [ n \in BOOTSTRAPPING_NODES |-> {} ]
    /\ peers              = [ n \in BOOTSTRAPPING_NODES |-> {} ]
    /\ locators           = [ n \in BOOTSTRAPPING_NODES |-> <<>> ]
    /\ fetched_headers    = [ n \in BOOTSTRAPPING_NODES |-> <<>> ]
    /\ fetched_operations = [ n \in BOOTSTRAPPING_NODES |-> <<>> ]
    /\ validated_blocks   = [ n \in BOOTSTRAPPING_NODES |-> <<genesis>> ]

(****************)
(* Next actions *)
(****************)

Next ==
    /\ {}
    /\ Init_peers

(************)
(* Fairness *)
(************)

Fairness == {}

(*****************)
(* Specification *)
(*****************)

Spec == Init /\ [][Next]_vars /\ Fairness

----

(**************)
(* Invariants *)
(**************)

(**************)
(* Properties *)
(**************)

===================================
