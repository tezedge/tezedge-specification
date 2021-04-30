---- MODULE Bootstrap_pipeline ----

EXTENDS Naturals

CONSTANTS
    BAD_NODES,
    GOOD_NODES,
    BOOTSTRAPPING_NODES

\* Not needed we will allow for all possibilities
\* distributed_db
\* block_validator

VARIABLES
    locators,           \* 
    fetched_headers,    \* 
    fetched_operations, \* 
    validated_blocks,   \* 
    header_pipe,        \* 
    operation_pipe      \* 

vars == <<>>

----

(***********)
(* Helpers *)
(***********)

----

(***********)
(* Actions *)
(***********)

----

(*********************)
(* Initial predicate *)
(*********************)

Init == {}

(****************)
(* Next actions *)
(****************)

Next == {}

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
