------------------------------ MODULE Counter ------------------------------

EXTENDS Utils

CONSTANTS alpha,       \* average parameter
          id,          \* id for counter manager
          sizeBound,   \* bound on size of each counter (to keep model finite)
          numCounters, \* max number of counters that can be managed
          None         \* null value

VARIABLES state,     \* function from counter id to its state
          registered \* set of registered counters

vars == <<state, registered>>

ASSUME (alpha \in Nat) /\ (alpha > 0) /\ (alpha < 1000)
ASSUME id \in Nat
ASSUME numCounters \in Nat
ASSUME (sizeBound \in Nat) /\ (sizeBound > alpha)

\* state \in [ PossibleCounterValues -> [ avg : Nat, curr : Nat, tot : Nat ] ]

----------------------------------------------------------------------------

PossibleCounters == 1..numCounters

PossibleCounterValues == 0..sizeBound

Optional == PossibleCounterValues \cup {None}

\* value of an unregistered counter's state
null == [ avg |-> None, curr |-> None, total |-> None ]

\* value of a newly registered counter's state
fresh == [ avg |-> 0, curr |-> 0, total |-> 0 ]

----------------------------------------------------------------------------

(* Actions *)

(***********)
(* Include *)
(***********)
\* Register a previously unregistered counter with this manager
Include(c) ==
    /\ state' = [ state EXCEPT ![c] = fresh ]
    /\ registered' = registered \cup {c}

Include_one ==
    \E c \in PossibleCounters :
        /\ c \notin registered
        /\ Include(c)

(*******)
(* Add *)
(*******)
\* Add x to a registered counter
Add(c, x) ==
    /\ state' = [ state EXCEPT ![c].total = @ + x, ![c].curr = @ + x ]
    /\ UNCHANGED registered

\* Add x if doing so will not cause either total or avg to exceed sizeBound
Add_x ==
    \E c \in registered, x \in 1..sizeBound :
        LET curr == state[c].curr
        IN
          /\ state[c].total <= sizeBound - x
          /\ state[c].avg <= sizeBound - alpha * (curr + x)
          /\ Add(c, x)

(*********)
(* Reset *)
(*********)
\* Reset a registered counter
Reset(c) ==
    /\ state' = [ state EXCEPT ![c] = fresh ]
    /\ UNCHANGED registered

\* Reset a registered counter that has reached its maximum value
Reset_one ==
    \E c \in registered :
        /\ state[c].total = sizeBound
        /\ Reset(c)

(***********)
(* Destroy *)
(***********)
\* Destroy a registered counter
Destroy(c) ==
    /\ state' = [ state EXCEPT ![c] = null ]
    /\ registered' = registered \ {c}

Destroy_one == \E c \in registered : Destroy(c)

(********)
(* Work *)
(********)
\* Enabled by having all registered counters with average < alpha
Work ==
    /\ registered # {}
    /\ \A c \in registered : state[c].avg < alpha
    /\ state' =
         [ c \in PossibleCounters |->
             CASE c \in registered ->
                 LET curr == state[c].curr IN
                 [ state[c] EXCEPT
                     !.avg = alpha * curr + divide[(1000 - alpha) * @, 1000],
                     !.curr = 0 ]
               [] OTHER -> state[c] ]
    /\ UNCHANGED registered

----------------------------------------------------------------------------

(* Initial predicate *)
Init ==
    /\ state = [ x \in PossibleCounters |-> null ]
    /\ registered = {}

(* Next actions *)
Next ==
    \/ Include_one
    \/ Add_x
    \/ Reset_one
    \/ Destroy_one
    \/ Work

(* Specification *)
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

(* Invariants *)

TypeOK ==
    /\ state \in
         [ PossibleCounters -> [ avg : Optional, curr : Optional, total : Optional ] ]
    /\ registered \subseteq PossibleCounters

OnlyUnregisteredNullState ==
    \A c \in PossibleCounters : state[c] = null <=> c \notin registered

=============================================================================
