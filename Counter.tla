------------------------------ MODULE Counter ------------------------------

EXTENDS Utils

CONSTANTS alpha, id, None,
          N,  \* counter size bound
          M   \* counter number bound

VARIABLES state,     \* function from counter id to its state
          registered \* set of registered counters

vars == <<state, registered>>

ASSUME (alpha \in Nat) /\ (alpha > 0) /\ (alpha < 1000)
ASSUME id \in Nat
ASSUME (N \in Nat) /\ (N > 0)
\*ASSUME state \in [ 0..M -> [ avg : Nat, curr : Nat, tot : Nat ] ]

----------------------------------------------------------------------------

Optional == 0..N \cup {None}

empty == [ avg |-> None, curr |-> None, total |-> None ]

fresh == [ avg |-> 0, curr |-> 0, total |-> 0 ]

RECURSIVE _divide(_, _, _)
_divide(n, m, p) ==
    IF n < m
    THEN IF m <= 2 * n
         THEN p + 1
         ELSE p
    ELSE _divide(n - m, m, p + 1)

divide(a, b) == _divide(a, b, 0)

RECURSIVE update(_, _)
update(s, r) ==
    IF s = {}
    THEN r
    ELSE
      LET x == Pick(s)
          avg == r[x].avg
          cur == r[x].curr
          new == [ r EXCEPT ![x].avg = alpha * cur + divide((1000 - alpha) * avg, 1000),
                            ![x].curr = 0 ]
      IN update(s \ {x}, new)

----------------------------------------------------------------------------

(* Actions *)

\* Include a previously unregistered counter
Include(c) ==
    /\ state' = [ state EXCEPT ![c] = fresh ]
    /\ registered' = registered \cup {c}

\* Add x to a registered counter
Add(c, x) ==
    /\ state' = [ state EXCEPT ![c].total = @ + x, ![c].curr = @ + x ]
    /\ UNCHANGED registered

\* Reset a registered counter
Reset(c) ==
    /\ state' = [ state EXCEPT ![c] = fresh ]
    /\ UNCHANGED registered

\* Destroy a registered counter
Destroy(c) ==
    /\ state' = [ state EXCEPT ![c] = empty ]
    /\ registered' = registered \ {c}

\* Work action
\* Enabled by having all registered counters with average < alpha
Work ==
    /\ registered # {}
    /\ \A c \in registered : state[c].avg < alpha
    /\ state' = update(registered, state)
    /\ UNCHANGED registered

----------------------------------------------------------------------------

(* Type invariant *)
\*TypeOK ==
\*    /\ state \in [ 0..M -> [ avg : Optional, curr : Optional, total : Optional ] ]
\*    /\ registered \subseteq 0..M

(* Initial predicate *)
Init ==
    /\ state = [ x \in 0..M |-> empty ]
    /\ registered = {}

----------------------------------------------------------------------------

(* Next actions *)

\* Register a counter
Include_one ==
    \E c \in 0..M :
        /\ c \notin registered
        /\ Include(c)

\* Add to a registered counter
Add_x ==
    \E c \in registered, x \in 0..N :
        /\ state[c].total <= N - x
        /\ Add(c, x)

Reset_one ==
    \E c \in registered :
        /\ state[c].total = N
        /\ Reset(c)

Destroy_one == \E c \in registered : Destroy(c)

Next ==
    \/ Include_one
    \/ Add_x
    \/ Reset_one
    \/ Destroy_one
    \/ Work

----------------------------------------------------------------------------

(* Specification *)
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

(* Invariants *)

=============================================================================
