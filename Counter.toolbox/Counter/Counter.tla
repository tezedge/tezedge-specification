------------------------------ MODULE Counter ------------------------------

EXTENDS Naturals, Integers, TLC

CONSTANTS alpha, id, None,
          N,  \* counter size bound
          M   \* counter number bound

VARIABLES state, registered

(* state[id] \in [ avg : Nat, curr : Nat, tot : Nat ] *)

vars == <<state, registered>>

ASSUME (alpha \in Nat) /\ (alpha > 0) /\ (alpha < 1000)
ASSUME id \in Nat
ASSUME (N \in Nat) /\ (N > 0)

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
      LET x == CHOOSE _x \in s : TRUE
          avg == r[x].avg
          cur == r[x].curr
          new == [ r EXCEPT ![x].avg = alpha * cur + divide((1000 - alpha) * avg, 1000),
                            ![x].curr = 0 ]
      IN update(s \ {x}, new)

----------------------------------------------------------------------------

\*TypeOK ==
\*    /\ state \in [ 0..M -> [ avg : Optional, curr : Optional, total : Optional ] ]
\*    /\ registered \subseteq 0..M

Init ==
    /\ state = [ x \in 0..M |-> empty ]
    /\ registered = {}

----------------------------------------------------------------------------

(* Actions *)
Include(c) ==
    /\ c \notin registered
    /\ state' = [ state EXCEPT ![c] = fresh ]
    /\ registered' = registered \cup {c}

Add(c, x) ==
    /\ state[c].total <= N - x
    /\ state' = [ state EXCEPT ![c].total = @ + x, ![c].curr = @ + x ]
    /\ UNCHANGED registered

Reset(c) ==
    /\ state[c].total = N
    /\ state' = [ state EXCEPT ![c] = fresh ]
    /\ UNCHANGED registered

Destroy(c) ==
    /\ state' = [ state EXCEPT ![c] = empty ]
    /\ registered' = registered \ {c}

Work ==
    /\ registered # {}
    /\ \A c \in registered : state[c].avg < alpha
    /\ state' = update(registered, state)
    /\ UNCHANGED registered 

----------------------------------------------------------------------------

(* Next actions *)
Include_one == \E c \in 0..M : Include(c)

Add_x == \E c \in registered, x \in 0..N : Add(c, x)

Reset_one == \E c \in registered : Reset(c)

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

=============================================================================
