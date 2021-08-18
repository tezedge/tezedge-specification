------------------------------ MODULE Counter ------------------------------

EXTENDS Utils

CONSTANTS
    \* average parameter
    \* @type: Int;
    alpha,

    \* id for counter manager
    \* @type: Int;
    id,

    \* bound on size of each counter (to keep model finite)
    \* @type: Int;
    sizeBound,

    \* max number of counters that can be managed
    \* @type: Int;
    NumCounters,
    
    \* null value
    \* @type: Int;
    None

VARIABLES
    \* function from counter id to its state
    \* @type: Int => [ avg : Int, current : Int, total : Int ];
    state,

    \* set of registered counters
    \* @type: Set(Int);
    registered

vars == <<state, registered>>

ASSUME alpha \in 1..1000
ASSUME id \in Nat
ASSUME NumCounters \in Nat /\ NumCounters > 0
ASSUME sizeBound \in Nat /\ sizeBound > alpha

----------------------------------------------------------------------------

PossibleCounters == 1..NumCounters

PossibleCounterValues == 0..sizeBound

Optional == PossibleCounterValues \cup {None}

\* value of an unregistered counter's state
null == [ avg |-> None, current |-> None, total |-> None ]

\* value of a newly registered counter's state
fresh == [ avg |-> 0, current |-> 0, total |-> 0 ]

----------------------------------------------------------------------------

(***********)
(* Actions *)
(***********)

\* Register a previously unregistered counter with this manager
Include(c) ==
    /\ state' = [ state EXCEPT ![c] = fresh ]
    /\ registered' = registered \cup {c}

Include_one ==
    \E c \in PossibleCounters :
        /\ c \notin registered
        /\ Include(c)

\* Add x to a registered counter
add(c, x) ==
    /\ state' = [ state EXCEPT ![c].total = @ + x, ![c].current = @ + x ]
    /\ UNCHANGED registered

\* Add x if doing so will not cause either total or avg to exceed sizeBound
Add ==
    \E c \in registered, x \in 1..sizeBound :
        LET curr == state[c].current
        IN /\ state[c].total <= sizeBound - x
           /\ state[c].avg <= sizeBound - alpha * (curr + x)
           /\ add(c, x)

\* Reset a registered counter
reset(c) ==
    /\ state' = [ state EXCEPT ![c] = fresh ]
    /\ UNCHANGED registered

\* Reset a registered counter that has reached its maximum value
Reset ==
    \E c \in registered :
        /\ state[c].total = sizeBound
        /\ reset(c)

\* Destroy a registered counter
destroy(c) ==
    /\ state' = [ state EXCEPT ![c] = null ]
    /\ registered' = registered \ {c}

Destroy == \E c \in registered : destroy(c)

\* Enabled by having all registered counter averages < alpha
Work ==
    /\ registered /= {}
    /\ \A c \in registered : state[c].avg < alpha
    /\ state' =
         [ c \in PossibleCounters |->
            CASE c \in registered ->
                    LET curr == state[c].current IN
                    [ state[c] EXCEPT
                        !.avg = alpha * curr + ((1000 - alpha) * @) \div 1000,
                        !.current = 0 ]
              [] OTHER -> state[c] ]
    /\ UNCHANGED registered

----------------------------------------------------------------------------

(*********************)
(* Initial predicate *)
(*********************)

Init ==
    /\ state = [ x \in PossibleCounters |-> null ]
    /\ registered = {}

(****************)
(* Next actions *)
(****************)

Next ==
    \/ Include_one
    \/ Add
    \/ Reset
    \/ Destroy
    \/ Work

(************)
(* Fairness *)
(************)

Fairness ==
    /\ WF_vars(Include_one)
    /\ WF_vars(Add)
    /\ WF_vars(Reset)
    /\ WF_vars(Work)

(*****************)
(* Specification *)
(*****************)

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------

(**************)
(* Invariants *)
(**************)

StateOK ==
    /\ DOMAIN state = PossibleCounters
    /\ \A c \in PossibleCounters :
        state[c] \in [ avg : Optional, current : Optional, total : Optional ]

RegisteredOK == registered \subseteq PossibleCounters

TypeOK ==
    /\ StateOK
    /\ RegisteredOK

OnlyUnregisteredNullState ==
    \A c \in PossibleCounters : state[c] = null <=> c \notin registered

(**************)
(* Properties *)
(**************)

\* Fairness of scheduling as a liveness property modulo a notion of peer score
FarinessOfScheduling == TRUE

=============================================================================
