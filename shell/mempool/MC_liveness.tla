---- MODULE MC_liveness ----

EXTENDS Mempool_global, TLC

NN == 3

char(n) ==
    CASE n = 1 -> "a"
      [] n = 2 -> "b"
      [] n = 3 -> "c"
      [] n = 4 -> "d"
      [] n = 5 -> "e"

int_of_char(c) ==
    CASE c = "a" -> 1
      [] c = "b" -> 2
      [] c = "c" -> 3
      [] c = "d" -> 4
      [] c = "e" -> 5

Ns == Map_set(1..NN, char)

exclude(n) == {n, char((int_of_char(n) % Cardinality(Ns)) + 1)}

----

Init_peers[ n \in Ns ] == Ns \ {n}

\* NN = 2
\* Init_connections[ n \in Ns ] == Ns \ {n}

\* NN = 3
\* a --- b --- c
Init_connections[ n \in Ns ] == IF n /= "b" THEN {"b"} ELSE {"a", "c"}

\* NN = 5
\* Init_connections[ n \in Ns ] ==
\*     CASE n = "a" -> {"b", "c"}
\*       [] n = "b" -> {"a", "c"}
\*       [] n = "c" -> {"a", "b", "d"}
\*       [] n = "d" -> {"c", "e"}
\*       [] n = "e" -> {"d"}

Init_predecessor[ n \in Ns ] == block(0, <<>>)

Max_hops == 3

Min_connections == 1

Max_connections == 4

Min_endorsements == 2

Max_hash == 25

View == [
    shell |-> [
        peers |-> peers,
        connections |-> connections,
        messages |-> messages
    ],
    pv |-> [
        predecessor |-> predecessor,
        branch_delayed |-> branch_delayed,
        branch_refused |-> branch_refused,
        refused |-> refused,
        pending |-> pending,
        advertisement |-> advertisement
    ],
    mp |-> [
        known_valid |-> known_valid,
        mp_pending |-> mp_pending
    ]
]

============================
