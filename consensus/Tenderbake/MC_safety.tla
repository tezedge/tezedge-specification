---- MODULE MC_safety ----

EXTENDS Tenderbake

Correct_procs == 1..4

Faulty_procs == 0..0

Committee_size == 4

Committee[ l \in Levels ] == RandomElement(Committees)

Proposer[ l \in Levels ] == [ r \in Rounds |-> (l + r) % n ]

==========================
