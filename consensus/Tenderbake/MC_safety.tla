---- MODULE MC_safety ----

EXTENDS Tenderbake

Faulty_bakers == 0..0

Correct_bakers == 1..3

Max_level == 3

Proposer[ l \in Levels ] == [ r \in Rounds |-> (l + r) % n ]

==========================
