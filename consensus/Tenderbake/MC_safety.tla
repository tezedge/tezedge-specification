---- MODULE MC_safety ----

EXTENDS Tenderbake

Correct_procs == 1..4

Faulty_procs == 0..0

Committee_size == 4

Committee[ l \in Levels ] ==
    IF l = 0 THEN Procs
    ELSE Procs \ {l % n}

Proposer[ l \in Levels ] ==
    [ r \in Rounds |->
        IF r % n = 0 THEN (l + 1) % n
        ELSE (l + r) % n ]

==========================
