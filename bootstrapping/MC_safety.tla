---- MODULE MC_safety ----

EXTENDS Bootstrap_pipeline, TLC

Bad_nodes == 0..0

Good_nodes == 1..1

Bad_bootstrapping == 2..2

Good_bootstrapping == 3..3

Min_peers == 1

Max_peers == 2

Max_level == 2

Max_ops == 2

\* Good_nodes -> Headers
Current_head ==
    1 :> {}

\* Good_nodes -> SUBSET Blocks
Good_node_blocks ==
    1 :> {}

All_good_node_blocks == UNION { Good_node_blocks[n] : n \in GOOD_NODES }

Validator == [ b \in Blocks |->
    CASE b \in All_good_node_blocks -> "known_valid"
      [] OTHER -> "unknown" ]

Node_samples == [ n \in Good_nodes |-> [ bn \in Bad_bootstrapping \cup Good_bootstrapping |-> <<>> ] ]

==========================
