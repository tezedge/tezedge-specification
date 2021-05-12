---- MODULE MC_liveness ----

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
    1 :> header(0, 0, 0)

\* Good_nodes -> SUBSET Blocks
Good_node_blocks ==
    LET hd1  == header(1, 0, 0)
        hsh1 == hash(hd1)
        ops1 == operations(hsh1, 0..0)
        b1   == block(hd1, ops1)
        hd2  == header(2, hsh1, 0)
        b2   == block(hd2, operations(hash(hd2), 0..1))
    IN
    1 :> {genesis, b1, b2}

All_good_node_blocks == UNION { Good_node_blocks[n] : n \in GOOD_NODES }

Validator == [ b \in Blocks |->
    CASE b \in All_good_node_blocks -> "known_valid"
      [] OTHER -> "unknown" ]

Node_samples == [ n \in Good_nodes |-> [ bn \in Bad_bootstrapping \cup Good_bootstrapping |-> <<>> ] ]

============================
