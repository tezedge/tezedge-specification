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

LOCAL hd1  == header(1, 0, 0, 1)
LOCAL hsh1 == hash(hd1)
LOCAL ops1 == operations(hsh1, 0..0)
LOCAL b1   == block(hd1, ops1)
LOCAL hd2  == header(2, hsh1, 0, 2)
LOCAL b2   == block(hd2, operations(hash(hd2), 0..1))

\* Good_nodes -> Headers
Current_head == 1 :> hd2

\* Good_nodes -> SUBSET Blocks
Good_node_blocks == 1 :> {genesis, b1, b2}

All_good_node_blocks == UNION { Good_node_blocks[n] : n \in GOOD_NODES }

Validator == [ b \in Blocks |->
    CASE b \in All_good_node_blocks -> "known_valid"
      [] OTHER -> "unknown" ]

Node_samples == [ n \in Good_nodes |->
    [ bn \in Bootstrapping_nodes |-> <<1>> ]
]

============================
