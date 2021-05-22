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

Threshold == 0

LOCAL hd1  == header(1, 0, 0, 1)
LOCAL hsh1 == hash(hd1)
LOCAL ops1 == operations(hsh1, 0..0)
LOCAL b1   == block(hd1, ops1)
LOCAL hd2  == header(2, hsh1, 0, 2)
LOCAL b2   == block(hd2, operations(hash(hd2), 0..1))

\* Good_nodes -> Headers
Current_head == 1 :> hd2

\* Good_nodes -> SUBSET Blocks
Good_node_blocks == 1 :> <<genesis, b1, b2>>

All_good_node_blocks == UNION { ToSet(Good_node_blocks[n]) : n \in GOOD_NODES }

Good_node_levels[ n \in Good_nodes ] == { b.header.level : b \in ToSet(Good_node_blocks[n]) }

Good_node_max_level[ n \in Good_nodes ] == Max_set(Good_node_levels[n])

\* Merkle tree
\* 
\* ...                 .
\*                    / \
\*                   /   \
\* level: 2        h20    .
\*                 / \   / \
\*                /   \ /   \
\* level: 1     h10   h11    .
\*              / \   / \   / \
\*             /   \ /   \ /   \
\* level: 0  h00   h01   h02    .
\*            |     |     |     |
\* BLOCKS[n]  b0 <- b1 <- b2 <- ...

MerkleTree == [ n \in Good_nodes |->
    [ l \in Levels |->
        LET h00 == hash(gen_header)
            h01 == hash(hd1)
            h02 == hash(hd2)
            h10 == hash_nums(h00, h01)
            h11 == hash_nums(h01, h02)
            h20 == hash_nums(h10, h11)
        IN
        CASE l = 2 -> <<h20>>
          [] l = 1 -> <<h10, h11>>
          [] l = 0 -> <<h00, h01, h02>>
    ]
]

Validator == [ b \in Blocks |->
    CASE b \in All_good_node_blocks -> "known_valid"
      [] hash(b) > Cardinality(BlockHashes) \div 2 -> "known_invalid"
      [] OTHER -> "unknown" ]

Node_samples == [
    n \in Good_nodes |->
        LET length  == Cardinality(BLOCKS[n]) - 1
            levels  == Pick({ s \in Seq(Good_node_levels) :
                                /\ Len(s) >= length \div 2
                                /\ Len(s) <= length
                                /\ \A i \in DOMAIN s \ {1} : s[i - 1] < s[i] })
        IN
        [ bn \in Bootstrapping_nodes |->
            Map(LAMBDA l : MerkleTree[n][Good_node_max_level][l + 1], levels)
    ]
]

Merkle_hashes == [ n \in Good_nodes |->
    [ l \in Good_node_levels[n] |-> Head(MerkleTree[n][l]) ]
]

==========================
