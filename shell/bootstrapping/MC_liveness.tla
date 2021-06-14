---- MODULE MC_liveness ----

EXTENDS Bootstrap_pipeline, TLC

Bad_nodes == 0..0

Good_nodes == 1..2

Bad_bootstrapping == 3..3

Good_bootstrapping == 4..4

Min_peers == 1

Max_peers == 2

Max_level == 2

Max_ops == 2

Threshold == 0

\* block 0 = genesis
\* block 1
\*   header(level, predecessor, context, fitness, ops_hash)
LOCAL ctx1 == hash_nums(0, 0)
LOCAL hd1  == header(1, 0, ctx1, 0, 1)
LOCAL hsh1 == hash(hd1)
LOCAL ops1 == operations(hsh1, 0..0)
LOCAL fit1 == 1
LOCAL b1   == block(hd1, ops1)
\* block 2
LOCAL ctx2 == hash_nums(ctx1, hsh1)
LOCAL hd2  == header(2, hsh1, ctx2, 0, 2)
LOCAL hsh2 == hash(hd2)
LOCAL ops2 == operations(hsh2, 0..1)
LOCAL fit2 == 2
LOCAL b2   == block(hd2, ops2)

\* Good_nodes -> Headers
Current_head[ n \in Good_nodes ] == hd2

\* Good_nodes -> SUBSET Blocks
Good_node_blocks ==
    LET chain == <<genesis, b1, b2>> IN
    [ n \in Good_nodes |-> chain ]

All_good_node_blocks == UNION { ToSet(Good_node_blocks[n]) : n \in GOOD_NODES }

Good_node_levels[    n \in Good_nodes ] == { b.header.level : b \in ToSet(Good_node_blocks[n]) }
Good_node_max_level[ n \in Good_nodes ] == Max_set(Good_node_levels[n])

\* BLOCKS[n]: b0 <- b1 <- b2 <- ...

node_blocks_at_level(n, l) == { b \in ToSet(Good_node_blocks[n]) : b.header.level = l }

Block_hashes[ n \in Good_nodes ] == UNION { node_blocks_at_level(n, l) : l \in Levels }

block_hash_level[ n \in Good_nodes, l \in Levels ] ==
    LET L == Max_set(Good_node_levels[n]) IN
    [ ll \in 1..L |->
        LET b(_l) ==
                LET blocks == node_blocks_at_level(n, _l) IN
                IF blocks = {} THEN genesis
                ELSE Pick(blocks)
        IN
        hash(b(ll).header)
    ]

Validator == [ b \in Blocks |->
    CASE b \in All_good_node_blocks -> "known_valid"
      [] hash(b) > Cardinality(BlockHashes) \div 2 -> "known_invalid"
      [] OTHER -> "unknown" ]

Node_samples[ n \in Good_nodes, bn \in (Bad_bootstrapping \cup Good_bootstrapping) ] ==
    LET length == Cardinality(BLOCKS[n])
        levels ==
            Pick({ s \in Seq(Good_node_levels) :
                \E L \in 1..length :
                    /\ DOMAIN s = 1..L
                    /\ Len(s) >= length \div 2
                    /\ Len(s) <= length
                    /\ \A i \in DOMAIN s \ {1} : s[i - 1] < s[i] })
    IN
    Map(LAMBDA l : <<l, block_hash_level[n, l]>>, levels)

============================
