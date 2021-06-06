---- MODULE Emmy_star_safety ----

EXTENDS Consensus

Rolls == 0..9
Delegates == 1..5

Max_bake == 2
Max_cycle == 3
Max_delay == 5
Max_endorse == 4
Min_endorse == 1
Max_time == 10
Max_balance == 1000
Max_deposit == 20
Max_reward == 100

\* block delay
Min_block_delay == 1
Baking_delay == 2
Endorsement_delay == 1
Initial_endorsers == 2

Tokens_per_roll == 300
Blocks_per_cycle == 3
Blocks_per_snapshot == 1
Init_balance == [ d \in Delegates |-> 200 ]
Init_rolls_snapshot == [ d \in Delegates |->
    LET n == 2 * (d - 1) IN
    n..(n + 1)
]
Init_safety_deposit == [ d \in Delegates |-> 100 ]

level_rewards_prio_zero == 40
level_rewards_prio_nonzero == 3

emmy_plus_delay(p, e) ==
    Min_block_delay + Baking_delay * p + Endorsement_delay * max(0, Initial_endorsers - e)

emmy_star_delay(p, e) ==
    IF p = 0 /\ 5 * e >= 3 * Max_endorse THEN Min_block_delay
    ELSE emmy_plus_delay(p, e)

Block_delay[ p \in 0..(Max_bake - 1) ] == [ e \in 0..Max_endorse |->
    Min_block_delay + Baking_delay * p + Endorsement_delay * max(0, Initial_endorsers - e)
]

baking_reward_(c, bs, r) ==
    LET p == baking_priority(c, bs, r)
        e == endorsements[c][bs][r]
    IN
    IF p = 0 THEN ((level_rewards_prio_zero \div 2) * e) \div Max_endorse
    ELSE (level_rewards_prio_nonzero * e) \div Max_endorse

endorsing_reward(c, bs, r) ==
    LET p == baking_priority(c, bs, r) IN
    IF p = 0 THEN baking_reward_(c, bs, r)
    ELSE (baking_reward_(c, bs, r) * 2) \div 3

\* TODO
\*   find all rolls controlled by delegate
\*   find lowest priority baking roll [r]
\*   
\* cycle -> block_slot -> delegate -> int
Baking_reward[ c \in 0..Max_cycle ] ==
    [ bs \in 0..(Blocks_per_cycle - 1) |->
        [ d \in Delegates |->
            0
        ]
    ]

\* cycle -> block_slot -> delegate -> int
Endorsement_reward[ c \in 0..Max_cycle ] ==
    [ bs \in 0..(Blocks_per_cycle - 1) |->
        [ d \in Delegates |->
            0
        ]
    ]

Baking_priority == {} \* TODO
Endorsement_rights == {} \* TODO

=================================
