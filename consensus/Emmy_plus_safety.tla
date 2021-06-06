---- MODULE Emmy_plus_safety ----

EXTENDS Consensus

Rolls == 0..9
Delegates == 1..5

Max_bake == 2
Max_cycle == 3
Max_endorse == 4
Min_endorse == 1
Max_time == 10
Max_balance == 1000
Max_deposit == 20
Max_reward == 100
Min_block_delay == 1
Baking_delay == 2
Endorsement_delay == 1
Initial_endorsers == 2
Tokens_per_roll == 300
Blocks_per_cycle == 3
Blocks_per_snapshot == 1
Init_balance == [ d \in Delegates |-> 200 ]
Init_rolls_snapshot == [ d \in Delegates |-> {} ]
Init_safety_deposit == [ d \in Delegates |-> 100 ]

level_rewards_prio_zero == 40
level_rewards_prio_nonzero == 3

Baking_priority == {} \* TODO
Endorsement_rights == {} \* TODO

emmy_plus_delay(p, e) ==
    MIN_BLOCK_DELAY + BAKING_DELAY * p + ENDORSEMENT_DELAY * max(0, INITIAL_ENDORSERS - e)

emmy_star_delay(p, e) ==
    IF p = 0 /\ 5 * e >= 3 * MAX_ENDORSE THEN MIN_BLOCK_DELAY
    ELSE emmy_plus_delay(p, e)

baking_reward_(c, bs, r) ==
    LET p == baking_priority(c, bs, r)
        e == endorsements[c][bs][r]
    IN
    IF p = 0 THEN ((level_rewards_prio_zero \div 2) * e) \div MAX_ENDORSE
    ELSE (level_rewards_prio_nonzero * e) \div MAX_ENDORSE

endorsing_reward(c, bs, r) ==
    LET p == baking_priority(c, bs, r) IN
    IF p = 0 THEN baking_reward_(c, bs, r)
    ELSE (baking_reward_(c, bs, r) * 2) \div 3

\* Baking_reward[c][bs][d] == {} \* TODO

\* Endorsement_reward[c][bs][d] == {} \* TODO

=================================
