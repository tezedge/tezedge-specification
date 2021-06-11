---- MODULE Consensus ----

EXTENDS FiniteSets, Integers, Naturals, Sequences, TLC

CONSTANTS
    ROLLS,                  \* set of roll ids
    DELEGATES,              \* set of delegate ids
    MAX_BAKE,               \* maximum number of baking slots per block slot
    MAX_CYCLE,              \* last cycle
    MAX_ENDORSE,            \* maximum number of endorsement slots per block slot
    MAX_TIME,               \* maximum time
    MAX_BALANCE,            \* maximum balance a delegate can have
    MAX_REWARD,             \* maximum baking/endorsement reward
    MIN_ENDORSE,            \* minimum number of endorses to close a block
    MAX_BLOCK_DELAY,        \* delay for non-priority bakers
    MIN_BLOCK_DELAY,        \* minimum block delay
    BLOCK_DELAY,            \* priority -> endorsements -> time
    INITIAL_ENDORSERS,      \* number of endorsements required to not incure additional block delay
    TOKENS_PER_ROLL,        \* Emmy = 10000, Emmy+/Emmy* = 8000
    BLOCKS_PER_CYCLE,       \* Emmy = 2048, Emmy+ = 4096, Emmy* = 8192
    \* BLOCKS_PER_SNAPSHOT,    \* number of blocks between roll snapshots
    INIT_BALANCE,           \* delegate -> int
    INIT_ROLLS_SNAPSHOT,    \* delegate -> Set(roll)
    SAFETY_DEPOSIT,         \* delegate -> int
    BAKING_PRIORITY,        \* cycle -> block_slot -> Seq(roll)
    ENDORSEMENT_RIGHTS,     \* cycle -> block_slot -> roll -> int
    BAKING_REWARD,          \* cycle -> block_slot -> roll -> int
    ENDORSEMENT_REWARD      \* cycle -> block_slot -> roll -> int

VARIABLES
    time,                   \* timestamp: 1 time ~ MIN_BLOCK_DELAY
    cycle,                  \* int
    block_slot,             \* int
    phase,                  \* phase \in { "active", "cycle_admin", "snapshot_admin" }
    all_blocks,             \* cycle -> block_slot -> Set(roll * time)
    delegate_blocks,        \* cycle -> block_slot -> delegate -> bool * roll * time
    balance,                \* cycle -> block_slot -> delegate -> int
    rolls_snapshot,         \* cycle -> block_slot -> delegate -> Set(roll)
    rolls_lifo,             \* cycle -> block_slot -> Seq(roll)
    endorsements,           \* cycle -> block_slot -> roll -> Set(roll)
    safety_deposit          \* cycle -> delegate -> int

\* inclusive variables


\* exclusive variables
non_block_vars == <<cycle, block_slot, phase, balance, rolls_snapshot, rolls_lifo, endorsements>>
non_del_vars   == <<time, cycle, block_slot, phase, all_blocks, balance, rolls_snapshot, rolls_lifo, endorsements>>
non_phase_vars == <<time, cycle, block_slot, all_blocks, delegate_blocks, balance, rolls_snapshot, rolls_lifo, endorsements>>
non_slot_vars  == <<time, phase, all_blocks, delegate_blocks, balance, rolls_snapshot, rolls_lifo, endorsements>>
non_time_vars  == <<cycle, block_slot, phase, all_blocks, delegate_blocks, balance, rolls_snapshot, rolls_lifo, endorsements>>

\* all variables
vars == <<time, cycle, block_slot, phase, all_blocks, delegate_blocks, balance, rolls_snapshot, rolls_lifo, endorsements>>

----

(***************)
(* Definitions *)
(***************)

All_time == 0..MAX_TIME

Cycles == 0..MAX_CYCLE

Balances == 0..MAX_BALANCE

max_slot == BLOCKS_PER_CYCLE - 1

Block_slots == 0..max_slot

Blocks == ROLLS \X All_time

\* Delegates either make a safety deposit or they don't
Deposits == {0} \cup {SAFETY_DEPOSIT}

Phases == { "active", "cycle_admin", "snapshot_admin" }

Rewards == 0..MAX_REWARD

card(set) == Cardinality(set)

ToSet(seq) == { seq[i] : i \in DOMAIN seq }

Pick(set) ==
    CASE set /= {} -> CHOOSE x \in set : TRUE

\* @type: (Int, Int) => Int;
max(a, b) == IF a >= b THEN a ELSE b

\* @type: (Seq(Int), Int) => Int;
RECURSIVE sum(_, _)
sum(seq, acc) ==
    IF seq = <<>> THEN acc
    ELSE sum(Tail(seq), acc + Head(seq))

Sum(seq) == sum(seq, 0)

loose(bal) == bal % TOKENS_PER_ROLL

\* @type: (Set(a), Seq(a)) => Seq(a);
RECURSIVE seq_of_set(_, _)
seq_of_set(s, acc) ==
    IF s = {} THEN acc
    ELSE
        LET x == Pick(s) IN
        seq_of_set(s \ {x}, Append(acc, x))

\* @type: Set(a) => Seq(a);
SetToSeq(s) == seq_of_set(s, <<>>)

\* @type: (a => b, Seq(a), Seq(b)) => Seq(b);
RECURSIVE map(_, _, _)
map(f(_), seq, acc) ==
    IF seq = <<>> THEN acc
    ELSE map(f, Tail(seq), Append(acc, f(Head(seq))))

\* @type: (a => b, Seq(a)) => Seq(b);
Map(f(_), seq) == map(f, seq, <<>>)

\* @type: (a, Seq(a), Int) => Int;
RECURSIVE index(_, _, _)
index(x, seq, i) ==
    IF seq = <<>> THEN -1
    ELSE
        IF x = Head(seq) THEN i + 1
        ELSE index(x, Tail(seq), i + 1)

\* @type: (a, Seq(a)) => Int;
Index0(x, seq) == index(x, seq, -1)

active_rolls(c, bs) == UNION { rolls_snapshot[c][bs][d] : d \in DELEGATES }

inactive_rolls(c, bs) == ROLLS \ active_rolls(c, bs)

RECURSIVE num_occ(_, _, _)
num_occ(x, s, acc) ==
    IF s = <<>> THEN acc
    ELSE
        LET new_acc == IF x /= Head(s) THEN acc ELSE acc + 1 IN
        num_occ(x, Tail(s), new_acc)

Num_occ(x, s) == num_occ(x, s, 0)

RECURSIVE seq_n(_, _, _, _)
seq_n(S, n, N, acc) ==
    IF n = N THEN acc
    ELSE
        LET new_acc == { Append(s, x) : s \in acc, x \in S } IN
        seq_n(S, n + 1, N, new_acc)

\* sequences of S of length n
Seq_n(S, n) == seq_n(S, 0, n, {<<>>})

\* injective sequences of S, length = card(S)
inj_seq(S) == { s \in Seq_n(S, card(S)) : \A x \in ToSet(s) : Num_occ(x, s) = 1 }

\* Get [d]'s current roll snapshot
current_snapshot_rolls(d) == rolls_snapshot[cycle][block_slot][d]

\* Get delegate id associated with roll [r]
lookup_roll_opt(r) ==
    LET s == { d \in DELEGATES : current_snapshot_rolls(d) = r } IN
    IF s /= {} THEN <<TRUE, Pick(s)>>
    ELSE <<FALSE, 0>>

isSome(opt) == opt[1]

abs(x) == IF x >= 0 THEN x ELSE -x

----

(***************)
(* Assumptions *)
(***************)

\* MAX_TIME is at least as long as the time is would take to bake all blocks at priority 0
ASSUME MAX_TIME >= (MAX_CYCLE + 1) * BLOCKS_PER_CYCLE * MIN_BLOCK_DELAY

LOCAL Max_baking_reward == 20
LOCAL Max_endorsement_reward == 2

\* MAX_REWARD is at least as large as the rewards accrued for baking all blocks in a cycle at priority 0
ASSUME MAX_REWARD >= card(Block_slots) * (Max_baking_reward + Max_endorsement_reward)

\* There are sufficiently many rolls to support all tokens in the network
ASSUME card(ROLLS) * TOKENS_PER_ROLL >= card(DELEGATES) * MAX_BALANCE

\* The block delay is always more than the minimum and less than the maximum delay
ASSUME \A p \in 0..MAX_BAKE, e \in 0..MAX_ENDORSE :
    /\ BLOCK_DELAY[p][e] >= MIN_BLOCK_DELAY
    /\ BLOCK_DELAY[p][e] <= MAX_BLOCK_DELAY

\* There are always MAX_BAKE baking slots in each block slot
ASSUME \A c \in Cycles, bs \in Block_slots : Len(BAKING_PRIORITY[c][bs]) = MAX_BAKE

\* There are always MAX_ENDORSE endorsement slots in each block slot
ASSUME \A c \in Cycles, bs \in Block_slots :
    Sum(Map(LAMBDA r : ENDORSEMENT_RIGHTS[c][bs][r], SetToSeq(ROLLS))) = MAX_ENDORSE

\* Initial rolls are disjoint
ASSUME \A d1, d2 \in DELEGATES :
    d1 /= d2 => INIT_ROLLS_SNAPSHOT[d1] \cap INIT_ROLLS_SNAPSHOT[d2] = {}

\* initial active rolls
LOCAL init_active_rolls == UNION { INIT_ROLLS_SNAPSHOT[d] : d \in DELEGATES }

\* There must be at least as many baking slots per cycle as there active rolls
ASSUME MAX_BAKE * BLOCKS_PER_CYCLE >= init_active_rolls

LOCAL baking_slot_freq_threshold == 2

\* Baking priorities have the correct frequency of active rolls
ASSUME
    LET total_rolls == card(init_active_rolls)
        total_slots == MAX_BAKE * BLOCKS_PER_CYCLE
    IN
    \A c \in Cycles, r \in init_active_rolls :
        LET prio_lists == Map(LAMBDA bs : BAKING_PRIORITY[c][bs], SetToSeq(Block_slots))
            num_occs   == Sum(Map(LAMBDA seq : Num_occ(r, seq), prio_lists))
        IN
        abs(num_occs * total_rolls - total_slots) < baking_slot_freq_threshold

LOCAL endorsement_slot_freq_threshold == 2

\* Endorsement rights have the correct frequency of active rolls
ASSUME
    LET total_rolls == card(init_active_rolls)
        total_slots == MAX_ENDORSE * BLOCKS_PER_CYCLE
    IN
    \A c \in Cycles, r \in init_active_rolls :
        LET rights   == Map(LAMBDA bs : ENDORSEMENT_RIGHTS[c][bs][r], SetToSeq(Block_slots))
            num_occs == Sum(rights)
        IN
        abs(num_occs * total_rolls - total_slots) < endorsement_slot_freq_threshold

----

(*****************)
(* Initial state *)
(*****************)

Init ==
    /\ time               = 0
    /\ cycle              = 0
    /\ block_slot         = 0
    /\ phase              = "active"
    /\ balance            = INIT_BALANCE
    /\ rolls_snapshot     = INIT_ROLLS_SNAPSHOT
    /\ rolls_lifo         = inj_seq(inactive_rolls(0, 0))
    /\ all_blocks         = [ c \in Cycles |-> [ b \in Block_slots |-> {} ] ]
    /\ delegate_blocks    = [ c \in Cycles |-> [ b \in Block_slots |-> [ d \in DELEGATES |->
                                IF c = 0 /\ b = 0 THEN <<TRUE, 0, 0>> ELSE <<FALSE, 0, 0>>
                            ] ] ]
    /\ endorsements       = [ c \in Cycles |-> [ b \in Blocks |-> {} ] ]
    /\ safety_deposit     = [ c \in Cycles |-> [ b \in Block_slots |-> [ d \in DELEGATES |-> SAFETY_DEPOSIT] ] ]

(******************)
(* Type invariant *)
(******************)

TypeOK ==
    /\ time            \in All_time
    /\ cycle           \in Cycles
    /\ block_slot      \in Block_slots
    /\ balance         \in Balances
    /\ phase           \in Phases
    /\ all_blocks      \in [ Cycles -> [ Block_slots -> SUBSET Blocks ] ]
    /\ delegate_blocks \in [ Cycles -> [ Block_slots -> [ DELEGATES -> BOOLEAN \X ROLLS \X All_time ] ] ]
    /\ rolls_snapshot  \in [ Cycles -> [ Block_slots -> [ DELEGATES -> SUBSET ROLLS ] ] ]
    /\ rolls_lifo      \in inj_seq(inactive_rolls(cycle, block_slot))
    /\ endorsements    \in [ Cycles -> [ Block_slots -> [ DELEGATES -> SUBSET ROLLS ] ] ]
    /\ safety_deposit  \in [ Cycles -> [ Block_slots -> [ DELEGATES -> Deposits ] ] ]

----

(***********)
(* Helpers *)
(***********)

\* the baking priority of the given roll in the given cycle/baking slot
baking_priority(c, bs, r) == Index0(r, BAKING_PRIORITY[c][bs])

has_baking_rights(c, bs, r) == r \in ToSet(BAKING_PRIORITY[c][bs])

\* rolls with baking rights
nonzero_baking_rights(c, bs) == ToSet(BAKING_PRIORITY[c][bs])

\* set of rolls which have already baked in the given cycle/slot
already_baked(c, bs) == { b[1] : b \in all_blocks[c][bs] }

\* rolls with endorsement rights in the given cycle and block slot
nonzero_endorsement_rights(c, bs) == { r \in ROLLS : ENDORSEMENT_RIGHTS[c][bs][r] > 0 }

\* 
has_endorsement_rights(c, bs, r) == r \in nonzero_endorsement_rights(c, bs)

\* rolls which have endorsed a block in the given cycle/block slot
endorsers(c, bs) == UNION { endorsements[c][bs][r] : r \in ROLLS }

\* number of endorsements for the block baked by roll [r] in the given cycle/block slot
num_endorsements(c, bs, r) == card(endorsements[c][bs][r])

\* set of blocks baked in the previous cycle/block slot
prev_blocks(c, bs) ==
    IF c = 0 /\ bs = 0 THEN <<0, 0>>
    ELSE
        LET prev_c  == IF bs > 0 THEN c ELSE c - 1
            prev_bs == IF bs > 0 THEN bs - 1 ELSE max_slot
        IN
        all_blocks[prev_c][prev_bs]

\* latest block known by the delegate prior to the given cycle/block slot
\* returns <<cycle, block_slot, roll, time>>
RECURSIVE prev_delegate_block(_, _, _)
prev_delegate_block(c, bs, d) ==
    IF c = 0 /\ bs = 0 THEN <<0, 0, 0, 0>>
    ELSE
        LET prev_c  == IF bs > 0 THEN c ELSE c - 1
            prev_bs == IF bs > 0 THEN bs - 1 ELSE max_slot
            prev_b  == delegate_blocks[prev_c][prev_bs][d]
        IN
        IF prev_b[1] THEN <<prev_c, prev_bs, prev_b[2], prev_b[3]>>
        ELSE prev_delegate_block(prev_c, prev_bs, d)

\* time of the delegate's last known block
latest_block_time(c, bs, d) == prev_delegate_block(c, bs, d)[4]

cmp_time(b1, b2) == b1[2] <= b2[2]

\* @type: Seq(BLOCK) => Seq(ROLL);
roll_list_of_slice(blk_seq) == Map(Head, blk_seq)

\* block delay for the given roll in the given cycle/block slot
block_delay(c, bs, r) ==
    LET del == lookup_roll_opt(r)
        d   == del[2]
        p   == baking_priority(c, bs, r)
    IN
    IF p < 0 THEN MAX_BLOCK_DELAY
    ELSE
        LET prev_b == prev_delegate_block(c, bs, d) \* cycle * block_slot * roll * time
            cyc    == prev_b[1]
            slot   == prev_b[2]
            baker  == prev_b[3]
            e      == num_endorsements(cyc, slot, baker)
        IN
        BLOCK_DELAY[p][e]

has_baked_block(c, bs, r) == r \in { b[1] : b \in all_blocks[c][bs] }

\* list of <<cycle, block slot>> for which there is at least one block
curr_slots ==
    LET has_b   == all_blocks[cycle][block_slot] /= {}
        prev_c  == IF has_b \/ block_slot /= 0 THEN cycle ELSE cycle - 1
        prev_bs == IF has_b THEN block_slot ELSE IF block_slot /= 0 THEN block_slot - 1 ELSE max_slot
    IN
    (0..(prev_c - 1)) \X Block_slots \cup {prev_c} \X (0..prev_bs)

\* all cycle-block slot pairs in cycle [c]
cycle_slots(c) == SetToSeq({c} \X Block_slots)

\* given a cycle and block slot, returns <<cycle, block_slot>> for which delegate [d] knows of a block
RECURSIVE delegate_slots(_, _, _)
delegate_slots(c, bs, d) ==
    LET has_b   == delegate_blocks[c][bs][d][1]
        prev_c  == IF has_b \/ bs /= 0 THEN c ELSE c - 1
        prev_bs == IF has_b THEN bs ELSE IF bs /= 0 THEN bs - 1 ELSE max_slot
    IN
    IF ~has_b THEN delegate_slots(prev_c, prev_bs, d)
    ELSE (0..(prev_c - 1)) \X Block_slots \cup {prev_c} \X (0..prev_bs)

\* list of <<cycle, block slot>> for which the delegate knows of a block
curr_delegate_slots(d) == delegate_slots(cycle, block_slot, d)

\* @type: <<CYCLE, BLOCK_SLOT>> => BLOCK;
\* the best block is the lowest priority block with the most endorsements
best_block(cbs) ==
    LET c    == cbs[1]
        bs   == cbs[2]
        \* cycle * block_slot * roll * time
        blks == { <<c, bs, b[1], b[2]>> : b \in all_blocks[c][bs] }
        most_endorsed == { b \in blks : \A bb \in blks :
            card(endorsements[c][bs][b[3]]) >= card(endorsements[c][bs][bb[3]]) }
        lowest_prio == { b \in blks : \A bb \in blks :
            baking_priority(c, bs, b[3]) <= baking_priority(c, bs, bb[3]) }
    IN
    Pick(lowest_prio)

\* blocks of the chain in cycle [c]
slice(c) == Map(best_block, cycle_slots(c))

\* @type: Seq(<<CYCLE, BLOCK_SLOT, ROLL, TIME>>);
\* best chain up to the most recent block
chain == Map(best_block, SetToSeq(curr_slots))

\* delegate [d]'s view of the blockchain
delegate_slice(d) ==
    Map(LAMBDA cbs : LET b == delegate_blocks[cbs[1]][cbs[2]][d] IN <<b[2], b[3]>>,
        SetToSeq(curr_delegate_slots(d)) )

zero_reward_fn == [ d \in DELEGATES |-> 0 ]

add_to_fn(x, y, f) == [ f EXCEPT ![x] = @ + y ]

RECURSIVE convert(_, _)
convert(seq, f) ==
    IF seq = <<>> THEN f
    ELSE
        LET h == Head(seq)
            d == h[1]
            n == h[2]
        IN
        convert(Tail(seq), add_to_fn(d, n, f))

Convert(seq) == convert(seq, zero_reward_fn)

\* @type: Seq(<<CYCLE, BLOCK_SLOT, ROLL, TIME>>) => DELEGATE -> Int;
\* Converts a chain into a seq of baking rewards
baking_rewards(_slice) ==
    LET reward_pairs ==
        Map(LAMBDA q :
            LET c  == q[1]
                bs == q[2]
                r  == q[3]
                d  == lookup_roll_opt(r)[2]
            IN
            <<d, BAKING_REWARD[c][bs][r]>>,
            _slice)
    IN
    Convert(reward_pairs)

\* adding values of delgate functions
fn_add(f, g) == [ d \in DELEGATES |-> f[d] + g[d] ]

\* @type: (Set(<<CYCLE, BLOCK_SLOT, ROLL>>), DELEGATE -> Int) => DELEGATE -> Int;
RECURSIVE _reward_fn_of_endorsers(_, _)
_reward_fn_of_endorsers(c_bs_end_set, f) ==
    IF c_bs_end_set = {} THEN f
    ELSE
        LET cbse == Pick(c_bs_end_set)
            c    == cbse[1]               \* cycle
            bs   == cbse[2]               \* block slot
            r    == cbse[3]               \* endorsing roll
            d    == lookup_roll_opt(r)[2] \* delegate associated with endorsing roll [r]
        IN
        _reward_fn_of_endorsers(
            c_bs_end_set \ {cbse},
            add_to_fn(d, ENDORSEMENT_REWARD[c][bs][r] * ENDORSEMENT_RIGHTS[c][bs][r], f) )

reward_fn_of_endorsers(set) == _reward_fn_of_endorsers(set, zero_reward_fn)

RECURSIVE fold(_, _, _)
fold(comb(_, _), seq, acc) ==
    IF seq = <<>> THEN acc
    ELSE fold(comb, Tail(seq), comb(Head(seq), acc))

\* @type: Seq(<<CYCLE, BLOCK_SLOT, ROLL, TIME>>) => DELEGATE -> Int;
\* 
endorsement_rewards(_slice) ==
    LET reward_fns ==
        Map(LAMBDA q :
            LET c  == q[1]
                bs == q[2]
                r  == q[3]
                es == endorsements[c][bs][r]
            IN
            reward_fn_of_endorsers({ <<c, bs, e>> : e \in es}),
            _slice)
    IN
    fold(fn_add, reward_fns, zero_reward_fn)

\* 
RECURSIVE take_drop(_, _, _)
take_drop(n, seq, acc) ==
    IF n = 0 THEN <<acc, seq>>
    ELSE take_drop(n - 1, Tail(seq), Append(acc, Head(seq)))

Take_drop(n, seq) == take_drop(n, seq, <<>>)

(***********)
(* Actions *)
(***********)

phase_change(succ) == phase' = succ

incr_time ==
    /\ time < MAX_TIME
    /\ time' = time + 1

Tick ==
    /\ phase = "active"
    /\ incr_time
    /\ UNCHANGED non_time_vars

\* Increment block_slot if sufficiently small
\* otherwise increment cycle if sufficiently small
\* variables: block_slot, cycle
incr_block_slot ==
    \* increments suff small block_slot
    CASE block_slot < max_slot ->
            /\ block_slot' = block_slot + 1
            /\ UNCHANGED cycle
    \* increments suff small cycle
         [] cycle < MAX_CYCLE ->
            /\ block_slot' = 0
            /\ cycle' = cycle + 1
    \* disables action
         [] OTHER ->
            /\ FALSE
            /\ UNCHANGED <<block_slot, cycle>>

\* if a block has been baked and suff endorsed in the current slot, we can progress to the next slot
IncrBlockSlot == \E r \in ROLLS :
    /\ phase = "active"
    /\ block_slot /= 0 => block_slot % max_slot /= 0
    /\ has_baked_block(cycle, block_slot, r)
    /\ num_endorsements(cycle, block_slot, r) >= MIN_ENDORSE
    /\ incr_block_slot
    /\ UNCHANGED non_slot_vars

\* active roll [r] bakes a block on top of [prev_block]
bake_block(prev_block, r) ==
    LET del == lookup_roll_opt(r)
        d   == del[2]
    IN
    /\ del[1]
    /\ time >= latest_block_time(cycle, block_slot, r) + block_delay(cycle, block_slot, d)
    /\ all_blocks'      = [ all_blocks      EXCEPT ![cycle][block_slot] = @ \cup {<<r, time>>} ]
    /\ delegate_blocks' = [ delegate_blocks EXCEPT ![cycle][block_slot][d] = <<TRUE, r, time>> ]
    /\ UNCHANGED non_block_vars \* time intentionally missing

\* A roll with baking rights bakes a block
Bake == \E r \in nonzero_baking_rights(cycle, block_slot) :
    LET del == lookup_roll_opt(r)
        d   == del[2]
        b   == prev_delegate_block(cycle, block_slot, d)
    IN
    /\ time < MAX_TIME
    /\ phase = "active"
    /\ isSome(del)
    /\ r \notin already_baked(cycle, block_slot)
    /\ incr_time
    /\ bake_block(b, r)

\* A roll with endorsement rights endorses a block
Endorse == \E r \in nonzero_endorsement_rights(cycle, block_slot), b \in all_blocks[cycle][block_slot] :
    LET del == lookup_roll_opt(r)
        d   == del[2]
        bkr == b[1]
        t   == b[2]
    IN
    /\ time < MAX_TIME
    /\ phase = "active"
    /\ isSome(del)                           \* [r] is an active roll
    /\ r \notin endorsers(cycle, block_slot) \* [d] has not already endorsed a block in this slot
    /\ endorsements'    = [ endorsements    EXCEPT ![cycle][block_slot][bkr] = @ \cup {r} ]
    /\ delegate_blocks' = [ delegate_blocks EXCEPT ![cycle][block_slot][d] = <<TRUE, bkr, t>> ]
    /\ UNCHANGED <<time, all_blocks, non_block_vars>>

\* A delegate which does not have a block in a given cycle/block slot includes an existing one
\* TODO exclude delegates with baking or endorsement slots?
IncludeBlock == \E d \in DELEGATES, c \in Cycles, bs \in Block_slots :
    \E b \in all_blocks[c][bs] :
        /\ phase = "active"
        /\ c <= cycle
        /\ c < cycle => bs <= block_slot
        \* time/prioroity
        /\ ~delegate_blocks[c][bs][d][1] \* [d] does not have a block in this cycle/block slot
        /\ delegate_blocks' = [ delegate_blocks EXCEPT ![c][bs][d] = b ]
        /\ UNCHANGED non_del_vars

\* 
rewards(_slice) ==
    LET rewards_from_baking    == baking_rewards(_slice)
        rewards_from_endorsing == endorsement_rewards(_slice)
    IN
    fn_add(rewards_from_baking, rewards_from_endorsing)

\* Transitions
\* once a block has been endorsed by suff many endorsers in the last slot of the cycle
\* we temporarily stop baking/endorsing to credit rewards and manage the rolls
ActiveToAdmin == \E r \in ROLLS :
    /\ time < MAX_TIME
    /\ phase = "active"
    /\ num_endorsements(cycle, block_slot, r) >= MIN_ENDORSE
    /\ block_slot = max_slot
    /\ phase_change("cycle_admin")
    \* /\ IF block_slot = max_slot
    \*    THEN phase_change("cycle_admin")
    \*    ELSE /\ block_slot /= 0
    \*         /\ block_slot % max_slot = 0
    \*         /\ phase_change("snapshot_admin")
    /\ UNCHANGED non_phase_vars

\* SnapshotAdminToActive == \E r \in nonzero_baking_rights(cycle, block_slot) :
\*     /\ time < MAX_TIME
\*     /\ phase = "snapshot_admin"
\*     /\ phase_change("active")
\*     /\ BakingReward(cycle, block_slot, r)
\*     /\ EndorsementRewards(cycle, block_slot)
\*     \* /\ manage_rolls
\*     \* /\ update snapshot
\*     /\ incr_block_slot
\*     /\ UNCHANGED <<time, all_blocks, delegate_blocks, endorsements>>

\* TODO
deposit_management == {}

\* functional update of rolls_snapshot and rolls_lifo
RECURSIVE roll_management(_, _, _)
roll_management(snapshot, lifo, rem_dels) ==
    IF rem_dels = {} THEN <<snapshot, lifo>>
    ELSE
        LET d       == Pick(rem_dels)
            bal     == balance[cycle][max_slot][d]
            delta   == balance'[cycle][max_slot][d] - bal + loose(bal)
            new_rem == rem_dels \ {d}
        IN
        IF delta < TOKENS_PER_ROLL THEN roll_management(snapshot, lifo, new_rem)
        ELSE
            LET n         == delta \div TOKENS_PER_ROLL
                roll_pair == Take_drop(n, lifo)
                new_snap  == snapshot[cycle][max_slot][d] \cup ToSet(roll_pair[1])
                new_lifo  == roll_pair[2]
            IN
            roll_management([ snapshot EXCEPT ![cycle][max_slot][d] = new_snap ], new_lifo, new_rem)

\* Once we complete reward allocations and roll management,
\* we move to the active phase in the next block slot
CycleAdminToActive == \E r \in nonzero_baking_rights(cycle, block_slot) :
    /\ time < MAX_TIME
    /\ phase = "cycle_admin"
    /\ phase_change("active")
    /\ balance' = [ balance EXCEPT ![cycle][block_slot] = fn_add(@, rewards(slice(cycle))) ]
    \* /\ deposit_management
    /\ LET pair == roll_management(rolls_snapshot, rolls_lifo, DELEGATES) IN
        /\ rolls_snapshot' = pair[1]
        /\ rolls_lifo'     = pair[2]
    /\ incr_block_slot
    /\ UNCHANGED <<time, all_blocks, delegate_blocks, endorsements>>

Next ==
    \/ Tick
    \/ Bake
    \/ Endorse
    \/ IncludeBlock
    \/ IncrBlockSlot
    \/ ActiveToAdmin
    \/ CycleAdminToActive
    \* \/ SnapshotAdminToActive

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

(**************)
(* Properties *)
(**************)

\* TODO
CorrectFrequencyOfBakingPriorities == \A c \in Cycles, bs \in Block_slots :
    \A r \in active_rolls(c, bs) :
    LET total_rolls == card(active_rolls(c, bs))
        total_slots == MAX_BAKE * BLOCKS_PER_CYCLE
        prio_lists  == Map(LAMBDA b : BAKING_PRIORITY[c][b], SetToSeq(Block_slots))
        num_occs    == Sum(Map(LAMBDA seq : Num_occ(r, seq), prio_lists))
    IN
    abs(num_occs * total_rolls - total_slots) < baking_slot_freq_threshold

\* TODO
CorrectFrequencyOfEndorsingRights == \A c \in Cycles, bs \in Block_slots :
    \A r \in active_rolls(c, bs) :
    LET total_rolls == card(active_rolls(c, bs))
        total_slots == MAX_ENDORSE * BLOCKS_PER_CYCLE
        rights      == Map(LAMBDA b : ENDORSEMENT_RIGHTS[c][b][r], SetToSeq(Block_slots))
        num_occs    == Sum(rights)
    IN
    abs(num_occs * total_rolls - total_slots) < endorsement_slot_freq_threshold

\* rolls are neither created nor destroyed
RollConservation == \A c \in Cycles, bs \in Block_slots :
    active_rolls(c, bs) \cup ToSet(rolls_lifo[c][bs]) = ROLLS

BalanceRollCorrectness == \A c \in Cycles, bs \in Block_slots, d \in DELEGATES :
    balance[c][bs][d] \div TOKENS_PER_ROLL = card(rolls_snapshot[c][bs][d])

DisjointRolls == \A c \in Cycles, bs \in Block_slots, d1, d2 \in DELEGATES :
    rolls_snapshot[c][bs][d1] \cap rolls_snapshot[c][bs][d2] = {}

BakersHaveNonzeroPriorityForBakedSlots == \A c \in Cycles, b \in Block_slots :
    LET rts == all_blocks[c][b] IN
    \/ rts = {}
    \/ rts /= {} =>
        \A blk \in rts : \E r \in ToSet(BAKING_PRIORITY[c][b]) : r = rts[1]

EndorsersHaveNonzeroRightsForEndorsedSlots == \A c \in Cycles, bs \in Block_slots :
    LET blks == all_blocks[c][bs] IN
    \/ blks = {}
    \/ blks /= {} =>
        LET bkr == Pick(blks)[1] IN
        \A end \in endorsements[c][bs][bkr] : ENDORSEMENT_RIGHTS[c][bs][end] > 0

DelegateChainsAlwaysConsistOfRealBlocks == \A c \in Cycles, bs \in Block_slots, d \in DELEGATES :
    LET del_b      == delegate_blocks[c][bs][d]
        if_del_blk == del_b[1]
        del_blk    == <<del_b[2], del_b[3]>>
    IN
    if_del_blk => del_blk \in all_blocks[c][bs]

\* TODO more properties

\* delegate chains are contiguous
\* all blocks are valid
\* chain health - blocks have priority 0 and almost all (80%?) endorsement slots are filled
\*   properties of healthy chains Seq(roll)
\* double baking & double endorsing

==========================
