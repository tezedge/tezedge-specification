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
    TOKENS_PER_ROLL,        \* 8000
    BLOCKS_PER_CYCLE,       \* 8192
    BLOCKS_PER_SNAPSHOT,    \* number of blocks between roll snapshots
    INIT_BALANCE,           \* delegate -> int
    INIT_ROLLS_SNAPSHOT,    \* delegate -> Set(roll)
    SAFETY_DEPOSIT,         \* delegate -> int
    BAKING_PRIORITY,        \* cycle -> block_slot -> Seq(roll)
    ENDORSEMENT_RIGHTS,     \* cycle -> block_slot -> roll -> int
    BAKING_REWARD,          \* cycle -> block_slot -> delegate -> int
    ENDORSEMENT_REWARD      \* cycle -> block_slot -> delegate -> int

VARIABLES
    time,                   \* timestamp: 1 time ~ MIN_BLOCK_DELAY
    cycle,                  \* int
    block_slot,             \* int
    phase,                  \* phase \in { "active", "cycle_admin", "snapshot_admin" }
    all_blocks,             \* cycle -> block -> Set(roll * time)
    delegate_blocks,        \* cycle -> block_slot -> delegate -> bool * roll * time
    balance,                \* cycle -> block_slot -> delegate -> int
    baking_reward,          \* cycle -> block_slot -> delegate -> int
    endorsement_reward,     \* cycle -> block_slot -> delegate -> int
    rolls_snapshot,         \* cycle -> block_slot -> delegate -> Set(roll)
    rolls_lifo,             \* cycle -> block_slot -> Seq(roll)
    endorsements,           \* cycle -> block_slot -> roll -> Set(roll)
    safety_deposit          \* cycle -> delegate -> int

\* inclusive variables


\* exclusive variables
non_block_vars == <<time, cycle, block_slot, phase, balance, baking_reward, endorsement_reward, rolls_snapshot, rolls_lifo, endorsements>>
non_phase_vars == <<time, cycle, block_slot, all_blocks, delegate_blocks, balance, baking_reward, endorsement_reward, rolls_snapshot, rolls_lifo, endorsements>>
non_slot_vars  == <<time, phase, all_blocks, delegate_blocks, balance, baking_reward, endorsement_reward, rolls_snapshot, rolls_lifo, endorsements>>
non_time_vars  == <<cycle, block_slot, phase, all_blocks, delegate_blocks, balance, baking_reward, endorsement_reward, rolls_snapshot, rolls_lifo, endorsements>>

\* all variables
vars == <<time, cycle, block_slot, phase, all_blocks, delegate_blocks, balance, baking_reward, endorsement_reward, rolls_snapshot, rolls_lifo, endorsements>>

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

Deposits == {0} \cup {SAFETY_DEPOSIT}

Phases == { "active", "cycle_admin", "snapshot_admin" }

Rewards == 0..MAX_REWARD

card(set) == Cardinality(set)

ToSet(seq) == { seq[i] : i \in DOMAIN seq }

Pick(set) ==
    CASE set /= {} -> CHOOSE x \in set : TRUE
      [] OTHER -> PrintT("Cannot supply an element of the empty set")

max(a, b) == IF a >= b THEN a ELSE b

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

Max_baking_reward == 20

\* MAX_TIME is at least as long as the time is would take to bake all blocks at priority 0
ASSUME MAX_TIME >= (MAX_CYCLE + 1) * BLOCKS_PER_CYCLE * MIN_BLOCK_DELAY

\* MAX_REWARD is at least as large as the rewards accrued for baking all blocks in a cycle at priority 0
ASSUME MAX_REWARD >= card(Block_slots) * Max_baking_reward

ASSUME \A p \in 0..MAX_BAKE, e \in 0..MAX_ENDORSE :
    /\ BLOCK_DELAY[p][e] >= MIN_BLOCK_DELAY
    /\ BLOCK_DELAY[p][e] <= MAX_BLOCK_DELAY

\* there are always MAX_ENDORSE endorsement slots in each block slot
ASSUME \A c \in Cycles, bs \in Block_slots : Len(BAKING_PRIORITY[c][bs]) = MAX_BAKE

\* there are always MAX_ENDORSE endorsement slots in each block slot
ASSUME \A c \in Cycles, bs \in Block_slots :
    Sum(Map(LAMBDA r : ENDORSEMENT_RIGHTS[c][bs][r], SetToSeq(ROLLS))) = MAX_ENDORSE

\* initial rolls are disjoint
ASSUME \A d1, d2 \in DELEGATES : d1 /= d2 => INIT_ROLLS_SNAPSHOT[d1] \cap INIT_ROLLS_SNAPSHOT[d2] = {}

\* initial active rolls
init_active_rolls == UNION { INIT_ROLLS_SNAPSHOT[d] : d \in DELEGATES }

\* there must be at least as many baking slots per cycle as there active rolls
ASSUME MAX_BAKE * BLOCKS_PER_CYCLE >= init_active_rolls

baking_slot_freq_threshold == 2

\* baking priorities have the correct frequency of active rolls
ASSUME
    LET total_rolls == card(init_active_rolls)
        total_slots == MAX_BAKE * BLOCKS_PER_CYCLE
    IN
    \A c \in Cycles, r \in init_active_rolls :
        LET prio_lists == Map(LAMBDA bs : BAKING_PRIORITY[c][bs], SetToSeq(Block_slots))
            num_occs   == Sum(Map(LAMBDA seq : Num_occ(r, seq), prio_lists))
        IN
        abs(num_occs * total_rolls - total_slots) < baking_slot_freq_threshold

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
    /\ baking_reward      = [ c \in Cycles |-> [ b \in Block_slots |-> [ d \in DELEGATES |-> 0 ] ] ]
    /\ endorsement_reward = [ c \in Cycles |-> [ b \in Block_slots |-> [ d \in DELEGATES |-> 0 ] ] ]
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
    /\ baking_reward   \in [ Cycles -> [ Block_slots -> [ DELEGATES -> Nat ] ] ]
    /\ endorsements    \in [ Cycles -> [ Block_slots -> [ DELEGATES -> SUBSET ROLLS ] ] ]
    /\ safety_deposit  \in [ Cycles -> [ Block_slots -> [ DELEGATES -> Deposits ] ] ]

----

(***********)
(* Helpers *)
(***********)

baking_priority(c, bs, r) == Index0(r, BAKING_PRIORITY[c][bs])

has_baking_rights(c, bs, r) == r \in ToSet(BAKING_PRIORITY[c][bs])

endorsers(c, bs) == UNION { endorsements[c][bs][r] : r \in ROLLS }

num_endorsements(c, bs, r) == card(endorsements[c][bs][r])

prev_blocks(c, bs) ==
    IF c = 0 /\ bs = 0 THEN <<0, 0>>
    ELSE
        LET prev_c  == IF bs > 0 THEN c ELSE c - 1
            prev_bs == IF bs > 0 THEN bs - 1 ELSE max_slot
        IN
        all_blocks[prev_c][prev_bs]

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

\* rolls with baking rights
nonzero_baking_rights(c, bs) == ToSet(BAKING_PRIORITY[c][bs])

\* rolls with endorsement rights in the given cycle and block slot
nonzero_endorsement_rights(c, bs) == { r \in ROLLS : ENDORSEMENT_RIGHTS[c][bs][r] > 0 }

phase_change(succ) == phase' = succ

cmp_time(b1, b2) == b1[2] <= b2[2]

roll_list_of_blocks(blks) ==
    LET sorted == SortSeq(SetToSeq(blks), cmp_time) IN
    Map(Head, sorted)

\* roll -> time
block_delay(c, bs, d) ==
    LET r == rolls_snapshot[c][bs][d]
        p == baking_priority(c, bs, r)
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

\* given a cycle and block slot, returns <<cycle, block_slot>> for which [d] knows of a block
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

\* best chain up to the most recent block
chain ==
    \* the best block is the lowest priority block with the most endorsements
    LET best_block(cbs) ==
        LET c    == cbs[1]
            bs   == cbs[2]
            \* cycle * block_slot * roll * time
            blks == { <<c, bs, b[1], b[2]>> : b \in all_blocks[c][bs] }
            most_endorsed == { b \in blks : \A bb \in blks :
                card(endorsements[c][bs][b[3]]) >= card(endorsements[c][bs][bb[3]])
            }
            lowest_prio == { b \in blks : \A bb \in blks :
                baking_priority(c, bs, b[3]) <= baking_priority(c, bs, bb[3])
            }
        IN Pick(lowest_prio)
    IN
    Map(best_block, SetToSeq(curr_slots))

\* [d]'s view of the blockchain
delegate_chain(d) ==
    Map(LAMBDA cbs :
            LET b == delegate_blocks[cbs[1]][cbs[2]][d] IN <<b[2], b[3]>>,
        SetToSeq(curr_delegate_slots(d))
    )

(***********)
(* Actions *)
(***********)

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
    CASE block_slot < BLOCKS_PER_CYCLE - 1 ->
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
    /\ block_slot % BLOCKS_PER_CYCLE /= 0
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
    /\ UNCHANGED non_block_vars

\* 
Bake == \E r \in nonzero_baking_rights(cycle, block_slot) :
    LET del == lookup_roll_opt(r)
        d   == del[2]
        b   == prev_delegate_block(cycle, block_slot, d)
    IN
    /\ time < MAX_TIME
    /\ block_slot % BLOCKS_PER_CYCLE /= 0
    /\ phase = "active"
    /\ isSome(del)
    /\ incr_time
    /\ bake_block(b, r)

\* 
Endorse == \E r \in nonzero_endorsement_rights(cycle, block_slot), b \in all_blocks[cycle][block_slot] :
    LET del == lookup_roll_opt(r)
        d   == del[2]
        bkr == b[1]
        t   == b[2]
    IN
    /\ time < MAX_TIME
    /\ block_slot % BLOCKS_PER_CYCLE /= 0
    /\ phase = "active"
    /\ isSome(del)                                    \* [r] is an active roll
    /\ ~isSome(delegate_blocks[cycle][block_slot][d]) \* [d] has not already baked or endorsed a block in this slot
    /\ endorsements'    = [ endorsements    EXCEPT ![cycle][block_slot][bkr] = @ \cup {r} ]
    /\ delegate_blocks' = [ delegate_blocks EXCEPT ![cycle][block_slot][d] = <<TRUE, bkr, t>> ]
    /\ UNCHANGED <<all_blocks, non_block_vars>>

\* variables: balance, rolls_lifo, rolls_snapshot
adjust_rolls(type, amt, d) ==
    LET bal == balance[cycle][block_slot][d] IN
    CASE type = "add" ->
        IF amt + loose(bal) >= TOKENS_PER_ROLL THEN
            /\ balance'        = [ balance EXCEPT ![cycle][block_slot][d] = @ + amt ]
            /\ rolls_lifo'     = Tail(rolls_lifo)
            /\ rolls_snapshot' = [ rolls_snapshot EXCEPT ![cycle][block_slot][d] = @ \cup {Head(rolls_lifo)} ]
        ELSE
            /\ balance' = [ balance EXCEPT ![cycle][block_slot][d] = @ + amt ]
            /\ UNCHANGED <<rolls_lifo, rolls_snapshot>>
      [] type = "sub" ->
        IF amt > loose(bal) THEN
            LET r == Pick(rolls_snapshot[cycle][block_slot][d]) IN
            /\ balance'        = [ balance EXCEPT ![cycle][block_slot][d] = @ - amt ]
            /\ rolls_lifo'     = <<r>> \o rolls_lifo
            /\ rolls_snapshot' = [ rolls_snapshot EXCEPT ![cycle][block_slot][d] = @ \ {r} ]
        ELSE
            /\ balance' = [ balance EXCEPT ![cycle][block_slot][d] = @ - amt ]
            /\ UNCHANGED <<rolls_lifo, rolls_snapshot>>

\* calculate and distribute baking reward
\* variables: baking_reward
BakingReward(c, bs, r) == \E d \in DELEGATES :
    LET dp  == lookup_roll_opt(r)
        del == dp[2]
        rew == BAKING_REWARD[c][bs][d]
    IN
    \E new_roll \in inactive_rolls(c, bs) :
        /\ phase = "admin"
        /\ isSome(dp)
        /\ del = d
        /\ baking_reward' = [ baking_reward EXCEPT ![c][bs][d] = @ + rew ]

\* calculate endorsement rewards
\* variables: endorsement_reward
EndorsementRewards(c, bs) == \A r \in endorsers(c, bs) :
    LET dp  == lookup_roll_opt(r) \* bool * delegate
        d   == dp[2]
        rew == ENDORSEMENT_REWARD[c][bs][d] * ENDORSEMENT_RIGHTS[c][bs][r]
    IN
    /\ phase = "admin"
    /\ isSome(dp)
    /\ endorsement_reward' = [ endorsement_reward EXCEPT ![c][bs][d] = @ + rew ]

\* Transitions
\* once a block has been endorsed by suff many endorsers in "snapshot slot"
\* we temporarily stop baking/endorsing and 
ActiveToAdmin == \E r \in ROLLS :
    /\ time < MAX_TIME
    /\ phase = "active"
    /\ num_endorsements(cycle, block_slot, r) >= MIN_ENDORSE
    /\ IF block_slot = BLOCKS_PER_CYCLE
       THEN phase_change("cycle_admin")
       ELSE /\ block_slot % BLOCKS_PER_SNAPSHOT = 0
            /\ phase_change("snapshot_admin")
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

\* 
CycleAdminToActive == \E r \in nonzero_baking_rights(cycle, block_slot) :
    /\ time < MAX_TIME
    /\ phase = "cycle_admin"
    /\ phase_change("active")
    /\ BakingReward(cycle, block_slot, r)
    /\ EndorsementRewards(cycle, block_slot)
    \* /\ safety deposit management
    \* /\ roll management
    /\ incr_block_slot
    /\ UNCHANGED <<time, all_blocks, delegate_blocks, endorsements>>

Next ==
    \/ Tick
    \/ Bake
    \/ Endorse
    \/ IncrBlockSlot
    \/ ActiveToAdmin
    \/ CycleAdminToActive
    \* \/ SnapshotAdminToActive

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

(**************)
(* Properties *)
(**************)

BalanceRollCorrectness == \A c \in Cycles, bs \in Block_slots, d \in DELEGATES :
    balance[c][bs][d] \div TOKENS_PER_ROLL = card(rolls_snapshot[c][bs][d])

DisjointRolls == \A c \in Cycles, bs \in Block_slots, d1, d2 \in DELEGATES :
    rolls_snapshot[c][bs][d1] \cap rolls_snapshot[c][bs][d2] = {}

BakersHaveNonzeroPriorityForBakedSlots == \A c \in Cycles, b \in Block_slots :
    LET rts == all_blocks[c][b] IN
    \/ rts = {}
    \/ rts /= {} => \A blk \in rts : \E r \in ToSet(BAKING_PRIORITY[c][b]) : r = rts[1]

EndorsersHaveNonzeroPriorityForEndorsedSlots == \A c \in Cycles, b \in Block_slots :
    LET blks == all_blocks[c][b] IN
    \/ blks = {}
    \/ blks /= {} =>
        LET r == Pick(blks)[1] IN
        ENDORSEMENT_RIGHTS[c][b][r] > 0

\* TODO more properties

\* delegate chains always consist of blocks from all_blocks

\* TODO
\* chain health - blocks have priority 0 and almost all (80%?) endorsement slots are filled
\*   properties of healthy chains Seq(roll)

\* Double baking & double endorsing

==========================
