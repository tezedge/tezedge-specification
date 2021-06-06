---- MODULE Consensus ----

EXTENDS FiniteSets, Integers, Naturals, Sequences, TLC

CONSTANTS
    ROLLS,                  \* set of roll ids
    DELEGATES,              \* set of delegate ids
    MAX_BAKE,               \* maximum number of bakers per block slot
    MAX_CYCLE,              \* last cycle
    MAX_ENDORSE,            \* maximum number of endorsements per block
    MAX_TIME,               \* maximum time
    MAX_BALANCE,            \* maximum balance a delegate can have
    MAX_DEPOSIT,            \* maximum deposit
    MAX_REWARD,             \* maximum baking/endorsement reward
    MIN_ENDORSE,            \* minimum number of endorses to close a block
    MIN_BLOCK_DELAY,        \* minimum block delay
    BAKING_DELAY,           \* delay per missed baking slot
    ENDORSEMENT_DELAY,      \* delay per missing endorsement
    INITIAL_ENDORSERS,      \* number of endorsements required to not incure additional block delay
    TOKENS_PER_ROLL,        \* 8000
    BLOCKS_PER_CYCLE,       \* 8192
    BLOCKS_PER_SNAPSHOT,    \* number of blocks between roll snapshots
    INIT_BALANCE,           \* delegate -> int
    INIT_ROLLS_SNAPSHOT,    \* delegate -> Set(roll)
    INIT_SAFETY_DEPOSIT,    \* delegate -> int
    BAKING_PRIORITY,        \* cycle -> block_slot -> Seq(roll)
    ENDORSEMENT_RIGHTS,     \* cycle -> block_slot -> roll -> int
    BAKING_REWARD,          \* cycle -> block_slot -> delegate -> int
    ENDORSEMENT_REWARD      \* cycle -> block_slot -> delegate -> int

VARIABLES
    time,               \* timestamp: 1 time ~ MIN_BLOCK_DELAY
    cycle,              \* int
    block_slot,         \* int
    phase,              \* phase \in { "active", "cycle_admin", "snapshot_admin" }
    all_blocks,         \* cycle -> block -> Set(roll * time)
    delegate_blocks,    \* cycle -> block_slot -> delegate -> bool * roll * time
    balance,            \* cycle -> block_slot -> delegate -> int
    baking_reward,      \* cycle -> block_slot -> delegate -> int
    endorsement_reward, \* cycle -> block_slot -> delegate -> int
    rolls_snapshot,     \* cycle -> block_slot -> delegate -> Set(roll)
    rolls_lifo,         \* cycle -> block_slot -> Seq(roll)
    endorsements,       \* cycle -> block_slot -> roll -> Set(roll)
    safety_deposit      \* cycle -> delegate -> int

\* inclusive variables


\* exclusive variables
non_phase_vars == <<time, cycle, block_slot, all_blocks, delegate_blocks, balance, baking_reward, endorsement_reward, rolls_snapshot, rolls_lifo, endorsements>>
non_time_vars == <<cycle, block_slot, phase, all_blocks, delegate_blocks, balance, baking_reward, endorsement_reward, rolls_snapshot, rolls_lifo, endorsements>>

\* all variables
vars == <<time, cycle, block_slot, phase, all_blocks, delegate_blocks, balance, baking_reward, endorsement_reward, rolls_snapshot, rolls_lifo, endorsements>>

----

All_time == 0..MAX_TIME

Cycles == 0..MAX_CYCLE

Balances == 0..MAX_BALANCE

max_slot == BLOCKS_PER_CYCLE - 1

Block_slots == 0..max_slot

Blocks == ROLLS \X All_time

Deposits == 0..MAX_DEPOSIT

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
Index(x, seq) == index(x, seq, 0)

active_rolls(c, bs) == UNION { rolls_snapshot[c][bs][d] : d \in DELEGATES }

inactive_rolls(c, bs) == ROLLS \ active_rolls(c, bs)

RECURSIVE num_occ(_, _, _)
num_occ(x, s, acc) ==
    IF s = <<>> THEN acc
    ELSE
        LET new_acc == IF x /= Head(s) THEN acc ELSE acc + 1 IN
        num_occ(x, s, new_acc)

RECURSIVE seq_n(_, _, _, _)
seq_n(S, n, N, acc) ==
    IF n = N THEN acc
    ELSE
        LET new_acc == { Append(s, x) : s \in acc, x \in S } IN
        seq_n(S, n + 1, N, new_acc)

\* sequences of S of length n
Seq_n(S, n) == seq_n(S, 0, n, {<<>>})

\* injective sequences of S, length = card(S)
inj_seq(S) == { s \in Seq_n(S, card(S)) : \A x \in ToSet(s) : num_occ(x, s, 0) = 1 }

----

\* MAX_TIME is at least as long as the time is would take to bake all blocks at priority 0
ASSUME MAX_TIME >= card(Cycles) * card(Block_slots) * MIN_BLOCK_DELAY

ASSUME \A c \in Cycles, b \in Block_slots : Len(BAKING_PRIORITY[c][b]) <= MAX_BAKE

ASSUME \A c \in Cycles, b \in Block_slots :
    Sum(Map(LAMBDA r : ENDORSEMENT_RIGHTS[c][b][r], SetToSeq(ROLLS))) <= MAX_ENDORSE

ASSUME \A d1, d2 \in DELEGATES : d1 /= d2 => INIT_ROLLS_SNAPSHOT[d1] \cap INIT_ROLLS_SNAPSHOT[d2] = {}

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
    /\ safety_deposit     = [ c \in Cycles |-> [ b \in Block_slots |-> [ d \in DELEGATES |-> INIT_SAFETY_DEPOSIT] ] ]

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
    /\ endorsements    \in [ Cycles -> [ Blocks -> 0..MAX_ENDORSE ] ]
    /\ safety_deposit  \in [ Cycles -> [ Block_slots -> [ DELEGATES -> Deposits ] ] ]

----

(***************)
(* Block delay *)
(***************)
\*
\* emmy_delay(p) = MIN_BLOCK_DELAY + BAKING_DELAY * p
\*
\* emmy_plus_delay(p, e) =
\*   MIN_BLOCK_DELAY + BAKING_DELAY * p + ENDORSEMENT_DELAY * max(0, INITIAL_ENDORSERS - e)
\* where
\*   BAKING_DELAY      (40) - delay per missing baking slot
\*   ENDORSEMENT_DELAY (8)  - delay per missing endorsement
\*   INITIAL_ENDORSERS (24) - threshold of endorsers needed to get least delay
\*
\* emmy_star_delay(p, e) ==
\*     IF p = 0 /\ 5 * e >= 3 * MAX_ENDORSE THEN MIN_BLOCK_DELAY
\*     ELSE emmy_plus_delay(p, e)

----

baking_priority(c, bs, r) == Index(r, BAKING_PRIORITY[c][bs]) - 1

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

\* Get [d]'s current roll snapshot
current_snapshot_rolls(d) == rolls_snapshot[cycle][block_slot][d]

\* Get delegate id associated with roll [r]
lookup_roll_opt(r) ==
    LET s == { d \in DELEGATES : current_snapshot_rolls(d) = r } IN
    IF s /= {} THEN <<TRUE, Pick(s)>>
    ELSE <<FALSE, 0>>

isSome(opt) == opt[1]

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
    IF p < 0 THEN MAX_TIME \* TODO max_delay for non-priority rolls
    ELSE
        LET prev_b == prev_delegate_block(c, bs, d) \* cycle * block_slot * roll * time
            cyc    == prev_b[1]
            slot   == prev_b[2]
            baker  == prev_b[3]
            e      == num_endorsements(cyc, slot, baker)
        IN
        MIN_BLOCK_DELAY + BAKING_DELAY * p + ENDORSEMENT_DELAY * max(0, INITIAL_ENDORSERS - e)

has_baked_block(c, bs, r) == r \in { b[1] : b \in all_blocks[c][bs] }

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

IncrBlockSlot == \E r \in ROLLS :
    /\ phase = "active"
    /\ has_baked_block(cycle, block_slot, r)
    /\ num_endorsements(cycle, block_slot, r) >= MIN_ENDORSE
    \* increments suff small block_slot
    /\ CASE block_slot < BLOCKS_PER_CYCLE - 1 ->
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

\* an active roll bakes a block on top of [prev_block]
bake_block(prev_block, r) ==
    LET del == lookup_roll_opt(r)
        d   == del[2]
    IN
    /\ del[1]
    /\ time >= latest_block_time(cycle, block_slot, r) + block_delay(cycle, block_slot, d)
    /\ all_blocks'      = [ all_blocks      EXCEPT ![cycle][block_slot] = @ \cup {<<r, time>>} ]
    /\ delegate_blocks' = [ delegate_blocks EXCEPT ![cycle][block_slot][d] = <<TRUE, r, time>> ]
    /\ UNCHANGED <<phase>> \* TODO

\* 
Bake == \E r \in nonzero_baking_rights(cycle, block_slot) :
    LET del == lookup_roll_opt(r)
        d   == del[2]
        b   == prev_delegate_block(cycle, block_slot, d)
    IN
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
    /\ phase = "active"
    /\ isSome(del)                                    \* [r] is an active roll
    /\ ~isSome(delegate_blocks[cycle][block_slot][d]) \* [d] has not already baked or endorsed a block in this slot
    /\ endorsements'    = [ endorsements    EXCEPT ![cycle][block_slot][bkr] = @ \cup {r} ]
    /\ delegate_blocks' = [ delegate_blocks EXCEPT ![cycle][block_slot][d] = <<TRUE, bkr, t>> ]
    /\ UNCHANGED <<>> \* TODO

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
        reward == BAKING_REWARD[c][bs][d]
    IN
    \E new_roll \in inactive_rolls(c, bs) :
        /\ phase = "admin"
        /\ isSome(dp)
        /\ del = d
        /\ baking_reward' = [ baking_reward EXCEPT ![c][bs][d] = @ + reward ]

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
    /\ phase = "active"
    /\ num_endorsements(cycle, block_slot, r) >= MIN_ENDORSE
    /\ IF block_slot = BLOCKS_PER_CYCLE - 1
       THEN phase_change("cycle_admin")
       ELSE /\ block_slot % BLOCKS_PER_SNAPSHOT
            /\ phase_change("snapshot_admin")
    /\ UNCHANGED non_phase_vars \* TODO

\* 
SnapshotAdminToActive == \E r \in nonzero_baking_rights(cycle, block_slot) :
    /\ phase = "snapshot_admin"
    /\ num_endorsements(cycle, block_slot, r) >= MIN_ENDORSE
    /\ phase_change("active")
    /\ BakingReward(cycle, block_slot, r)
    /\ EndorsementRewards(cycle, block_slot)
    /\ UNCHANGED <<>> \* TODO

\* 
CycleAdminToActive == \E r \in nonzero_baking_rights(cycle, block_slot) :
    /\ phase = "cycle_admin"
    /\ num_endorsements(cycle, block_slot, r) >= MIN_ENDORSE
    /\ phase_change("active")
    /\ BakingReward(cycle, block_slot, r)
    /\ EndorsementRewards(cycle, block_slot)
    /\ UNCHANGED <<>> \* TODO

\* TODO
\* - safety deposit management
\* - roll management

Next ==
    \/ Tick
    \/ Bake
    \/ Endorse
    \/ IncrBlockSlot
    \/ ActiveToAdmin
    \/ CycleAdminToActive
    \/ SnapshotAdminToActive

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

(**************)
(* Properties *)
(**************)

BalanceRollCorrectness == \A c \in Cycles, bs \in Block_slots, d \in DELEGATES :
    /\ balance[c][bs][d] >= TOKENS_PER_ROLL * card(rolls_snapshot[c][bs][d])
    /\ balance[c][bs][d] <  TOKENS_PER_ROLL * (card(rolls_snapshot[c][bs][d]) + 1)

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

\* TODO
\* chain health - blocks have priority 0 and almost all (80%?) endorsement slots are filled
\*   properties of healthy chains Seq(roll)

==========================
