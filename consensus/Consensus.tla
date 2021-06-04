---- MODULE Consensus ----

EXTENDS FiniteSets, Integers, Naturals, Sequences, TLC

CONSTANTS
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
    ROLLS,                  \* set of roll ids
    DELEGATES,              \* set of delegate ids
    TOKENS_PER_ROLL,        \* 8000
    BLOCKS_PER_CYCLE,       \* 8192
    BAKING_PRIORITY,        \* cycle -> block_slot -> Seq(roll)
    ENDORSEMENT_RIGHTS,     \* cycle -> block_slot -> roll -> int
    INIT_BALANCE,           \* initial balances
    INIT_ROLLS_SNAPSHOT,    \* cycle -> block_slot -> delegate -> Set(roll)
    INIT_SAFETY_DEPOSIT,    \* initial safety deposit
    BAKING_REWARD,          \* cycle -> block_slot -> delegate -> int
    ENDORSEMENT_REWARD      \* cycle -> block_slot -> delegate -> int

VARIABLES
    time,               \* timestamp: 1 time ~ MIN_BLOCK_DELAY
    cycle,              \* int
    block_slot,         \* int
    phase,              \* phase
    all_blocks,         \* cycle -> block -> Set(<<roll, time>>)
    delegate_blocks,    \* cycle -> block_slot -> delegate -> bool * time
    balance,            \* cycle -> block_slot -> delegate -> int
    baking_reward,      \* cycle -> block_slot -> delegate -> int
    endorsement_reward, \* cycle -> block_slot -> delegate -> int
    rolls_snapshot,     \* cycle -> block_slot -> delegate -> Set(roll)
    rolls_working,      \* cycle -> block_slot -> delegate -> Set(roll)
    endorsements,       \* cycle -> block_slot -> roll -> int
    safety_deposit      \* cycle -> delegate -> int

\* inclusive variables



\* exclusive variables

vars_no_time == <<cycle, block_slot, phase, all_blocks, delegate_blocks, balance, baking_reward, endorsement_reward, rolls_snapshot, rolls_working, endorsements>>

vars == <<time, cycle, block_slot, phase, all_blocks, delegate_blocks, balance, baking_reward, endorsement_reward, rolls_snapshot, rolls_working, endorsements>>

----

All_time == 0..MAX_TIME

Cycles == 0..MAX_CYCLE

Balances == 0..MAX_BALANCE

max_slot == BLOCKS_PER_CYCLE - 1

Block_slots == 0..max_slot

Blocks == ROLLS \X All_time

Deposits == 0..MAX_DEPOSIT

Baking_phase == { <<"bake", t>> : t \in All_time }

Endorsing_phase == { <<"endorse", t>> : t \in All_time }

Close_phase == { <<"close", 0>> }

Phases == Baking_phase \cup Endorsing_phase \cup Close_phase

Rewards == 0..MAX_REWARD

baking_phase(t) == <<"bake", t>>

endorsing_phase(t) == <<"endorse", t>>

close_phase(t) == <<"close", t>>

card(set) == Cardinality(set)

ToSet(seq) == { seq[i] : i \in DOMAIN seq }

Pick(set) ==
    CASE set /= {} -> CHOOSE x \in set : TRUE
      [] OTHER -> PrintT("Cannot supply an element of the empty set")

max(a, b) == IF a >= b THEN a ELSE b

RECURSIVE sum(_, _)
sum(set, acc) == 
    IF set /= {} THEN
        LET x == Pick(set) IN sum(set \ {x}, acc + x)
    ELSE acc

Sum(set) == sum(set, 0)

rem(bal) == bal % TOKENS_PER_ROLL

\* @type: (Set(a), Seq(a)) => Seq(a);
RECURSIVE seq_of_set(_, _)
seq_of_set(s, acc) ==
    IF s = {} THEN acc
    ELSE
        LET x == Pick(s)
            t == s \ {x}
        IN seq_of_set(t, Append(acc, x))

\* @type: Set(a) => Seq(a);
SetToSeq(s) == seq_of_set(s, <<>>)

\* @type: (a => b, Seq(a), Seq(b)) => Seq(b);
RECURSIVE map(_, _, _)
map(f(_), seq, acc) ==
    IF seq = <<>> THEN acc
    ELSE
        LET x == Head(seq) IN
        map(f, Tail(seq), Append(acc, f(x)))

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

----

ASSUME MAX_TIME >= (MAX_CYCLE + 1) * card(Block_slots) * MIN_BLOCK_DELAY

ASSUME \A c \in Cycles, b \in Block_slots : Len(BAKING_PRIORITY[c][b]) <= MAX_BAKE

ASSUME \A c \in Cycles, b \in Block_slots : Sum({ ENDORSEMENT_RIGHTS[c][b][r] : r \in ROLLS }) <= MAX_ENDORSE

(*****************)
(* Initial state *)
(*****************)

Init ==
    /\ time               = 0
    /\ cycle              = 0
    /\ block_slot         = 0
    /\ phase              = baking_phase(0)
    /\ balance            = INIT_BALANCE
    /\ rolls_snapshot     = INIT_ROLLS_SNAPSHOT
    /\ rolls_working      = INIT_ROLLS_SNAPSHOT
    /\ all_blocks         = [ c \in Cycles |-> [ b \in Block_slots |-> {} ] ]
    /\ delegate_blocks    = [ c \in Cycles |-> [ b \in Block_slots |-> [ d \in DELEGATES |-> <<FALSE, 0>> ] ] ]
    /\ baking_reward      = [ c \in Cycles |-> [ b \in Block_slots |-> [ d \in DELEGATES |-> 0 ] ] ]
    /\ endorsement_reward = [ c \in Cycles |-> [ b \in Block_slots |-> [ d \in DELEGATES |-> 0 ] ] ]
    /\ endorsements       = [ c \in Cycles |-> [ b \in Blocks |-> 0 ] ]
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
    /\ delegate_blocks \in [ Cycles -> [ Block_slots -> [ DELEGATES -> BOOLEAN \X All_time ] ] ]
    /\ rolls_snapshot  \in [ Cycles -> [ Block_slots -> [ DELEGATES -> SUBSET ROLLS ] ] ]
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

emmy_plus_delay(p, e) ==
    MIN_BLOCK_DELAY + BAKING_DELAY * p + ENDORSEMENT_DELAY * max(0, INITIAL_ENDORSERS - e)

emmy_star_delay(p, e) ==
    IF p = 0 /\ 5 * e >= 3 * MAX_ENDORSE THEN MIN_BLOCK_DELAY
    ELSE emmy_plus_delay(p, e)

----

baking_priority(c, bs, r) == Index(r, BAKING_PRIORITY[c][bs]) - 1

has_baking_rights(c, bs, r) == r \in ToSet(BAKING_PRIORITY[c][bs])

endorsers(c, bs) == { r \in ROLLS : ENDORSEMENT_RIGHTS[c][bs][r] > 0 }

active_rolls(c, bs) ==
    UNION { rolls_working[c][bs][d] : d \in DELEGATES } \cup UNION { rolls_snapshot[c][bs][d] : d \in DELEGATES }

inactive_rolls(c, bs) == ROLLS \ active_rolls(c, bs)

RECURSIVE latest_block_time(_, _, _)
latest_block_time(c, bs, d) ==
    IF c = 0 /\ bs = 0 THEN 0
    ELSE
        LET prev_c  == IF bs > 0 THEN c ELSE c - 1
            prev_bs == IF bs > 0 THEN bs - 1 ELSE max_slot
            prev    == delegate_blocks[prev_c][prev_bs][d]
        IN
        IF prev[1] THEN prev[2]
        ELSE latest_block_time(prev_c, prev_bs, d)

\* rolls with baking rights
nonzero_baking_rights(c, bs) == ToSet(BAKING_PRIORITY[c][bs])

\* rolls with endorsement rights in the given cycle and block slot
nonzero_endorsement_rights(c, bs) == { r \in ROLLS : ENDORSEMENT_RIGHTS[c][bs][r] > 0 }

\* Get [d]'s current roll snapshot
current_snapshot_rolls(d) == rolls_snapshot[cycle][block_slot][d]

\* Get [d]'s current working rolls
current_working_rolls(d) == rolls_working[cycle][block_slot][d]

\* Get delegate id associated with roll [r]
lookup_roll_opt(r) ==
    LET s == { d \in DELEGATES : current_snapshot_rolls(d) = r } IN
    IF s /= {} THEN <<TRUE, Pick(s)>>
    ELSE <<FALSE, 0>>

\* TODO
\* reward calculation
\* baking_reward(d, br, es) == {}
\* endorsement_reward(r, er, es) == {}

true_blocks == UNION { all_blocks[c][bs] : c \in Cycles, bs \in Block_slots }

isSome(opt) == opt[1]

phase_change(succ) == phase' = <<succ, time>>

cmp_time(b1, b2) == b1[2] <= b2[2]

roll_list_of_blocks(blks) ==
    LET sorted == SortSeq(SetToSeq(blks), cmp_time) IN
    Map(Head, sorted)

prev_cycle_slot ==
    IF block_slot > 0 THEN <<cycle, block_slot - 1>>
    ELSE
        IF cycle > 0 THEN <<cycle - 1, BLOCKS_PER_CYCLE>>
        ELSE <<0, 0>>

\* roll -> time
\* TODO what endorsements are considered?
block_delay(r) ==
    LET prio == baking_priority(cycle, block_slot, r) IN
    IF prio < 0 THEN MAX_TIME
    ELSE
        MIN_BLOCK_DELAY + BAKING_DELAY * prio \* + ENDORSEMENT_DELAY * max(0, INITIAL_ENDORSERS - e)

has_baked_block(c, bs, r) == r \in { b[1] : b \in all_blocks[c][bs] }

(***********)
(* Actions *)
(***********)

incr_time ==
    /\ time < MAX_TIME
    /\ time' = time + 1

Tick ==
    /\ incr_time
    /\ UNCHANGED vars_no_time

\* Increment block number if sufficiently small
\* otherwise increment  cycle number if sufficiently small

Incr ==
    \* increments suff small slot
    CASE block_slot < BLOCKS_PER_CYCLE - 1 ->
            /\ block_slot' = block_slot + 1
            /\ UNCHANGED cycle
    \* increments suff small cycle
      [] cycle < MAX_CYCLE ->
            /\ block_slot' = 0
            /\ cycle' = cycle + 1
    \* disables Incr action
      [] OTHER ->
            /\ FALSE
            /\ UNCHANGED <<block_slot, cycle>>

bake_block(r) ==
    LET del == lookup_roll_opt(r)
        d   == del[2]
    IN
    /\ del[1]
    /\ time >= latest_block_time(cycle, block_slot, r) + block_delay(r)
    /\ all_blocks'      = [ all_blocks      EXCEPT ![cycle][block_slot] = @ \cup {<<r, time>>} ]
    /\ delegate_blocks' = [ delegate_blocks EXCEPT ![cycle][block_slot][d] = <<r, time>> ]
    /\ UNCHANGED <<>> \* TODO

\* 
Bake == \E r \in nonzero_baking_rights(cycle, block_slot) :
    /\ phase[1] = "bake"
    /\ incr_time
    \* increment slot/cycle
    /\ Incr
    \* bake the block
    /\ bake_block(r)

adjust(type, amt, d) ==
    LET bal == balance[cycle][block_slot][d] IN
    CASE type = "add" ->
        IF amt > TOKENS_PER_ROLL - rem(bal) THEN
            /\ balance' = [ balance EXCEPT ![cycle][block_slot][d] = @ + amt ]
            /\ UNCHANGED <<rolls_snapshot, rolls_working>>
        ELSE
            \* split rolls and reassign
            \E r \in inactive_rolls(cycle, block_slot) :
                /\ balance'       = [ balance       EXCEPT ![cycle][block_slot][d] = @ + amt ]
                /\ rolls_working' = [ rolls_working EXCEPT ![cycle][block_slot][d] = @ \cup {r} ]
      [] type = "sub" ->
        IF amt > rem(bal) THEN
            balance' = [ balance EXCEPT ![cycle][block_slot][d] = @ - amt ]
        ELSE
            \* split rolls and reassign
            \E r \in rolls_working[cycle][block_slot][d] :
                /\ balance'       = [ balance       EXCEPT ![cycle][block_slot][d] = @ - amt ]
                /\ rolls_working' = [ rolls_working EXCEPT ![cycle][block_slot][d] = @ \ {r} ]

\* calculate and distribute baking reward
BakingReward(c, bs, r) == \E d \in DELEGATES :
    LET dp  == lookup_roll_opt(r)
        del == dp[2]
        reward == BAKING_REWARD[c][bs][d]
    IN
    \E new_roll \in inactive_rolls(c, bs) :
        /\ phase[1] = "close"
        /\ dp[1]
        /\ del = d
        /\ balance' = [ balance EXCEPT ![c][bs][d] = @ + reward ]
        /\ rolls_working' = [ rolls_working EXCEPT ![c][bs][d] = @ \cup {new_roll} ]

Endorse == \E r \in nonzero_endorsement_rights(cycle, block_slot) :
    LET dopt == lookup_roll_opt(r)
        del  == dopt[2]
    IN
    /\ phase[1] = "endorse"
    /\ isSome(dopt)
    /\ phase_change("close")

\* calculate and distribute endorsement rewards
EndorsementReward(c, bs, r) == \E d \in DELEGATES :
    LET dp  == lookup_roll_opt(r)
        del == dp[2]
    IN
    /\ dp[1]
    /\ del = d
    /\ balance'       = [ balance       EXCEPT ![c][bs][d] = @ + BAKING_REWARD[c][bs][d] ]
    /\ rolls_working' = [ rolls_working EXCEPT ![c][bs][d] = @ \cup {} ]

\* Transitions
BakeToEndorse ==
    /\ phase[1] = "bake"
    /\ all_blocks[cycle][block_slot] /= {}
    /\ phase_change("endorse")
    /\ UNCHANGED <<>> \* TODO

EndorseToClose == \E r \in ROLLS :
    /\ phase[1] = "endorse"
    /\ has_baked_block(cycle, block_slot, r)
    /\ endorsements[cycle][block_slot][r] >= MIN_ENDORSE
    /\ phase_change("close")
    /\ UNCHANGED <<>> \* TODO

CloseToBake == \E r \in nonzero_baking_rights(cycle, block_slot) :
    /\ phase[1] = "endorse"
    /\ endorsements[cycle][block_slot][r] >= MIN_ENDORSE
    /\ phase_change("bake")
    /\ BakingReward(cycle, block_slot, r)
    /\ EndorsementReward(cycle, block_slot, r)
    /\ UNCHANGED <<>> \* TODO

\* TODO
\* - safety deposit management
\* - roll management

(**************)
(* Properties *)
(**************)

BalanceRollCorrectness == \A c \in Cycles, bs \in Block_slots, d \in DELEGATES :
    /\ balance[c][bs][d] >= TOKENS_PER_ROLL * card(rolls_working[c][bs][d])
    /\ balance[c][bs][d] <  TOKENS_PER_ROLL * (card(rolls_working[c][bs][d]) + 1)

DisjointRolls == \A c \in Cycles, bs \in Block_slots, d1, d2 \in DELEGATES :
    rolls_working[c][bs][d1] \cap rolls_working[c][bs][d2] = {}

BakersHaveNonzeroPriorityForBakedSlots == \A c \in Cycles, b \in Block_slots :
    LET rts == all_blocks[c][b] IN
    \/ rts = {}
    \/ rts /= {} => \A blk \in rts : \E r \in ToSet(BAKING_PRIORITY[c][b]) : r = rts[1]

EndorsersHaveNonzeroPriorityForEndorsedSlots == \A c \in Cycles, b \in Block_slots :
    LET blks == all_blocks[c][b] IN
    \/ blks = {}
    \/ blks /= {} =>
        LET r == Pick(blks)[1] IN ENDORSEMENT_RIGHTS[c][b][r] > 0

\* TODO more properties

==========================
