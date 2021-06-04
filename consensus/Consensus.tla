---- MODULE Consensus ----

EXTENDS FiniteSets, Integers, Naturals, Sequences, TLC

CONSTANTS
    MAX_BAKE,               \* maximum number of bakers per block slot
    MAX_CYCLE,              \* last cycle
    MAX_COMMIT,             \* maximum commitment number
    MAX_ENDORSE,            \* maximum number of endorsements per block
    MAX_TIME,               \* maximum time
    MAX_BALANCE,            \* maximum balance a delegate can have
    MAX_DEPOSIT,            \* maximum deposit
    MIN_ENDORSE,            \* minimum number of endorses to close a block
    MIN_BLOCK_DELAY,        \* minimum block delay
    BLOCK_DELAY,            \* tuple of delay parameters
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
    time,               \* timestamp, as granular as MIN_BLOCK_DELAY
    cycle,              \* int
    block_slot,         \* int
    phase,              \* phase
    all_blocks,         \* cycle -> block -> Set(<<roll, time>>)
    delegate_blocks,    \* cycle -> block_slot -> delegate -> bool * time
    balance,            \* cycle -> block_slot -> delegate -> int
    rewards,            \* cycle -> block_slot -> delegate -> int
    rolls_snapshot,     \* cycle -> block_slot -> delegate -> Set(roll)
    rolls_working,      \* cycle -> block_slot -> delegate -> Set(roll)
    endorsements,       \* cycle -> block_slot -> roll -> weight
    safety_deposit,     \* cycle -> delegate -> int
    commitment          \* cycle -> block_slot -> roll -> int

VARIABLE
    phase_log       \* log of the phases as they change

\* inclusive variables

phase_vars == <<phase, phase_log>>

\* exclusive variables

vars_no_time == <<cycle, block_slot, phase, all_blocks, delegate_blocks, balance, rewards, rolls_snapshot, rolls_working, endorsements, commitment, phase_log>>

vars == <<time, cycle, block_slot, phase, all_blocks, delegate_blocks, balance, rewards, rolls_snapshot, rolls_working, endorsements, commitment, phase_log>>

----

All_time == 0..MAX_TIME

Cycles == 0..MAX_CYCLE

Balances == 0..MAX_BALANCE

Block_slots == 0..(BLOCKS_PER_CYCLE - 1)

Blocks == ROLLS \X All_time

Commits == 0..MAX_COMMIT

Deposits == 0..MAX_DEPOSIT

Baking_phase == { <<"bake", t>> : t \in All_time }

Endorsing_phase == { <<"endorse", t>> : t \in All_time }

Close_phase == { <<"close", 0>> }

Phases == Baking_phase \cup Endorsing_phase \cup Close_phase

baking_phase(t) == <<"bake", t>>

endorsing_phase(t) == <<"endorse", t>>

close_phase(t) == <<"close", t>>

card(set) == Cardinality(set)

ToSet(seq) == { seq[i] : i \in DOMAIN seq }

Pick(set) ==
    CASE set /= {} -> CHOOSE x \in set : TRUE
      [] OTHER -> PrintT("Cannot supply an element of the empty set")

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
    /\ time            = 0
    /\ cycle           = 0
    /\ block_slot      = 0
    /\ phase           = baking_phase(0)
    /\ balance         = INIT_BALANCE
    /\ rolls_snapshot  = INIT_ROLLS_SNAPSHOT
    /\ rolls_working   = INIT_ROLLS_SNAPSHOT
    /\ all_blocks      = [ c \in Cycles |-> [ b \in Block_slots |-> {} ] ]
    /\ delegate_blocks = [ c \in Cycles |-> [ b \in Block_slots |-> [ d \in DELEGATES |-> <<FALSE, 0>> ] ] ]
    /\ rewards         = [ c \in Cycles |-> [ b \in Block_slots |-> [ d \in DELEGATES |-> 0 ] ] ]
    /\ endorsements    = [ c \in Cycles |-> [ b \in Blocks |-> 0 ] ]
    /\ safety_deposit  = [ c \in Cycles |-> [ b \in Block_slots |-> [ d \in DELEGATES |-> INIT_SAFETY_DEPOSIT] ] ]
    \* /\ commitment     = [ c \in Cycles |-> [ b \in Block_slots |-> [ r \in ROLLS |-> <<FALSE, 0>> ] ] ]

(******************)
(* Type invariant *)
(******************)

TypeOK ==
    /\ time            \in All_time
    /\ cycle           \in Cycles
    /\ block_slot      \in Block_slots
    /\ balance         \in Balances
    /\ phase           \in Phases
    /\ phase_log       \in Seq(Phases)
    /\ all_blocks      \in [ Cycles -> [ Block_slots -> SUBSET Blocks ] ]
    /\ delegate_blocks \in [ Cycles -> [ Block_slots -> [ DELEGATES -> BOOLEAN \X All_time ] ] ]
    /\ rolls_snapshot  \in [ Cycles -> [ Block_slots -> [ DELEGATES -> SUBSET ROLLS ] ] ]
    /\ endorsements    \in [ Cycles -> [ Blocks -> 0..MAX_ENDORSE ] ]
    /\ safety_deposit  \in [ Cycles -> [ Block_slots -> [ DELEGATES -> Deposits ] ] ]
    \* /\ commitment     \in [ Cycles -> [ Block_slots -> [ ROLLS -> BOOLEAN \X Commits ] ] ]

----

baking_priority(c, bs, r) == Index(r, BAKING_PRIORITY[c][bs])

has_baking_rights(c, bs, r) == r \in ToSet(BAKING_PRIORITY[c][bs])

endorsers(c, bs) == { r \in ROLLS : ENDORSEMENT_RIGHTS[c][bs][r] > 0 }

active_rolls(c, bs) ==
    UNION { rolls_working[c][bs][d] : d \in DELEGATES } \cup UNION { rolls_snapshot[c][bs][d] : d \in DELEGATES }

inactive_rolls(c, bs) == ROLLS \ active_rolls(c, bs)

\* rolls with baking rights
nonzero_baking_rights(c, bs) == ToSet(BAKING_PRIORITY[c][bs])

\* rolls with endorsement rights in the given cycle and block slot
nonzero_endorsement_rights(c, bs) == { r \in ROLLS : ENDORSEMENT_RIGHTS[c][bs][r] > 0 }

\* Get [d]'s current roll snapshot
current_snapshot_rolls(d) == rolls_snapshot[cycle][block_slot][d]

\* 
current_working_rolls(d) == rolls_working[cycle][block_slot][d]

\* 
lookup_roll_opt(r) ==
    LET s == { d \in DELEGATES : current_snapshot_rolls(d) = r } IN
    IF s /= {} THEN
        <<TRUE, CHOOSE x \in s : TRUE>>
    ELSE <<FALSE, 0>>

\* reward calculation
baking_reward(d, br, es) == {} \* TODO

endorsement_reward(r, er, es) == {} \* TODO

true_blocks(c, bs) == UNION { all_blocks[c][bs] : d \in DELEGATES }

baked_a_block(d, c, bs) == rolls_snapshot[c][bs][d] \cap ToSet(all_blocks[c][bs])

isSome(opt) == opt[0]

phase_change(succ) ==
    LET new_phase == <<succ, time + 1>> IN
    /\ phase' = new_phase
    /\ phase_log' = new_phase \o phase_log
    /\ UNCHANGED time

cmp_time(b1, b2) == b1[1] <= b2[1]

roll_list_of_blocks(blks) ==
    LET sorted == SortSeq(SetToSeq(blks), cmp_time) IN
    Map(Head, sorted)

prev_cycle_slot ==
    IF block_slot > 0 THEN <<cycle, block_slot - 1>>
    ELSE
        IF cycle > 0 THEN <<cycle - 1, BLOCKS_PER_CYCLE>>
        ELSE <<0, 0>> \* TODO

prev_block_time(r) ==
    IF cycle = 0 /\ block_slot = 0 THEN 0
    ELSE delegate_blocks

\* roll -> time
\* TODO how to get endorsements?
block_delay(r) ==
    IF r = Head(BAKING_PRIORITY[cycle][block_slot]) THEN MIN_BLOCK_DELAY + 0 \* endorsements
    ELSE
        LET prio == baking_priority(cycle, block_slot, r) IN
        MIN_BLOCK_DELAY + prio * BLOCK_DELAY[0] + 0 \* other factors

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
        d   == del[1]
    IN
    /\ del[0]
    /\ time >= prev_block_time(r) + block_delay(r)
    /\ all_blocks'      = [ all_blocks      EXCEPT ![cycle][block_slot] = @ \cup {<<r, time>>} ]
    /\ delegate_blocks' = [ delegate_blocks EXCEPT ![cycle][block_slot][d] = @ ]
    /\ phase_change("endorse")
    /\ UNCHANGED <<>> \* TODO

\* 
Bake == \E r \in nonzero_baking_rights(cycle, block_slot) :
    /\ phase[0] = "bake"
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
                /\ balance' = [ balance EXCEPT ![cycle][block_slot][d] = @ + amt ]
                /\ rolls_working' = [ rolls_working EXCEPT ![cycle][block_slot][d] = @ \cup {r} ]
      [] type = "sub" ->
        IF amt > rem(bal) THEN
            balance' = [ balance EXCEPT ![cycle][block_slot][d] = @ - amt ]
        ELSE
            \* split rolls and reassign
            \E r \in rolls_working[cycle][block_slot][d] :
                /\ balance' = [ balance EXCEPT ![cycle][block_slot][d] = @ - amt ]
                /\ rolls_working' = [ rolls_working EXCEPT ![cycle][block_slot][d] = @ \ {r} ]

\* calculate and distribute baking reward
BakingReward(c, bs, r) == \E d \in DELEGATES :
    LET dp  == lookup_roll_opt(r)
        del == dp[1]
        reward == BAKING_REWARD[c][bs][d]
    IN
    \E new_roll \in inactive_rolls(c, bs) :
        /\ phase[0] = "close"
        /\ dp[0]
        /\ del = d
        /\ balance' = [ balance EXCEPT ![c][bs][d] = @ + reward ]
        /\ rolls_working' = [ rolls_working EXCEPT ![c][bs][d] = @ \cup {new_roll} ]

Endorse == \E r \in nonzero_endorsement_rights(cycle, block_slot) :
    LET dopt == lookup_roll_opt(r)
        del  == dopt[1]
    IN
    /\ phase[0] = "endorse"
    /\ isSome(dopt)
    /\ phase_change("close")

\* calculate and distribute endorsement rewards
EndorsementReward(c, bs, r) == \E d \in DELEGATES :
    LET dp  == lookup_roll_opt(r)
        del == dp[1]
    IN
    /\ dp[0]
    /\ del = d
    /\ balance' = [ balance EXCEPT ![c][bs][d] = @ + BAKING_REWARD[c][bs][d] ]
    /\ rolls_working' = [ rolls_working EXCEPT ![c][bs][d] = @ \cup {} ]

CloseBlock == \E r \in nonzero_baking_rights(cycle, block_slot) :
    /\ phase[0] = "endorse"
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
    \/ rts /= {} => \A blk \in rts : \E r \in ToSet(BAKING_PRIORITY[c][b]) : r = rts[0]

EndorsersHaveNonzeroPriorityForEndorsedSlots == \A c \in Cycles, b \in Block_slots :
    LET blks == all_blocks[c][b] IN
    \/ blks = {}
    \/ blks /= {} =>
        LET r == Pick(blks)[0] IN ENDORSEMENT_RIGHTS[c][b][r] > 0

\* TODO more properties

==========================
