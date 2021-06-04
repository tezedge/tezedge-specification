---- MODULE Consensus ----

EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS
    MAX_BAKE,            \* maximum number of bakers per block slot
    MAX_CYCLE,           \* last cycle
    MAX_COMMIT,          \* maximum commitment number
    MAX_ENDORSE,         \* maximum number of endorsements per block
    MAX_TIME,            \* maximum time
    MAX_BALANCE,         \* maximum balance a delegate can have
    MAX_DEPOSIT,         \* maximum deposit
    MIN_BLOCK_DELAY,     \* minimum block delay
    ROLLS,               \* set of roll ids
    DELEGATES,           \* set of delegate ids
    TOKENS_PER_ROLL,     \* 8000
    BLOCKS_PER_CYCLE,    \* 8192
    BAKING_RIGHTS,       \* cycle -> block -> roll -> int
    ENDORSEMENT_RIGHTS,  \* cycle -> block -> roll -> int
    INIT_BALANCE,        \* initial balances
    INIT_ROLLS_SNAPSHOT, \* cycle -> block -> roll -> Set(roll)
    INIT_SAFETY_DEPOSIT  \* initial safety deposit

VARIABLES
    time,           \* timestamp, as granular as MIN_BLOCK_DELAY
    cycle,          \* int
    block_slot,     \* int
    phase,          \* phase
    block_list,     \* cycle -> block -> Seq(<<bool, <<roll, time>>>>)
    balance,        \* cycle -> block -> delegate -> int
    rewards,        \* cycle -> block -> delegate -> int
    rolls_snapshot, \* cycle -> block -> delegate -> Set(roll)
    endorsements,   \* cycle -> block -> roll -> Set(roll)
    safety_deposit, \* cycle -> delegate -> int
    commitment      \* cycle -> block -> roll -> int

VARIABLE
    phase_log       \* log of the phases as they change

----

All_time == 0..MAX_TIME

Cycles == 0..MAX_CYCLE

Balances == 0..MAX_BALANCE

Block_slots == 0..(BLOCKS_PER_CYCLE - 1)

Commits == 0..MAX_COMMIT

Deposits == 0..MAX_DEPOSIT

Baking_phase == { <<"bake", t>> : t \in All_time }

Endorsing_phase == { <<"endorse", t>> : t \in All_time }

Close_phase == { <<"close", 0>> }

Phases == Baking_phase \cup Endorsing_phase \cup Close_phase

baking_phase(t) == <<"bake", t>>

endorsing_phase(t) == <<"endorse", t>>

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

----

ASSUME MAX_TIME >= (MAX_CYCLE + 1) * card(Block_slots) * MIN_BLOCK_DELAY

ASSUME \A c \in Cycles, b \in Block_slots : Sum({ BAKING_RIGHTS[c][b][r] : r \in ROLLS }) <= MAX_BAKE

ASSUME \A c \in Cycles, b \in Block_slots : Sum({ ENDORSEMENT_RIGHTS[c][b][r] : r \in ROLLS }) <= MAX_ENDORSE

(*****************)
(* Initial state *)
(*****************)

Init ==
    /\ time           = 0
    /\ cycle          = 0
    /\ block_slot     = 0
    /\ phase          = baking_phase(0)
    /\ balance        = INIT_BALANCE
    /\ rolls_snapshot = INIT_ROLLS_SNAPSHOT
    /\ block_list     = [ c \in Cycles |-> [ b \in Block_slots |-> <<FALSE, 0>> ] ]
    /\ rewards        = [ c \in Cycles |-> [ b \in Block_slots |-> [ d \in DELEGATES |-> 0 ] ] ]
    /\ endorsements   = [ c \in Cycles |-> [ b \in Block_slots |-> {} ] ]
    /\ safety_deposit = [ c \in Cycles |-> [ b \in Block_slots |-> [ d \in DELEGATES |-> INIT_SAFETY_DEPOSIT] ] ]
    /\ commitment     = [ c \in Cycles |-> [ b \in Block_slots |-> [ r \in ROLLS |-> <<FALSE, 0>> ] ] ]

(******************)
(* Type invariant *)
(******************)

TypeOK ==
    /\ time           \in All_time
    /\ cycle          \in Cycles
    /\ block_slot     \in Block_slots
    /\ balance        \in Balances
    /\ phase          \in Phases
    /\ phase_log      \in Seq(Phases)
    /\ block_list     \in [ Cycles -> [ Block_slots -> Seq(BOOLEAN \X (ROLLS \X All_time)) ] ]
    /\ rolls_snapshot \in [ Cycles -> [ Block_slots -> [ DELEGATES -> SUBSET ROLLS ] ] ]
    /\ endorsements   \in [ Cycles -> [ Block_slots -> SUBSET ROLLS ] ]
    /\ safety_deposit \in [ Cycles -> [ Block_slots -> [ DELEGATES -> Deposits ] ] ]
    /\ commitment     \in [ Cycles -> [ Block_slots -> [ ROLLS -> BOOLEAN \X Commits ] ] ]

----

\* rolls with baking rights
nonzero_baking_rights(c, bs) == { r \in ROLLS : BAKING_RIGHTS[c][bs][r] > 0 }

\* rolls with endorsement rights in the given cycle and block slot
nonzero_endorsement_rights(c, bs) == { r \in ROLLS : ENDORSEMENT_RIGHTS[c][bs][r] > 0 }

\* Get [d]'s current roll snapshot
rolls(d) == rolls_snapshot[cycle][block_slot][d]

\* 
lookup_roll_opt(r) ==
    LET s == { d \in DELEGATES : rolls(d) = r } IN
    IF s /= {} THEN
        <<TRUE, CHOOSE x \in s : TRUE>>
    ELSE <<FALSE, 0>>

\* reward calculation
baking_reward(d, br, es) == {} \* TODO

endorsement_reward(r, er, es) == {} \* TODO

isSome(opt) == opt[0]

phase_change(succ) ==
    LET new_phase == <<succ, time + 1>> IN
    /\ phase' = new_phase
    /\ phase_log' = new_phase \o phase_log
    /\ UNCHANGED time

(***********)
(* Actions *)
(***********)

\* Increment block number if sufficiently small
\* otherwise increment  cycle number if sufficiently small

Incr ==
    \* increments suff small block
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
    /\ Incr
    /\ block_list' = [ block_list EXCEPT ![cycle][block_slot] = <<TRUE, <<r, time>>>> \o @ ]
    /\ phase_change("endorse")

\* 
Bake == \E r \in nonzero_baking_rights(cycle, block_slot) :
    LET dopt == lookup_roll_opt(r)
        del  == dopt[1]
    IN
    /\ phase[0] = "bake"
    /\ isSome(dopt)
    /\ {}

\* 
BakingReward == {}

Endorse == \E r \in nonzero_endorsement_rights(cycle, block_slot) :
    LET dopt == lookup_roll_opt(r)
        del  == dopt[1]
    IN
    /\ phase[0] = "endorse"
    /\ isSome(dopt)
    /\ phase_change("close")

EndorsementRewards == {}

adjust(type, amt, d) ==
    CASE type = "add" ->
        LET bal == balance[cycle][block_slot][d] IN
        IF amt > TOKENS_PER_ROLL - (bal % TOKENS_PER_ROLL) THEN
            balance' = [ balance EXCEPT ![cycle][block_slot][d] = @ + amt ]
        ELSE {}

RECURSIVE manage_roll(_)
manage_roll(delta) ==
    IF delta /= <<>> THEN
        LET hd == delta[0] IN {}
    ELSE {}


CloseBlock ==
    /\ {}
    /\ phase_change("bake")

\* TODO
\* - safety deposit management
\* - roll management

(**************)
(* Properties *)
(**************)

BalanceRollCorrectness == \A c \in Cycles, s \in Block_slots, d \in DELEGATES :
    /\ balance[c][s][d] >= TOKENS_PER_ROLL * card(rolls(d))
    /\ balance[c][s][d] <  TOKENS_PER_ROLL * (card(rolls(d)) + 1)

DisjointRolls == \A d1, d2 \in DELEGATES : rolls_snapshot[d1] \cap rolls_snapshot[d2] = {}

BakersHaveNonzeroPriorityForBakedSlots == \A c \in Cycles, b \in Block_slots :
    LET rt == { brt[1] : brt \in { b_rt \in ToSet(block_list[c][b]) : b_rt[0] } } IN
    \/ rt = {}
    \/ LET r == Pick(rt)[0] IN rt /= {} => BAKING_RIGHTS[c][b][r] > 0

EndorsersHaveNonzeroPriorityForEndorsedSlots == \A c \in Cycles, b \in Block_slots :
    LET rt == block_list[c][b]
        r  == rt[1][0]
    IN
    rt[0] => ENDORSEMENT_RIGHTS[c][b][r] > 0

==========================
