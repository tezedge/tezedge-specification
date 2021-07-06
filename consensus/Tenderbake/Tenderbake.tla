---- MODULE Tenderbake ----

EXTENDS FiniteSets, Integers, Naturals, Sequences, Hash

CONSTANTS
    NULL,                   \* absence of a value
    CORRECT_PROCS,          \* processes who follow the protocol
    FAULTY_PROCS,           \* byzantine processes who can behave arbitrarily
    PROPOSER,               \* level -> round -> baker designated to propose value in this (level, round)
    COMMITTEE,              \* level -> set of bakers in the consensus instance at the given level
    COMMITTEE_SIZE          \* the size of each committee

VARIABLES
    messages,               \* process -> set of messages
    blockchain,             \* process -> sequence of output values (blocks)
    head_cert,              \* process -> endorsement quorum certificate which justifies the process's current head
    level,                  \* process -> level of the consensus instance in which the process participates
    round,                  \* process -> round the process thinks it should be in for their current level
    phase,                  \* process -> phase the process thinks it should be in for their current round
    locked_value,           \* process -> NULL or value on which the process is locked in the current level
    locked_round,           \* process -> 0 or round on which the process is locked on a value in the current level
    endorsable_value,       \* process -> NULL or an endorsable value
    endorsable_round,       \* process -> 0 or endorsable round corresponding the process's endorsable_value
    preendorsement_qc,      \* process -> preendorsement quorum certificate corresponding to an endorsable value at the process's current level
    chains,                 \* process -> set of other process' chains & certificates (repsonses to pullChain)
    events,                 \* process -> set of events to handle
    proposed,               \* level -> set of all proposed blocks at the given level
    decided                 \* level -> NULL or block for which a committee member has seen an eQC at the given 

vars == <<messages, blockchain, head_cert, level, round, phase, locked_value, locked_round, endorsable_value, endorsable_round, preendorsement_qc, chains, events, proposed, decided>>

\* 

hash(val) == Hash(val)

card(set) == Cardinality(set)

Procs == CORRECT_PROCS \cup FAULTY_PROCS

m == card(Procs)

n == COMMITTEE_SIZE

f == card(FAULTY_PROCS)

Levels == Nat

Rounds == Nat

Hashes == Int

Committees == { bs \in SUBSET Procs : card(bs) = n /\ card(bs) >= 3 * card(bs \cap FAULTY_PROCS) + 1 }

(***************)
(* Assumptions *)
(***************)

ASSUME \A l \in Levels: COMMITTEE[l] \in Committees

\* 

Pick(set) == CHOOSE x \in set : TRUE

hd(seq) == Head(seq)

tl(seq) == Tail(seq)

\* genesis block
genesis == [
    header |-> [
        level    |-> 0,
        round    |-> 0,
        pred     |-> NULL,
        proposer |-> NULL,
        eQC      |-> NULL,
        pQC      |-> NULL
    ],
    contents |-> TRUE
]

BiMap(F(_, _), seq) ==
    LET RECURSIVE bimap(_, _, _)
        bimap(ff(_, _), s, acc) ==
            CASE acc = FALSE -> FALSE
              [] s = <<>> -> acc
              [] Len(s) = 1 -> s[1] = genesis
              [] OTHER -> bimap(ff, tl(s), acc /\ ff(s[1], s[2]))
    IN
    bimap(F, seq, TRUE)

QuorumsOf(comm) == { bs \in SUBSET comm : card(bs) >= 2 * card(bs \cap FAULTY_PROCS) + 1 }

Quorums == UNION { QuorumsOf(COMMITTEE[l]) : l \in Levels }

Phases == { "P", "PE", "E" } \* P = PROPOSE, PE = PREENDORSE, E = ENDORSE

\* header: level, round, pred_hash, proposer, eQC, pQC
\* contents: u

\* set of all block headers
Headers == [
    level    : Levels,
    round    : Rounds,
    proposer : Procs,
    pred     : Hashes,
    pQC      : Levels \X Rounds \X Hashes \X BOOLEAN \X Quorums,
    eQC      : Levels \X Rounds \X Hashes \X BOOLEAN \X Quorums
]

header(l, r, p, h, eQC, pQC) == [
    level    |-> l,
    round    |-> r,
    proposer |-> p,
    pred     |-> h,
    eQC      |-> eQC,
    pQC      |-> pQC
]

\* set of all blocks
Blocks == [ header : Headers, contents : BOOLEAN ]

\* block constructor
block(hdr, cont) == [ header |-> hdr, contents |-> cont ]

\* sets of quorum certificates
EQCs == Levels \X Rounds \X Hashes \X BOOLEAN \X Quorums
PQCs == Levels \X Rounds \X Hashes \X BOOLEAN \X Quorums

\* extracting info from QCs
roundQC(qc) == qc[2]
valueQC(qc) == qc[4]

(************)
(* Messages *)
(************)

\* Propose messages are just blocks in a different format
\* payload = (eQC, u, eR, pQC)
\*   eQC endorsement quorum certificate which justifies the block at the previous level
\*   proposed value u to be agreed on
\*   in case u is a previously proposed value, the corresponding endorsable round eR and pQC that justifies it
\*   if u is newly generated, then eR = 0 and pQC = {}

ProposeMsgs == [
    type    : {"Propose"},
    from    : Procs,
    level   : Levels,
    round   : Rounds,
    pred    : Hashes,
    payload : EQCs \X BOOLEAN \X Rounds \X PQCs
]

\* payload = value to be agreed upon
PreendorseMsgs == [
    type    : {"Preendorse"},
    from    : Procs,
    level   : Levels,
    round   : Rounds,
    pred    : Hashes,
    payload : BOOLEAN
]

\* payload = pQC justifying an endorsable value and round
PreendorsementsMsgs == [
    type    : {"Preendorsements"},
    from    : Procs,
    level   : Levels,
    round   : Rounds,
    pred    : Hashes,
    payload : PQCs
]

\* payload = endorsed value
EndorseMsgs == [
    type    : {"Endorse"},
    from    : Procs,
    level   : Levels,
    round   : Rounds,
    pred    : Hashes,
    payload : BOOLEAN
]

\* 
QCMsgs == [ type : {"QC"}, QC : PQCs ]

Messages == ProposeMsgs \cup PreendorseMsgs \cup PreendorsementsMsgs \cup EndorseMsgs \cup QCMsgs

\* message constructors

propose_msg(b, payload) == [
    type    |-> "Propose",
    from    |-> b.header.proposer,
    level   |-> b.header.level,
    round   |-> b.header.round,
    pred    |-> b.header.pred,
    payload |-> payload ]

preendorse_msg(from, b) == [
    type    |-> "Preendorse",
    from    |-> from,
    level   |-> b.header.level,
    round   |-> b.header.round,
    pred    |-> b.header.pred,
    payload |-> b.contents ]

preendorsements_msg(from, b, pQC) == [
    type    |-> "Preendorsements",
    from    |-> from,
    level   |-> b.header.level,
    round   |-> b.header.round,
    pred    |-> b.header.pred,
    payload |-> pQC ]

QC_msg(pQC) == [ type |-> "QC", QC |-> pQC ]

\* collections of messages
proposal_msgs(p) == { msg \in messages[p] : msg.type = "Propose" }
preendorse_msgs(p) == { msg \in messages[p] : msg.type = "Preendorse" }
preendorsements_msgs(p) == { msg \in messages[p] : msg.type = "Preendorsements" }
endorse_msgs(p) == { msg \in messages[p] : msg.type = "Endorse" }
QC_msgs(p) == { msg \in messages[p] : msg.type = "QC" }

proposed_value(p) ==
    LET pvs == { pm.payload[2] : pm \in proposal_msgs(p) } IN
    Pick(pvs)

\* get the pQC from a propose or prendorsements message
get_pQC(msg) ==
    LET t == msg.type IN
    CASE t = "Propose" -> msg.payload[4]
      [] t = "Preendorsements" -> msg.payload

\* converts propose message to block
block_of_propose_msg(msg) ==
    CASE msg.type = "Propose" ->
        LET pl == msg.payload IN
        block(header(msg.level, msg.round, msg.from, msg.pred, pl[1], pl[4]), pl[2])

\* set of preendorsements seen by [p]
preendorsements(p) ==
    LET pems  == preendorse_msgs(p)
        _pems == preendorsements_msgs(p)
    IN
    IF _pems /= {} THEN
        \* the set of peers who have preendorsed in the latest round
        Pick({ msg \in _pems : \A mm \in _pems : msg.round >= mm.round }).payload[5]
    ELSE
        \* the set of peers who have preendorsed in the latest round
        { mm.from : mm \in { msg \in pems : \A mm \in pems : msg.round >= mm.round } }

\* events

EventKinds == { "NewChain", "NewMessage" }

Event(kind, data) == [ kind |-> kind, data |-> data ]

\* 

RECURSIVE isPrefix(_, _)
isPrefix(s1, s2) ==
    \/ s1 = <<>>
    \/ /\ s2 /= <<>>
       /\ hd(s1) = hd(s2)
       /\ isPrefix(tl(s1), tl(s2))

\* head of [p]'s chain
head(p) ==
    LET bc == blockchain[p] IN
    IF bc = <<>> THEN genesis
    ELSE bc[1]

block_at_level(p, l) ==
    LET L == Len(blockchain[p]) IN
    blockchain[p][L - l + 1]

prev_level(p) == IF level[p] <= 1 THEN 0 ELSE level[p] - 1

prev_block(p) ==
    IF level[p] <= 1 THEN genesis
    ELSE block_at_level(p, level[p] - 1)

best_chain(p, cs) ==
    LET good == { c \in cs : isPrefix(blockchain[p], c) }
        best == { c \in good : \A cc \in good : Len(c) >= Len(cc) }
    IN
    Pick(best)

\* checks validity of a pQC or an eQC
isValidQC(l, r, h, u, qc) ==
    LET _l == qc[1]
        _r == qc[2]
        _h == qc[3]
        _u == qc[4]
        _s == qc[5]
    IN
    /\ _l = l
    /\ _r = r
    /\ _h = h
    /\ _u = u
    /\ _s \subseteq COMMITTEE[l]

\* validity check for incoming messages
\* messages are validated before being stored in the message buffer
isValidMessage(p, msg) ==
    LET t == msg.type IN
    IF t = "QC" THEN isValidQC(level[p], round[p], head(p), valueQC(msg.QC), msg.QC)
    ELSE
        CASE t = "Propose" ->
            LET pb   == prev_block(p)
                ph   == pb.header
                pr   == ph.round
                _eQC == msg.payload[1]
                u    == msg.payload[2]
                eR   == msg.payload[3]
                _pQC == msg.payload[4]
            IN
            \* correct proposer
            /\ msg.from = PROPOSER[level[p]][msg.round]
            \* valid eQC for previous block
            /\ isValidQC(prev_level(p), pr, ph.pred, pb.contents, _eQC)
            /\ \/ _pQC[5] = {} /\ eR = 0 \* the value is newly generated
                \* checks for recycled value
               \/ /\ _pQC[2] = eR
                  /\ _pQC[4] = u
                  /\ _pQC[3] = head(p).pred
            \* validity of eQC
            /\ _eQC[5] \in QuorumsOf(COMMITTEE[prev_level(p)])
            \* validity of pQC
            /\ isValidQC(level[p], msg.round, head(p).header.pred, u, _pQC)
          [] t = "Preendorse" \/ t = "Endorse" ->
            /\ msg.from \in COMMITTEE[level[p]]
            /\ msg.level = level[p]
            /\ msg.round \in { round[p], round[p] + 1 }
            /\ msg.pred = head(p).pred
          [] t = "Preendorsements" ->
            LET _pQC == msg.payload IN
            /\ msg.from \in COMMITTEE[level[p]]
            /\ msg.level = level[p]
            /\ msg.round \in { round[p], round[p] + 1 }
            /\ msg.pred = head(p).pred
            /\ isValidQC(level[p], msg.round, head(p).header.pred, _pQC[4], _pQC)

\* phase change for a set of bakers
RECURSIVE phase_change(_, _, _)
phase_change(ph, Q, to_phase) ==
    IF Q = {} THEN ph
    ELSE
        LET q == Pick(Q) IN
        phase_change([ ph EXCEPT ![q] = to_phase ], Q \ {q}, to_phase)

\* set of all reasonable proposals that [p] can make at level [l], round [r]
proposals(p, l, r) ==
    LET prev_hd == prev_block(p).header
        pred    == hash(prev_block(p))
        proposalsWithValue(value, msgs) == { msg \in messages[p] : msg.type = "Propose" /\ msg.payload[2] = value }
        newly_gen(value) ==
            [ header :
              [ level    : {l},
                round    : {r},
                proposer : {p},
                pred     : {pred},
                eQC      : {prev_hd.pQC},
                pQC      : {l} \X {r} \X {p} \X {pred} \X {value} \X {{}}
              ],
              contents : {value}
            ]
    IN
    IF endorsable_value[p] = NULL THEN UNION { newly_gen(val) : val \in BOOLEAN }
    ELSE {endorsable_value[p]}

\* broadcast [msg] to each recipient in [rcvrs]
RECURSIVE broadcast(_, _, _)
broadcast(msgs, rcvrs, msg) ==
    IF rcvrs = {} THEN msgs
    ELSE
        LET r == Pick(rcvrs) IN
        broadcast([ msgs EXCEPT ![r] = @ \cup {msg} ], rcvrs \ {r}, msg)

\* if the chain agrees with what [p] has seen thus far, [p] updates their blockchain and head_cert
updateState(p, chain, cert) ==
    IF isPrefix(Tail(blockchain[p]), chain) THEN
        /\ blockchain' = [ blockchain EXCEPT ![p] = chain ]
        /\ head_cert'  = [ head_cert  EXCEPT ![p] = cert ]
    ELSE UNCHANGED <<blockchain, head_cert>>

\* aggregates chains and certificates from a set of bakers [Q]
chain_and_certs(Q) ==
    LET RECURSIVE _chains(_, _)
        _chains(QQ, acc) ==
            IF QQ = {} THEN acc
            ELSE
                LET q == Pick(QQ) IN
                _chains(QQ \ {q}, acc \cup {<<blockchain[q], head_cert[q]>>})
    IN
    _chains(Q, {})

\* pullChain primitive - invoked on timeouts and when [p] is "behind"
pullChain(p, Q) ==
    LET nces == { Event("NewChain", cc) : cc \in chain_and_certs(Q) } IN
    events' = [ events EXCEPT ![p] = @ \cup nces ]

\* extract certificate from proposal or certificate
get_certificate(propOrCert) ==
    IF propOrCert.type = "QC" THEN propOrCert.QC
    ELSE propOrCert.payload[1]

\* TODO other vars
\* Preendorsements messages too?
updateEndorsable(p, msg) ==
    IF card(preendorse_msgs(p)) >= 2 * f + 1 THEN
        LET pl == Pick(preendorse_msgs(p)).payload
            pf == { mm.from : mm \in preendorse_msgs(p) }
        IN
        /\ endorsable_value'  = [ endorsable_value  EXCEPT ![p] = pl ]
        /\ endorsable_round'  = [ endorsable_round  EXCEPT ![p] = round[p] ]
        /\ preendorsement_qc' = [ preendorsement_qc EXCEPT ![p] = <<level[p], round[p], hash(head(p)), pl, pf>> ]
    ELSE
        IF msg.type \in { "Propose", "Preendorsements" } THEN
            LET pQC == get_pQC(msg) IN
            IF roundQC(pQC) > endorsable_round[p] THEN
                /\ endorsable_value'  = [ endorsable_value  EXCEPT ![p] = valueQC(pQC) ]
                /\ endorsable_round'  = [ endorsable_round  EXCEPT ![p] = roundQC(pQC) ]
                /\ preendorsement_qc' = [ preendorsement_qc EXCEPT ![p] = pQC ]
            ELSE UNCHANGED <<endorsable_value, endorsable_round, preendorsement_qc>>
        ELSE UNCHANGED <<endorsable_value, endorsable_round, preendorsement_qc>>

\* delete messages that don't correspond to round [r]
filterMessages(p, r) ==
    messages' = [ messages EXCEPT ![p] = { mm \in @ : mm.round = r } ]

\* which head is better, [p]'s or the head of cahin?
better_head(p, chain, propOrCert) ==
    LET h  == Head(chain)
        l  == h.header.level
        r  == h.header.round
        t  == propOrCert.type
        pr == prev_block(p).header.round
    IN
    \* proposal
    CASE t = "Propose" ->
        LET eR == propOrCert.payload[3] IN
        \/ endorsable_round[p] < eR
        \/ /\ endorsable_round[p] = eR
           /\ r < pr
    \* certificate
      [] OTHER ->
        /\ endorsable_round[p] = 0
        /\ r < pr

justify(b, cert) ==
    LET l == b.header.level
        r == b.header.round
        h == b.header.pred
        u == b.contents
    IN
    /\ isValidQC(l, r, h, u, cert)
    /\ card(cert[5]) >= 2 * f + 1

\* given [prev_b] is a valid block, we check whether [b] is valid
isValidValue(b, prev_b) ==
    LET bh == b.header
        l  == bh.level
    IN
    \* consistency
    /\ bh.pred = hash(prev_b)
    \* legitimacy
    /\ bh.pQC \subseteq COMMITTEE[l]
    /\ bh.proposer = PROPOSER[l][bh.round]

\* check cert justifies head of chain
validChain(chain, cert) ==
    LET l == cert[1]
        h == cert[3]
        u == cert[4]
        s == cert[5]
    IN
    /\ justify(Head(chain), cert)
    /\ BiMap(isValidValue, chain)

\* decisionOpt = NULL or <<block, certificate>>
advance(p, decisionOpt) ==
    /\ IF decisionOpt = NULL THEN
            \* a value has not been decided for this level, go to next round
            /\ round' = [ round EXCEPT ![p] = @ + 1 ]
            /\ UNCHANGED <<level, blockchain, preendorsement_qc>>
        ELSE
            \* a value has been decided for this level, go to next level
            /\ round' = [ round EXCEPT ![p] = 1 ]
            /\ level' = [ level EXCEPT ![p] = @ + 1 ]
            /\ blockchain' = [ blockchain EXCEPT ![p] = decisionOpt[1] \o @ ]
            /\ preendorsement_qc' = [ preendorsement_qc EXCEPT ![p] = decisionOpt[2] ]
    /\ filterMessages(p, round'[p])

\* if [p] has decided (i.e. has seen an eQC in the ENDORSE phase), this returns the decided value at their level
\* otherwise, it returns NULL
get_decision(p) == decided[level[p]]

\* TODO
\* data = <<chain, propOrCert>>
HandleNewChain(p, data) ==
    LET chain == data[1]
        pOrC  == data[2]
        cert  == get_certificate(pOrC)
    IN
    /\ validChain(chain, cert)
    /\ IF Len(chain) > level[p] THEN <<chain, cert>>
        ELSE
        /\ Len(chain) = level[p]
        /\ better_head(p, chain, cert)
        /\ updateState(p, chain, cert)

HandleConsensusMessage(p, msg) ==
    LET t  == msg.type
        l  == msg.level
        r  == msg.round
        q  == msg.from
        h  == msg.pred
        hp == hash(head(p))
        pl == msg.payload
    IN
    IF /\ l = level[p]
       /\ h = hp
       /\ r \in {round[p], round[p] + 1}
    THEN
        IF isValidMessage(p, msg) THEN
            /\ messages' = [ messages EXCEPT ![p] = @ \cup {msg} ]
            /\ updateEndorsable(p, msg)
            /\ UNCHANGED chains
        ELSE UNCHANGED <<messages, endorsable_value, endorsable_round, chains>>
    ELSE
        IF \/ l = level[p] /\ h /= hp
           \/ l > level[p]
        THEN \E Q \in QuorumsOf(COMMITTEE[level[p]]) :
            /\ pullChain(p, Q)
            /\ UNCHANGED <<messages, endorsable_value, endorsable_round>>
        ELSE UNCHANGED <<messages, endorsable_value, endorsable_round, chains>>

\* TODO
HandleEvent(p, ev) ==
    LET t == ev.type IN
    /\ CASE t = "NewChain" -> HandleNewChain(p, best_chain(p, ev.data))
         [] t = "NewMessage" -> HandleConsensusMessage(p, ev.data)
    /\ events' = [ events EXCEPT ![p] = @ \ {ev} ]

\* Actions

\* the proposer of a round proposes a value
Propose(p) == \E val \in BOOLEAN :
    LET l   == level[p]
        r   == round[p]
        h   == hash(head(p))
        eQC == head_cert[p]
        pQC == preendorsement_qc[p]
        u   == IF endorsable_value[p] /= NULL THEN endorsable_value[p] ELSE val
        eR  == IF endorsable_value[p] /= NULL THEN round[p] ELSE 0
    IN
    \E v \in proposals(p, l, r) :
        \E Q \in QuorumsOf(COMMITTEE[l]) :
            /\ p = PROPOSER[l][r]
            /\ phase[p] = "P"
            /\ \A q \in Q: phase[q] = "P"
            /\ phase' = phase_change(phase, Q, "PE")
            \* sends propose_msg to a quorum of committee memebers
            /\ messages' = broadcast(messages, Q, propose_msg(v, <<eQC, u, eR, pQC>>))

Preendorse(p) == \E np \in {"PE", "E"}, msg \in proposal_msgs(p), Q \in QuorumsOf(COMMITTEE[level[p]]) :
    /\ p \in COMMITTEE[level[p]]
    /\ phase[p] = "PE"
    /\ phase' = [ phase EXCEPT ![p] = np ]
    /\ messages' = broadcast(messages, Q, preendorse_msg(p, block_of_propose_msg(msg)))

Endorse(p) == \E msg \in preendorse_msgs(p), Q \in QuorumsOf(COMMITTEE[level[p]]) :
    /\ p \in COMMITTEE[level[p]]
    /\ phase[p] = "E"
    \* TODO

Endorse_advance(p) == \E msg \in preendorse_msgs(p), Q \in QuorumsOf(COMMITTEE[level[p]]) :
    /\ p \in COMMITTEE[level[p]]
    /\ phase[p] = "E"
    \* TODO
    /\ advance(p, get_decision(p))

ObserveP(p) == \E ev \in events[p] :
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "P"
    /\ HandleEvent(p, ev)
    /\ UNCHANGED phase

ObserveP_PE(p) == \E ev \in events[p] :
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "P"
    /\ HandleEvent(p, ev)
    /\ phase' = [ phase EXCEPT ![p] = "PE" ]

ObservePE(p) == \E ev \in events[p] :
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "PE"
    /\ HandleEvent(p, ev)
    /\ UNCHANGED phase

ObservePE_E(p) == \E ev \in events[p] :
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "PE"
    /\ HandleEvent(p, ev)
    /\ phase' = [ phase EXCEPT ![p] = "E" ]

ObserveE(p) == \E ev \in events[p] :
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "E"
    /\ HandleEvent(p, ev)
    /\ UNCHANGED phase

ObserveE_advance(p) == \E ev \in events[p] :
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "E"
    /\ HandleEvent(p, ev)
    /\ advance(p, get_decision(p))

\* TODO what happens to level, round, phase?
OnTimeoutPullChain(p) == \E Q \in Quorums:
    /\ round' = [ round EXCEPT ![p] = @ + 1 ]
    /\ phase' = [ phase EXCEPT ![p] = "P" ]
    /\ pullChain(p, Q)

(*****************)
(* Specification *)
(*****************)

Init ==
    /\ blockchain = [ b \in Procs |-> <<>> ]
    /\ head_cert  = [ b \in Procs |-> Procs ]
    /\ level      = [ b \in Procs |-> 1 ]
    /\ round      = [ b \in Procs |-> 1 ]
    \* TODO

Next == {}

Fairness == {}

Spec == Init /\ [][Next]_vars /\ Fairness

(**************)
(* Properties *)
(**************)

Agreement == \A a, b \in CORRECT_PROCS :
    \/ isPrefix(blockchain[a], blockchain[b])
    \/ isPrefix(blockchain[b], blockchain[a])

Validity == \A p \in CORRECT_PROCS : validChain(blockchain[p], head_cert[p])

CorrectLevels == \A p \in CORRECT_PROCS : level[p] = Len(blockchain[p])

BoundedMessageBuffers == \A p \in CORRECT_PROCS : card(messages[p]) <= 4 * COMMITTEE_SIZE + 2

Progress == \A p \in CORRECT_PROCS : <><< Len(blockchain'[p]) > Len(blockchain[p]) >>_vars

===========================
