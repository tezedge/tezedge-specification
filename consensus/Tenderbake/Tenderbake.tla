---- MODULE Tenderbake ----

EXTENDS FiniteSets, Integers, Naturals, Sequences, Hash, TLC

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
    events                  \* process -> set of events to handle

\* 

vars_no_phase       == <<messages, blockchain, head_cert, level, round, locked_value, locked_round, endorsable_value, endorsable_round, preendorsement_qc, events>>
vars_no_phase_event == <<messages, blockchain, head_cert, level, round, locked_value, locked_round, endorsable_value, endorsable_round, preendorsement_qc>>
vars_handle_event   == <<level, round, locked_value, locked_round>>
vars_endorse        == <<messages, blockchain, head_cert, level, round, preendorsement_qc>>
vars_handle_msg     == <<blockchain, head_cert, endorsable_value, endorsable_round, preendorsement_qc>>

vars == <<messages, blockchain, head_cert, level, round, phase, locked_value, locked_round, endorsable_value, endorsable_round, preendorsement_qc, events>>

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

Values == BOOLEAN

Committees == { bs \in SUBSET Procs : card(bs) = n /\ card(bs) >= 3 * card(bs \cap FAULTY_PROCS) + 1 }

(***************)
(* Assumptions *)
(***************)

ASSUME \A l \in 1..10, r \in 1..10 : PROPOSER[l][r] \in COMMITTEE[l]

ASSUME \A l \in 1..10: COMMITTEE[l] \in Committees

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
        eQC      |-> {},
        pQC      |-> {}
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

Phases == { "P", "P_", "PE", "PE_", "E", "E_" } \* P = PROPOSE, PE = PREENDORSE, E = ENDORSE

(************)
(* Messages *)
(************)

\* payload = value to be agreed upon
PreendorseMsgs == [
    type    : {"Preendorse"},
    from    : Procs,
    level   : Levels,
    round   : Rounds,
    pred    : Hashes,
    payload : Values
]

PQCs == SUBSET PreendorseMsgs

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
    payload : PQCs
]

EQCs == SUBSET EndorseMsgs

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
    payload : EQCs \X Values \X Rounds \X PQCs
]

Messages == ProposeMsgs \cup PreendorseMsgs \cup PreendorsementsMsgs \cup EndorseMsgs

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

endorse_msg(from, l, r, h, pQC) == [
    type    |-> "Endorse",
    from    |-> from,
    level   |-> l,
    round   |-> r,
    pred    |-> h,
    payload |-> pQC ]

\* collections of messages
proposal_msgs(p) == { msg \in messages[p] : msg.type = "Propose" }
preendorse_msgs(p) == { msg \in messages[p] : msg.type = "Preendorse" }
preendorsements_msgs(p) == { msg \in messages[p] : msg.type = "Preendorsements" }
endorse_msgs(p) == { msg \in messages[p] : msg.type = "Endorse" }

preendorse_msgs_with(p, l, r, h, u) ==
    { msg \in preendorse_msgs(p) :
        /\ msg.level = l
        /\ msg.round = r
        /\ msg.pred = h
        /\ msg.payload = u }

endorse_msgs_with(p, l, r, h, u) ==
    { msg \in endorse_msgs(p) :
        /\ msg.level = l
        /\ msg.round = r
        /\ msg.pred = h
        /\ msg.payload = u }

\* transform preendorse messages to a QC
\* assumes
\*  - msgs /= {}
\*  - all messages in msgs have the same level, round, pred, and payload
QC_of_msgs(msgs) ==
    IF msgs = {} THEN <<0, 0, NULL, TRUE, {}>>
    ELSE
        LET mm == Pick(msgs)
            l  == mm.level
            r  == mm.round
            h  == mm.pred
            u  == mm.payload
            s  == { msg.from : msg \in msgs }
        IN
        <<l, r, h, u, s>>

\* header: level, round, pred_hash, proposer, eQC, pQC
\* contents: u

\* set of all block headers
Headers == [
    level    : Levels,
    round    : Rounds,
    proposer : Procs \cup {NULL},
    pred     : Hashes \cup {NULL},
    pQC      : PQCs,
    eQC      : EQCs
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
Blocks == [ header : Headers, contents : Values ]

\* block constructor
block(hdr, cont) == [ header |-> hdr, contents |-> cont ]

\* extracting info from QCs
roundQC(qc) == IF qc = {} THEN 0 ELSE Pick(qc).round
valueQC(qc) == IF qc = {} THEN TRUE ELSE Pick(qc).payload

proposed_value(p) ==
    LET pvs == { pm.payload[2] : pm \in proposal_msgs(p) } IN
    IF pvs = {} THEN NULL ELSE Pick(pvs)

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

\* events

EventKinds == { "NewChain", "NewMessage", "NewMessages" }

Event(kind, data) == [ kind |-> kind, data |-> data ]

ChainEvents == [ kind : {"NewChain"}, data : Seq(Blocks) \X EQCs ]

MessageEvents == [ kind : {"NewMessage"}, data : Messages ]

MessagesEvents == [ kind : {"NewMessages"}, data : SUBSET Messages ]

Events == ChainEvents \cup MessageEvents \cup MessagesEvents

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
    best

\* checks validity of a pQC or an eQC
isValidQC(l, r, h, u, _qc) ==
    \/ l = 1 /\ r = 1
    \/ LET qc == QC_of_msgs(_qc)
           _l == qc[1]
           _r == qc[2]
           _h == qc[3]
           _u == qc[4]
        IN
        /\ _l = l
        /\ _r = r
        /\ _h = h
        /\ _u = u

\* validity check for incoming messages
\* messages are validated before being stored in the message buffer
isValidMessage(p, msg) ==
    LET t == msg.type IN
    CASE t = "Propose" ->
        LET pb   == prev_block(p)
            ph   == pb.header
            pr   == ph.round
            _eQC == msg.payload[1] \* set of Endorse messages
            u    == msg.payload[2]
            eR   == msg.payload[3]
            _pQC == msg.payload[4] \* set of Preendorse messages
        IN
        \* correct proposer
        /\ msg.from = PROPOSER[level[p]][msg.round]
        \* valid eQC for previous block
        /\ \/ level[p] = 1
           \/ { e.from : e \in _eQC } \in QuorumsOf(COMMITTEE[prev_level(p)])
        /\ isValidQC(prev_level(p), pr, ph.pred, pb.contents, _eQC)
        /\ \* the value is newly generated
            \/ _pQC = {} /\ eR = 0
            \* checks for recycled value
            \/ LET __pQC == Pick(_pQC) IN
               /\ __pQC.payload = u
               /\ __pQC.round = eR
               /\ isValidQC(level[p], eR, hash(head(p)), u, _pQC)
      [] t \in {"Preendorse", "Endorse"} ->
        /\ msg.from \in COMMITTEE[level[p]]
        /\ msg.level = level[p]
        /\ msg.round \in { round[p], round[p] + 1 }
        /\ msg.pred = hash(head(p))
      [] t = "Preendorsements" ->
        LET _pQC == msg.payload
            u    == Pick(_pQC).payload
        IN
        /\ msg.from \in COMMITTEE[level[p]]
        /\ msg.level = level[p]
        /\ msg.round \in { round[p], round[p] + 1 }
        /\ msg.pred = hash(head(p))
        /\ isValidQC(level[p], msg.round, head(p).header.pred, u, _pQC)

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
        newly_gen(value) ==
            [ header :
              [ level    : {l},
                round    : {r},
                proposer : {p},
                pred     : {pred},
                eQC      : {prev_hd.pQC},
                pQC      : {{}}
              ],
              contents : {value}
            ]
    IN
    IF endorsable_value[p] = NULL THEN newly_gen(TRUE)
    ELSE
        LET eR == endorsable_round[p] IN
        [ header :
            [ level    : {l},
              round    : {eR},
              proposer : {PROPOSER[l][eR]},
              pred     : {pred},
              eQC      : {prev_hd.pQC},
              pQC      : {preendorsement_qc[p]}
            ],
          contents : {endorsable_value[p]}
        ]

\* broadcast [msg] to each recipient in [rcvrs]
RECURSIVE broadcast(_, _, _)
broadcast(evnts, rcvrs, ev) ==
    IF rcvrs = {} THEN evnts
    ELSE
        LET r == Pick(rcvrs) IN
        broadcast([ evnts EXCEPT ![r] = @ \cup {ev} ], rcvrs \ {r}, ev)

(***********)
(* Actions *)
(***********)

\* Good actions

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
pullChain(p, evts, Q) ==
    LET nces == { Event("NewChain", cc) : cc \in chain_and_certs(Q) } IN
    events' = [ events EXCEPT ![p] = evts \cup nces ]

\* extract certificate from proposal or certificate
get_certificate(propOrCert) ==
    IF propOrCert = {} THEN {}
    ELSE
        LET p == Pick(propOrCert)
            t == p.type
        IN
        IF t = "propose" THEN p.payload[1]
        ELSE propOrCert

\* if [p] has a quorum of preendorsements or is handling a Propose or Preendorsements,
\* then they update their endorsable_value, endorsable_round, and preendorsement_qc
\* otherwise, no changes are made
updateEndorsable(p, msg) ==
    LET pre ==
        IF msg.type = "Preendorse" THEN preendorse_msgs(p) \cup {msg}
        ELSE preendorse_msgs(p)
    IN
    IF card(pre) >= 2 * f + 1 THEN
        LET pl == Pick(pre).payload IN
        /\ endorsable_value'  = [ endorsable_value  EXCEPT ![p] = pl ]
        /\ endorsable_round'  = [ endorsable_round  EXCEPT ![p] = round[p] ]
        /\ preendorsement_qc' = [ preendorsement_qc EXCEPT ![p] = pre ]
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
filterMessages(p, l, r) ==
    messages' = [ messages EXCEPT ![p] = { mm \in @ : mm.level = l /\ mm.round = r } ]

\* drop events from previous levels
filterEvents(p, l) ==
    events' = [ events EXCEPT ![p] =
        { e \in @ :
            \/ e.kind = "NewChain"
            \/ /\ e.kind = "NewMessage"
               /\ e.data.level > l
            \/ /\ e.kind = "NewMessages"
               /\ e.data /= {}
               /\ Pick(e.data).level > l }
    ]

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

\* checks that [cert] justifies the inclusion of [b]
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
validChain(chain, _cert) ==
    LET cert == QC_of_msgs(_cert)
        l == cert[1]
        h == cert[3]
        u == cert[4]
        s == cert[5]
    IN
    \/ chain = <<genesis>>
    \/ /\ justify(Head(chain), cert)
       /\ BiMap(isValidValue, chain)

\* decisionOpt = NULL or <<block, certificate>>
advance(p, decisionOpt) ==
    /\ phase' = [ phase EXCEPT ![p] = "P" ]
    /\ IF decisionOpt = NULL THEN
            \* a value has not been decided for this level, go to next round
            /\ round' = [ round EXCEPT ![p] = @ + 1 ]
            /\ filterMessages(p, level[p], round'[p])
            /\ UNCHANGED <<level, blockchain, head_cert, preendorsement_qc>>
        ELSE
            LET blk  == decisionOpt[1]
                cert == decisionOpt[2]
            IN
            \* a value has been decided for this level, go to next level
            /\ round'    = [ round    EXCEPT ![p] = 1 ]
            /\ level'    = [ level    EXCEPT ![p] = @ + 1 ]
            /\ messages' = [ messages EXCEPT ![p] = {} ]
            /\ filterEvents(p, level[p])
            /\ updateState(p, blk \o blockchain[p], cert)
    /\ UNCHANGED <<locked_value, locked_round, endorsable_value, endorsable_round, preendorsement_qc, events>>

\* if [p] has decided (i.e. has seen an eQC in the ENDORSE phase), this returns the decided value at their level
\* otherwise, it returns NULL
get_decision(p) ==
    LET endorsements == endorse_msgs(p)
        proposal == block_of_propose_msg(Pick(proposal_msgs(p)))
    IN
    IF card(endorsements) < 2 * f + 1 THEN NULL
    ELSE <<proposal, QC_of_msgs(endorsements)>>

\* data = <<chain, propOrCert>>
HandleNewChain(p, data) ==
    LET chain == data[1]
        pOrC  == data[2]
        cert  == get_certificate(pOrC)
    IN
    /\ validChain(chain, cert)
    /\ IF Len(chain) > level[p] THEN updateState(p, chain, cert)
        ELSE
        /\ Len(chain) = level[p]
        /\ better_head(p, chain, cert)
        /\ updateState(p, chain, cert)
    /\ UNCHANGED <<messages, endorsable_value, endorsable_round>>

HandleConsensusMessage(p, ev) ==
    LET msg == ev.data
        t   == msg.type
        l   == msg.level
        r   == msg.round
        q   == msg.from
        h   == msg.pred
        hp  == hash(head(p))
        pl  == msg.payload
    IN
    IF /\ l = level[p]
       /\ h = hp
       /\ r \in {round[p], round[p] + 1}
    THEN
        /\ IF isValidMessage(p, msg) THEN
                /\ messages' = [ messages EXCEPT ![p] = @ \cup {msg} ]
                /\ updateEndorsable(p, msg)
                /\ UNCHANGED <<blockchain, head_cert>>
            ELSE UNCHANGED <<vars_handle_msg, messages>>
        /\ events' = [ events EXCEPT ![p] = @ \ {ev} ]
    ELSE
        IF \/ l = level[p] /\ h /= hp
           \/ l > level[p]
        THEN
            /\ pullChain(p, events[p] \ {ev}, Procs)
            /\ UNCHANGED <<vars_handle_msg, messages>>
        ELSE
            /\ events' = [ events EXCEPT ![p] = @ \ {ev} ]
            /\ UNCHANGED <<vars_handle_msg, messages>>

\* these messages have already been validated
\* now they're being passed as a quorum certificate
HandleConsensusMessages(p, msgs) ==
    /\ messages' = [ messages EXCEPT ![p] = @ \cup msgs ]
    /\ UNCHANGED vars_handle_msg

\* [p] handles one event
HandleEvent(p, ev) ==
    LET k == ev.kind IN
    /\ CASE k = "NewChain" ->
            /\ HandleNewChain(p, best_chain(p, ev.data))
            /\ events' = [ events EXCEPT ![p] = @ \ {ev} ]
            /\ UNCHANGED <<messages, endorsable_value, endorsable_round>>
         [] k = "NewMessage" -> HandleConsensusMessage(p, ev)
         [] k = "NewMessages" ->
            /\ HandleConsensusMessages(p, ev.data)
            /\ events' = [ events EXCEPT ![p] = @ \ {ev} ]
    /\ UNCHANGED vars_handle_event

\* PROPOSE - committee member
\* the proposer of a round proposes a value
Propose(p) ==
    LET l   == level[p]
        r   == round[p]
        h   == hash(head(p))
        eQC == head_cert[p]
        pQC == preendorsement_qc[p]
        u   == IF endorsable_value[p] /= NULL THEN endorsable_value[p] ELSE TRUE
        eR  == IF endorsable_value[p] /= NULL THEN round[p] ELSE 0
    IN
    \E v \in proposals(p, l, r) :
        /\ p = PROPOSER[l][r]
        /\ phase[p] = "P"
        /\ phase' = phase_change(phase, COMMITTEE[l], "P_")
        \* sends propose_msg to a quorum of committee memebers
        /\ events' = broadcast(events, Procs, Event("NewMessage", propose_msg(v, <<eQC, u, eR, pQC>>)))
        /\ UNCHANGED vars_no_phase_event

\* handle events when we have some
Propose_handle(p) == \E np \in {"P_", "PE"}, ev \in events[p] :
    /\ p \in COMMITTEE[level[p]]
    /\ phase[p] = "P_"
    /\ phase' = [ phase EXCEPT ![p] = np ]
    /\ HandleEvent(p, ev)

\* if no events, progress to next phase
Propose_(p) ==
    /\ p \in COMMITTEE[level[p]]
    /\ events[p] = {}
    /\ phase[p] \in {"P", "P_"}
    /\ phase' = [ phase EXCEPT ![p] = "PE" ]
    /\ UNCHANGED vars_no_phase

\* PREENDORSE - committee member
Preendorse(p) == \E msg \in proposal_msgs(p) :
    LET eR == msg.payload[3] IN
    /\ p \in COMMITTEE[level[p]]
    /\ phase[p] = "PE"
    /\ phase' = [ phase EXCEPT ![p] = "PE_" ]
    /\ IF \/ locked_value[p] = msg.payload[2]
          \/ /\ locked_round[p] < eR
             /\ eR < round[p]
          \/ /\ msg.level = 1
             /\ msg.round = 1
             /\ level[p] = 1
             /\ round[p] = 1
        THEN 
            events' = broadcast(events, Procs, Event("NewMessage", preendorse_msg(p, block_of_propose_msg(msg))))
        ELSE
            events' = broadcast(
                events,
                Procs,
                Event("NewMessage", preendorsements_msg(p, block_of_propose_msg(msg), preendorsement_qc[p]))
            )
    /\ UNCHANGED vars_no_phase_event

Preendorse_handle(p) == \E np \in {"PE_", "E"}, ev \in events[p] :
    /\ p \in COMMITTEE[level[p]]
    /\ phase[p] \in { "PE_", "PE_" }
    /\ phase' = [ phase EXCEPT ![p] = np ]
    /\ HandleEvent(p, ev)

Preendorse_(p) ==
    /\ p \in COMMITTEE[level[p]]
    /\ events[p] = {}
    /\ phase[p] \in {"PE", "PE_"}
    /\ phase' = [ phase EXCEPT ![p] = "E" ]
    /\ UNCHANGED vars_no_phase

\* ENDORSE - committee member
Endorse(p) == \E msg \in preendorse_msgs(p), np \in {"E", "E_"} :
    LET pre == preendorse_msgs(p) IN
    /\ p \in COMMITTEE[level[p]]
    /\ phase[p] = "E"
    /\ phase' = [ phase EXCEPT ![p] = np ]
    /\ IF card(pre) >= 2 * f + 1 THEN
            LET u    == proposed_value(p)
                l    == level[p]
                r    == round[p]
                h    == hash(head(p))
            IN
            /\ endorsable_value' = [ endorsable_value EXCEPT ![p] = u ]
            /\ locked_value'     = [ locked_value     EXCEPT ![p] = u ]
            /\ endorsable_round' = [ endorsable_round EXCEPT ![p] = r ]
            /\ locked_round'     = [ locked_round     EXCEPT ![p] = r ]
            /\ events' = broadcast(
                broadcast(events, Procs, Event("NewMessage", endorse_msg(p, l, r, h, pre))),
                Procs,
                Event("NewMessages", pre)
               )
        ELSE UNCHANGED <<endorsable_round, endorsable_value, locked_round, locked_value, events>>
    /\ UNCHANGED vars_endorse

Endorse_handle(p) == \E ev \in events[p] :
    /\ p \in COMMITTEE[level[p]]
    /\ phase[p] = "E_"
    /\ HandleEvent(p, ev)
    /\ UNCHANGED phase

Endorse_advance(p) ==
    /\ p \in COMMITTEE[level[p]]
    /\ phase[p] \in {"E", "E_"}
    /\ advance(p, get_decision(p))

\* PROPOSE - observer
ObserveP_handle(p) == \E ev \in events[p] :
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "P_"
    /\ HandleEvent(p, ev)
    /\ UNCHANGED phase

ObserveP_PE_handle(p) == \E ev \in events[p] :
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "P_"
    /\ HandleEvent(p, ev)
    /\ phase' = [ phase EXCEPT ![p] = "PE_" ]

ObserveP_PE(p) ==
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "P_"
    /\ phase' = [ phase EXCEPT ![p] = "PE_" ]
    /\ UNCHANGED vars_no_phase

\* PREENDORSE - observer
ObservePE_handle(p) == \E ev \in events[p] :
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "PE_"
    /\ HandleEvent(p, ev)
    /\ UNCHANGED phase

ObservePE_E_handle(p) == \E ev \in events[p] :
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "PE_"
    /\ HandleEvent(p, ev)
    /\ phase' = [ phase EXCEPT ![p] = "E_" ]

ObservePE_E(p) ==
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "PE_"
    /\ phase' = [ phase EXCEPT ![p] = "E_" ]
    /\ UNCHANGED vars_no_phase

\* ENDORSE - observer
ObserveE(p) == \E ev \in events[p] :
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "E"
    /\ HandleEvent(p, ev)
    /\ UNCHANGED phase

ObserveE_handle_advance(p) == \E ev \in events[p] :
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "E_"
    /\ HandleEvent(p, ev)
    /\ advance(p, get_decision(p))

ObserveE_advance(p) ==
    /\ p \notin COMMITTEE[level[p]]
    /\ phase[p] = "E_"
    /\ advance(p, get_decision(p))

OnTimeoutPullChain(p) == pullChain(p, events[p], Procs)

\* Faulty process actions
\* TODO

(*****************)
(* Specification *)
(*****************)

Init ==
    /\ messages          = [ p \in Procs |-> {} ]
    /\ blockchain        = [ p \in Procs |-> <<genesis>> ]
    /\ head_cert         = [ p \in Procs |-> {} ]
    /\ level             = [ p \in Procs |-> 1 ]
    /\ round             = [ p \in Procs |-> 1 ]
    /\ phase             = [ p \in Procs |-> IF p = PROPOSER[1][1] THEN "P" ELSE "P_" ]
    /\ locked_value      = [ p \in Procs |-> NULL ]
    /\ locked_round      = [ p \in Procs |-> 0 ]
    /\ endorsable_value  = [ p \in Procs |-> NULL ]
    /\ endorsable_round  = [ p \in Procs |-> 0 ]
    /\ preendorsement_qc = [ p \in Procs |-> {} ]
    /\ events            = [ p \in Procs |-> {} ]

Next ==
    \* correct process actions
    \/ \E p \in CORRECT_PROCS :
        \/ Propose(p)
        \/ Propose_handle(p)
        \/ Preendorse(p)
        \/ Preendorse_handle(p)
        \/ Endorse(p)
        \/ Endorse_handle(p)
        \/ Endorse_advance(p)
        \/ ObserveP_handle(p)
        \/ ObserveP_PE_handle(p)
        \/ ObserveP_PE(p)
        \/ ObservePE_handle(p)
        \/ ObservePE_E_handle(p)
        \/ ObservePE_E(p)
        \/ ObserveE(p)
        \/ ObserveE_handle_advance(p)
        \/ ObserveE_advance(p)
    \* faulty node actions
    \/ \E p \in FAULTY_PROCS :
        \/ FALSE

Fairness == SF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

(**************)
(* Properties *)
(**************)

TypeOK ==
    /\ messages          \in [ Procs -> SUBSET Messages ]
    /\ blockchain        \in [ Procs -> Seq(Blocks) ]
    /\ head_cert         \in [ Procs -> EQCs ]
    /\ level             \in [ Procs -> Levels ]
    /\ round             \in [ Procs -> Rounds ]
    /\ phase             \in [ Procs -> Phases ]
    /\ locked_value      \in [ Procs -> Values \cup {NULL} ]
    /\ locked_round      \in [ Procs -> Rounds ]
    /\ endorsable_value  \in [ Procs -> Values \cup {NULL} ]
    /\ endorsable_round  \in [ Procs -> Rounds ]
    /\ preendorsement_qc \in [ Procs -> PQCs ]
    /\ events            \in [ Procs -> SUBSET Events ]

\* TODO
\* - card(preendorsement_qc[p]) >= 2 * f + 1

Agreement == \A a, b \in CORRECT_PROCS :
    \/ isPrefix(blockchain[a], blockchain[b])
    \/ isPrefix(blockchain[b], blockchain[a])

Validity == \A p \in CORRECT_PROCS : validChain(blockchain[p], head_cert[p])

CorrectLevels == \A p \in CORRECT_PROCS : level[p] = Len(blockchain[p])

BoundedMessageBuffers == \A p \in CORRECT_PROCS : card(messages[p]) <= 4 * n + 2

Progress == \A p \in CORRECT_PROCS : []<><< Len(blockchain'[p]) > Len(blockchain[p]) >>_vars

Violated == \A p \in Procs : Len(blockchain[p]) < 2

===========================
