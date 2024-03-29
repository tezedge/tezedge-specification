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

\* variable collections

\* inclusion vars
comm_vars       == <<messages, events>>
state_vars      == <<level, round, phase>>
chain_vars      == <<blockchain, head_cert>>
endorsable_vars == <<endorsable_round, endorsable_value, preendorsement_qc>>
locked_vars     == <<locked_round, locked_value>>

\* exclusion vars
vars_no_phase       == <<comm_vars, chain_vars, level, round, locked_vars, endorsable_vars>>
vars_no_phase_event == <<messages, chain_vars, level, round, locked_vars, endorsable_vars>>
vars_handle_msg     == <<chain_vars, locked_vars, endorsable_vars>>

vars == <<comm_vars, state_vars, chain_vars, endorsable_vars, locked_vars>>

\* Definitions

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

\* TODO improve assumptions

ASSUME \A l \in 1..10, r \in 1..10 : PROPOSER[l][r] \in COMMITTEE[l]

ASSUME \A l \in 1..10: COMMITTEE[l] \in Committees

\* helpers

Pick(set) == CHOOSE x \in set : TRUE

hd(seq) == Head(seq)

tl(seq) == Tail(seq)

cons(h, seq) == <<h>> \o seq

\* genesis block
genesis == [
    header |-> [
        level    |-> 0,
        round    |-> 0,
        pred     |-> NULL,
        proposer |-> NULL,
        eQC      |-> {}
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

\* {P, P_} = PROPOSE
\* {PE, PE_} = PREENDORSE
\* {E, E_} = ENDORSE
Phases == { "P", "P_", "PE", "PE_", "E", "E_" }

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

\* 
preendorse_msgs_for_pQC(p) ==
    LET ps == preendorse_msgs(p)
        hs == { msg.pred    : msg \in ps }
        us == { msg.payload : msg \in ps }
        \* preendorsement messages with given predecessor and value
        pe_msgs_with(h, u) ==
            { msg \in ps :
                /\ msg.level = level[p]
                /\ msg.round = round[p]
                /\ msg.pred = h
                /\ msg.payload = u }
        pe_collections == { pe_msgs_with(h, u) : h \in hs, u \in us }
    IN
    IF ps = {} THEN {} ELSE
    Pick({ s \in pe_collections : \A ss \in pe_collections : card(s) >= card(ss) })

endorse_msgs_with(p, l, r, h, u) ==
    { msg \in endorse_msgs(p) :
        /\ msg.level = l
        /\ msg.round = r
        /\ msg.pred = h
        /\ msg.payload = u }

\* transform preendorse messages to a pQC
\* all messages in [msgs] have the same level, round, pred, and payload
pQC_of_msgs(pmsgs) ==
    IF pmsgs = {} THEN <<0, 0, NULL, TRUE, {}>>
    ELSE
        LET mm == Pick(pmsgs)
            l  == mm.level
            r  == mm.round
            h  == mm.pred
            u  == mm.payload
            s  == { msg.from : msg \in pmsgs }
        IN
        <<l, r, h, u, s>>

\* transform endorse messages to an eQC
\* all messages in [msgs] have the same level, round, pred, and payload
eQC_of_msgs(emsgs) ==
    IF emsgs = {} THEN <<0, 0, NULL, TRUE, {}>>
    ELSE
        LET mm == Pick(emsgs)
            l  == mm.level
            r  == mm.round
            h  == mm.pred
            u  == Pick(mm.payload).payload
            s  == { msg.from : msg \in emsgs }
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
    eQC      : EQCs
]

\* header constructor
header(l, r, p, h, eQC) == [
    level    |-> l,
    round    |-> r,
    proposer |-> p,
    pred     |-> h,
    eQC      |-> eQC
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
      [] t = "Endorse" -> msg.payload

\* converts propose message to block
block_of_propose_msg(msg) ==
    CASE msg.type = "Propose" ->
        LET pl == msg.payload IN
        block(header(msg.level, msg.round, msg.from, msg.pred, pl[1]), pl[2])

\* Events

EventKinds == { "NewChain", "NewMessage", "pQC" }

Event(kind, data) == [ kind |-> kind, data |-> data ]

ChainEvents == [ kind : {"NewChain"}, data : Seq(Blocks) \X (EQCs \cup SUBSET ProposeMsgs) ]

MessageEvents == [ kind : {"NewMessage"}, data : Messages ]

PQCEvents == [ kind : {"pQC"}, data : PQCs ]

Events == ChainEvents \cup MessageEvents \cup PQCEvents

\* Helper operators

\* Since we store the blockchain from most recent block to genesis,
\* we need to reverse the list before checking prefixes
isPrefix(seq1, seq2) ==
    LET RECURSIVE Rev(_, _)
    Rev(s, acc) ==
        IF s = <<>> THEN acc
        ELSE
            LET h == hd(s) IN
            Rev(tl(s), cons(h, acc))
    rev(s) == Rev(s, <<>>)
    RECURSIVE is_prefix(_, _)
    is_prefix(s1, s2) ==
        \/ s1 = <<>>
        \/ /\ s2 /= <<>>
           /\ hd(s1) = hd(s2)
           /\ is_prefix(tl(s1), tl(s2))
    IN
    \/ seq1 = seq2
    \/ is_prefix(rev(seq1), rev(seq2))

\* head of [p]'s chain
head(p) ==
    LET bc == blockchain[p] IN
    IF bc = <<>> THEN genesis
    ELSE bc[1]

block_at_level(p, l) ==
    LET L == level[p] IN
    CASE L > l -> blockchain[p][L - l]

\* Returns [p]'s previous block
prev_level(p) == IF level[p] <= 1 THEN 0 ELSE level[p] - 1

prev_block(p) ==
    IF level[p] <= 1 THEN genesis
    ELSE block_at_level(p, level[p] - 1)

best_chain(p, cs) ==
    LET good == { c \in cs : isPrefix(tl(blockchain[p]), c) }
        best == { c \in good : \A cc \in good : Len(c) >= Len(cc) }
    IN
    best

\* checks validity of a pQC
isValidPQC(l, r, h, u, pqc) ==
    \/ l = 1 /\ r = 1
    \/ LET qc == pQC_of_msgs(pqc)
           _l == qc[1]
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

\* checks validity of an eQC
isValidEQC(l, r, h, u, eqc) ==
    \/ l = 1 /\ r = 1
    \/ LET qc == eQC_of_msgs(eqc)
           _l == qc[1]
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
        /\ isValidEQC(prev_level(p), pr, ph.pred, pb.contents, _eQC)
        /\ \* the value is newly generated
            \/ _pQC = {} /\ eR = 0
            \* checks for recycled value
            \/ LET __pQC == Pick(_pQC) IN
               /\ __pQC.payload = u
               /\ __pQC.round = eR
               /\ isValidPQC(level[p], eR, hash(head(p)), u, _pQC)
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
        /\ isValidPQC(level[p], msg.round, head(p).header.pred, u, _pQC)

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
                eQC      : {head_cert[p]}
              ],
              contents : {value}
            ]
    IN
    IF endorsable_value[p] = NULL THEN newly_gen(TRUE)
    ELSE
        [ header :
            [ level    : {l},
              round    : {endorsable_round[p]},
              proposer : {p},
              pred     : {pred},
              eQC      : {head_cert[p]}
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
\* The following actions are taken by correct processes

\* if the chain agrees with what [p] has seen thus far,
\* [p] updates their blockchain, head_cert, level, and round
updateState(p, chain, cert) ==
    IF isPrefix(tl(blockchain[p]), chain) THEN
        /\ level'      = [ level      EXCEPT ![p] = Len(chain) ]
        /\ round'      = [ round      EXCEPT ![p] = 1 ]
        /\ blockchain' = [ blockchain EXCEPT ![p] = chain ]
        /\ head_cert'  = [ head_cert  EXCEPT ![p] = cert ]
    ELSE
        /\ round' = [ round EXCEPT ![p] = @ + 1 ]
        /\ UNCHANGED <<chain_vars, level>>

\* aggregates chains and certificates from a set of bakers [Q]
chain_and_certs(Q) ==
    LET RECURSIVE _chains(_, _)
        _chains(QQ, acc) ==
            IF QQ = {} THEN acc
            ELSE
                LET q    == Pick(QQ)
                    pOrC == IF proposal_msgs(q) = {} THEN head_cert[q]
                            ELSE proposal_msgs(q)
                IN
                _chains(QQ \ {q}, acc \cup {<<blockchain[q], pOrC>>})
    IN
    _chains(Q, {})

\* pullChain primitive - invoked on timeouts and when [p] is "behind"
\* a process finds out that it's "behind" when they get messages from future rounds/levels
\* when a process is "behind", they will request to pull everyone else's chain
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
        IF t = "Propose" THEN p.payload[1]
        ELSE propOrCert

\* if [p] has a quorum of preendorsements or is handling a Propose or Preendorsements message,
\* then they update their endorsable_value, endorsable_round, and preendorsement_qc
\* if [p] is handling an Endorse message in the ENDORSE phase, they lock on the value and round
updateEndorsable(p, msg) ==
    LET t    == msg.type
        r    == msg.round
        pmfp == preendorse_msgs_for_pQC(p)
        pre  == \* count incoming message
            IF r = round[p] THEN
                CASE t = "Preendorse" -> pmfp \cup {msg}
                  [] t = "Endorse" -> pmfp \cup msg.payload
                  [] OTHER -> pmfp
            ELSE pmfp
    IN
    IF r = round[p] THEN
        IF card(pre) >= 2 * f + 1 THEN
            LET pl == Pick(pre).payload IN
            /\ endorsable_value'  = [ endorsable_value  EXCEPT ![p] = pl ]
            /\ endorsable_round'  = [ endorsable_round  EXCEPT ![p] = round[p] ]
            /\ preendorsement_qc' = [ preendorsement_qc EXCEPT ![p] = pre ]
            /\ IF t = "Endorse" /\ phase[p] \in {"E", "E_"} THEN
                    /\ locked_value' = [ locked_value EXCEPT ![p] = pl ]
                    /\ locked_round' = [ locked_round EXCEPT ![p] = round[p] ]
               ELSE UNCHANGED locked_vars
        ELSE
            IF t \in { "Propose", "Preendorsements" } THEN
                LET pQC == get_pQC(msg) IN
                IF roundQC(pQC) > endorsable_round[p] THEN
                    /\ endorsable_value'  = [ endorsable_value  EXCEPT ![p] = valueQC(pQC) ]
                    /\ endorsable_round'  = [ endorsable_round  EXCEPT ![p] = roundQC(pQC) ]
                    /\ preendorsement_qc' = [ preendorsement_qc EXCEPT ![p] = pQC ]
                    /\ UNCHANGED locked_vars
                ELSE UNCHANGED <<endorsable_vars, locked_vars>>
            ELSE UNCHANGED <<endorsable_vars, locked_vars>>
    ELSE UNCHANGED <<endorsable_vars, locked_vars>>

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
            \/ /\ e.kind = "pQC"
               /\ Pick(e.data).level > l }
    ]

\* which head is better, [p]'s or the head of chain?
\* boolean expression
better_head(p, chain, propOrCert) ==
    IF propOrCert = {} THEN FALSE
    ELSE
        LET h  == hd(chain)
            l  == h.header.level
            r  == h.header.round
            t  == Pick(propOrCert).type
            pr == prev_block(p).header.round
        IN
        \* proposal
        CASE t = "Propose" ->
            LET eR == Pick(propOrCert).payload[3] IN
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
    /\ isValidEQC(l, r, h, u, cert)
    /\ card(cert) >= 2 * f + 1
    /\ b.header.eQC = cert

\* given [prev_b] is a valid block, we check whether [b] is valid
isValidValue(b, prev_b) ==
    LET bh  == b.header
        l   == bh.level
        r   == bh.round
        eQC == bh.eQC
    IN
    \* consistency = blocks are hash-linked
    /\ bh.pred = hash(prev_b)
    \* legitimacy = correct proposer & correct endorsement quorum certificate
    /\ bh.proposer = PROPOSER[l][r]
    /\ LET pl == prev_b.header.level IN
        /\ { eqc.from : eqc \in eQC } \subseteq COMMITTEE[pl] \* eQC messages are from committee members
        /\ Pick({ eqc.level : eqc \in eQC }) = l \* eQC messages are for the correct level
        /\ Pick({ eqc.round : eqc \in eQC }) = r \* eQC messages are for the correct round
        /\ card(eQC) >= 2 * f + 1

\* check cert justifies head of chain & chain is valid
\* boolean valued
validChain(chain, _cert) ==
    LET cert == eQC_of_msgs(_cert)
        l == cert[1]
        h == cert[3]
        u == cert[4]
        s == cert[5]
    IN
    \/ chain = <<genesis>>
    \/ /\ justify(hd(chain), _cert)
       /\ BiMap(isValidValue, chain)

reset(p) ==
    /\ endorsable_value'  = [ endorsable_value  EXCEPT ![p] = NULL ]
    /\ endorsable_round'  = [ endorsable_round  EXCEPT ![p] = 0 ]
    /\ locked_value'      = [ locked_value      EXCEPT ![p] = NULL ]
    /\ locked_round'      = [ locked_round      EXCEPT ![p] = 0 ]
    /\ preendorsement_qc' = [ preendorsement_qc EXCEPT ![p] = {} ]

\* decisionOpt = NULL or <<block, certificate>>
advance(p, decisionOpt) ==
    /\ IF decisionOpt = NULL THEN
            \* stay at current level and go to next round
            \* a value has not been decided for this level
            /\ round' = [ round EXCEPT ![p] = @ + 1 ]
            /\ filterMessages(p, level[p], round'[p])
            /\ UNCHANGED <<chain_vars, level, locked_vars, endorsable_vars, events>>
        ELSE
            LET blk  == decisionOpt[1]
                cert == decisionOpt[2]
            IN
            \* go to the next level
            \* - a value has been decided for the current level
            \* - reset endorsable/locked round and value
            /\ reset(p)
            /\ updateState(p, cons(blk, blockchain[p]), cert)
            /\ filterMessages(p, level'[p], round'[p])
            /\ filterEvents(p, level[p])
    /\ phase' = [ phase EXCEPT ![p] = IF p = PROPOSER[level'[p]][round'[p]] THEN "P" ELSE "P_" ]

\* if [p] has decided (i.e. has seen an eQC in the ENDORSE phase), this returns the decided value at their level
\* otherwise, it returns NULL
get_decision(p) ==
    LET endorsements == endorse_msgs(p)
        l == level[p]
        r == locked_round[p]
        h == hash(head(p))
        u == locked_value[p]
        b == block(header(l, r, PROPOSER[l][r], h, endorsements), u)
    IN
    IF card(endorsements) < 2 * f + 1 THEN NULL
    ELSE <<b, endorsements>>

\* data = <<chain, propOrCert>>
HandleNewChain(p, data) ==
    LET chain == data[1]
        pOrC  == data[2]
        cert  == get_certificate(pOrC)
    IN
    /\ validChain(chain, cert)
    /\ CASE Len(chain) > level[p] ->
            /\ updateState(p, chain, cert)
            /\ filterMessages(p, level'[p], round'[p])
            /\ filterEvents(p, level[p])
            /\ UNCHANGED endorsable_vars
         [] Len(chain) = level[p] ->
            /\ better_head(p, chain, cert)
            /\ updateState(p, chain, cert)
            /\ filterMessages(p, level'[p], round'[p])
            /\ filterEvents(p, level[p])
            /\ UNCHANGED endorsable_vars
         [] OTHER -> UNCHANGED <<messages, endorsable_vars, level, round, chain_vars>>

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
                /\ updateEndorsable(p, msg)
                /\ messages' = [ messages EXCEPT ![p] = @ \cup {msg} ]
                /\ UNCHANGED chain_vars
            ELSE UNCHANGED <<vars_handle_msg, messages>>
        /\ events' = [ events EXCEPT ![p] = @ \ {ev} ]
    ELSE
        IF \/ l = level[p] /\ h /= hp   \* same level, different predecessor
           \/ l > level[p]              \* [p] is behind [q]
        THEN
            \* [p] does pullChain since they may have missed blocks
            /\ pullChain(p, events[p] \ {ev}, Procs)
            /\ UNCHANGED <<vars_handle_msg, messages>>
        ELSE
            \* [q] is either behind or their chain is incompatible with [p]'s
            /\ events' = [ events EXCEPT ![p] = @ \ {ev} ]
            /\ UNCHANGED <<vars_handle_msg, messages>>

\* these messages have already been validated, they are Preendorse messages which are being re-broadcasted
\* now they're being passed as a quorum certificate
HandlePQCMessage(p, msgs) ==
    /\ messages' = [ messages EXCEPT ![p] = @ \cup msgs ]
    /\ UNCHANGED vars_handle_msg

\* [p] handles one event
HandleEvent(p, ev) ==
    LET k == ev.kind IN
    CASE k = "NewChain" ->
            /\ HandleNewChain(p, ev.data)
            /\ events' = [ events EXCEPT ![p] = @ \ {ev} ]
            /\ UNCHANGED locked_vars
      [] k = "NewMessage" ->
            /\ HandleConsensusMessage(p, ev)
            /\ UNCHANGED <<level, round>>
      [] k = "pQC" ->
            /\ HandlePQCMessage(p, ev.data)
            /\ events' = [ events EXCEPT ![p] = @ \ {ev} ]
            /\ UNCHANGED <<level, round>>

\* PROPOSE - committee member
\* the proposer of a round proposes a value
\*  - if [p] has an endorsable value, they propose this
\*  - otherwise, [p] proposes a newly generated value
\* after broadcasting their proposal, [p] handles events
Propose(p) ==
    LET l   == level[p]
        r   == round[p]
        h   == hash(head(p))
        eQC == head_cert[p]
        pQC == preendorsement_qc[p]
        u   == IF endorsable_value[p] /= NULL THEN endorsable_value[p] ELSE TRUE
        eR  == endorsable_round[p]
    IN
    \E v \in proposals(p, l, r) :
        /\ \/ p \in FAULTY_PROCS
           \/ /\ p = PROPOSER[l][r]
              /\ phase[p] = "P"
        /\ phase' = [ phase EXCEPT ![p] = "P_" ]
        \* broadcasts Propose message to everyone
        /\ events' = broadcast(events, Procs, Event("NewMessage", propose_msg(v, <<eQC, u, eR, pQC>>)))
        /\ UNCHANGED vars_no_phase_event

\* [p] handles an event while in the PROPOSE phase
\* and either stays in the PROPOSE phase or transitions to PREENDORSE
Propose_handle(p) == \E np \in {"P_", "PE"}, ev \in events[p] :
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \in COMMITTEE[level[p]]
          /\ phase[p] \in {"P", "P_"}
    /\ phase' = [ phase EXCEPT ![p] = np ]
    /\ HandleEvent(p, ev)

\* whether or not [p] has events, they can progress directly to the PREENDORSE phase
Propose_(p) ==
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \in COMMITTEE[level[p]]
          /\ events[p] = {}
          /\ phase[p] \in {"P", "P_"}
    /\ phase' = [ phase EXCEPT ![p] = "PE" ]
    /\ UNCHANGED vars_no_phase

\* PREENDORSE - committee member
\* If [p] has seen the current proposal, they do:
\*  - if they're not locked on a value in the current or a future round, preendorse the proposal
\*  - otherwise, advertise their "better" locked value
Preendorse(p) == \E msg \in proposal_msgs(p) :
    LET eR == msg.payload[3] IN
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \in COMMITTEE[level[p]]
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

\* [p] is currently in the PREENDORSE phase
\*  - [p] handles an incoming event
\*  - [p] either stays in the PREENDORSE phase or transitions to ENDORSE
Preendorse_handle(p) == \E ev \in events[p], np \in {"PE_", "E"} :
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \in COMMITTEE[level[p]]
          /\ phase[p] \in { "PE", "PE_" }
    /\ phase' = [ phase EXCEPT ![p] = np ]
    /\ HandleEvent(p, ev)

\* [p] is currently in the PREENDORSE phase
\* [p] either stays in the PREENDORSE phase or transitions to ENDORSE
Preendorse_(p) ==
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \in COMMITTEE[level[p]]
          /\ phase[p] \in {"PE", "PE_"}
    /\ phase' = [ phase EXCEPT ![p] = "E" ] 
    /\ UNCHANGED vars_no_phase

\* ENDORSE - committee member
\* [p] is in the ENDORSE phase
\* - if [p] has seen a preendorsement QC, then they lock on this value and record the pQC
\* - otherwise, maybe handle some events
Endorse(p) == \E msg \in preendorse_msgs_for_pQC(p) :
    LET pre == preendorse_msgs_for_pQC(p) IN
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \in COMMITTEE[level[p]]
          /\ phase[p] = "E"
    /\ phase' = [ phase EXCEPT ![p] = "E_" ]
    /\ IF card(pre) >= 2 * f + 1 THEN
            LET u == proposed_value(p)
                l == level[p]
                r == round[p]
                h == hash(head(p))
            IN
            /\ locked_value'      = [ locked_value      EXCEPT ![p] = u ]
            /\ locked_round'      = [ locked_round      EXCEPT ![p] = r ]
            /\ endorsable_value'  = [ endorsable_value  EXCEPT ![p] = u ]
            /\ endorsable_round'  = [ endorsable_round  EXCEPT ![p] = r ]
            /\ preendorsement_qc' = [ preendorsement_qc EXCEPT ![p] = pre ]
            /\ events' = broadcast(
                broadcast(events, Procs, Event("NewMessage", endorse_msg(p, l, r, h, pre))),
                Procs,
                Event("pQC", pre)
               )
            /\ UNCHANGED <<messages, chain_vars, level, round>>
        ELSE UNCHANGED <<comm_vars, chain_vars, endorsable_vars, locked_vars, level, round>>

\* [p] is in the ENDORSE phase, has events to handle, and handles one
\* [p] stays in the ENDORSE phase until they advance
Endorse_handle(p) == \E ev \in events[p], np \in {"E", "E_"} :
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \in COMMITTEE[level[p]]
          /\ phase[p] \in {"E", "E_"}
    /\ phase' = [ phase EXCEPT ![p] = np ]
    /\ HandleEvent(p, ev)

\* [p] advances to the next round/level depending on whether a decision has been made
\* [p] does not handle any events
Endorse_advance(p) ==
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \in COMMITTEE[level[p]]
          /\ phase[p] \in {"E", "E_"}
    /\ advance(p, get_decision(p))

\* PROPOSE - observer
ObserveP_handle(p) == \E ev \in events[p] :
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \notin COMMITTEE[level[p]]
          /\ phase[p] = "P_"
    /\ HandleEvent(p, ev)
    /\ UNCHANGED phase

ObserveP_PE_handle(p) == \E ev \in events[p] :
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \notin COMMITTEE[level[p]]
          /\ phase[p] = "P_"
    /\ HandleEvent(p, ev)
    /\ phase' = [ phase EXCEPT ![p] = "PE_" ]

ObserveP_PE(p) ==
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \notin COMMITTEE[level[p]]
          /\ phase[p] = "P_"
    /\ phase' = [ phase EXCEPT ![p] = "PE_" ]
    /\ UNCHANGED vars_no_phase

\* PREENDORSE - observer
ObservePE_handle(p) == \E ev \in events[p] :
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \notin COMMITTEE[level[p]]
          /\ phase[p] = "PE_"
    /\ HandleEvent(p, ev)
    /\ UNCHANGED phase

ObservePE_E_handle(p) == \E ev \in events[p] :
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \notin COMMITTEE[level[p]]
          /\ phase[p] = "PE_"
    /\ HandleEvent(p, ev)
    /\ phase' = [ phase EXCEPT ![p] = "E_" ]

ObservePE_E(p) ==
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \notin COMMITTEE[level[p]]
          /\ phase[p] = "PE_"
    /\ phase' = [ phase EXCEPT ![p] = "E_" ]
    /\ UNCHANGED vars_no_phase

\* ENDORSE - observer
ObserveE(p) == \E ev \in events[p] :
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \notin COMMITTEE[level[p]]
          /\ phase[p] = "E_"
    /\ phase' = [ phase EXCEPT ![p] = "E_" ]
    /\ HandleEvent(p, ev)

ObserveE_advance(p) ==
    /\ \/ p \in FAULTY_PROCS
       \/ /\ p \notin COMMITTEE[level[p]]
          /\ phase[p] = "E_"
    /\ advance(p, get_decision(p))

OnTimeoutPullChain(p) ==
    /\ pullChain(p, events[p], Procs)
    /\ UNCHANGED <<messages, chain_vars, state_vars, locked_vars, endorsable_vars>>

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

Next == \E p \in Procs :
    \* committee member actions
    \/ Propose(p)
    \/ Propose_handle(p)
    \/ Preendorse(p)
    \/ Preendorse_handle(p)
    \/ Endorse(p)
    \/ Endorse_handle(p)
    \/ Endorse_advance(p)
    \* noncommittee member actions
    \/ ObserveP_handle(p)
    \/ ObserveP_PE_handle(p)
    \/ ObserveP_PE(p)
    \/ ObservePE_handle(p)
    \/ ObservePE_E_handle(p)
    \/ ObservePE_E(p)
    \/ ObserveE(p)
    \/ ObserveE_advance(p)
    \* any process can timeout
    \/ OnTimeoutPullChain(p)

Fairness == SF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

(**************)
(* Properties *)
(**************)

\* Invariants
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

\* The head block is not finalized until there is a confirmation on top of it
Agreement == \A a, b \in CORRECT_PROCS :
    \/ isPrefix(tl(blockchain[a]), tl(blockchain[b]))
    \/ isPrefix(tl(blockchain[b]), tl(blockchain[a]))

Validity == \A p \in CORRECT_PROCS : validChain(blockchain[p], head_cert[p])

CorrectLevels == \A p \in CORRECT_PROCS : level[p] = Len(blockchain[p])

BoundedMessageBuffers == \A p \in CORRECT_PROCS : card(messages[p]) <= 4 * n + 2

\* Preendorsement quorum certificates are collections of messages with a common:
\* - level
\* - round
\* - predecessor
\* - value
consistentPQC(pQC) ==
    /\ card(pQC) >= 2 * f + 1
    /\ card({ pmsg.level   : pmsg \in pQC }) = 1 \* common level
    /\ card({ pmsg.round   : pmsg \in pQC }) = 1 \* common round
    /\ card({ pmsg.pred    : pmsg \in pQC }) = 1 \* common predecessor
    /\ card({ pmsg.payload : pmsg \in pQC }) = 1 \* common value

PreendorsementQCs == \A p \in CORRECT_PROCS :
    LET pQC == preendorsement_qc[p] IN
    pQC /= {} <=>
        /\ consistentPQC(pQC)
        /\ endorsable_round[p] > 0
        /\ endorsable_value[p] /= NULL

\* Endorsement quorum certificates are collections of messages with a common:
\* - level
\* - round
\* - predecessor
\* each Endorse message in the QC must contain a consistent preendorsement QC
consistentEQC(eQC) ==
    /\ card(eQC) >= 2 * f + 1
    /\ card({ emsg.level : emsg \in eQC }) = 1 \* common level
    /\ card({ emsg.round : emsg \in eQC }) = 1 \* common round
    /\ card({ emsg.pred  : emsg \in eQC }) = 1 \* common predecessor
    /\ \A emsg \in eQC : consistentPQC(emsg.payload)
    \* all Preendorse messages in all Endorse messages have the same value
    /\ card(UNION { { pmsg.payload : pmsg \in emsg.payload } : emsg \in eQC }) = 1

\* head_cert is used to store the endorsement QC for the last decided value
HeadCerts == \A p \in CORRECT_PROCS : level[p] > 1 =>
    /\ consistentEQC(head_cert[p])
    /\ head_cert[p] = head(p).header.eQC

\* Endorsable values/rounds are set/reset simultaneously
Endorsables == \A p \in CORRECT_PROCS :
    \/ /\ endorsable_round[p] = 0
       /\ endorsable_value[p] = NULL
    \/ /\ endorsable_round[p] > 0
       /\ endorsable_value[p] /= NULL

\* Locked values/rounds are set/reset simultaneously
LockedValuesRounds == \A p \in CORRECT_PROCS :
    \/ /\ locked_round[p] = 0
       /\ locked_value[p] = NULL
    \/ /\ locked_round[p] > 0
       /\ locked_value[p] /= NULL

\* A value/round is locked iff it also an endorsable value/round
LockedIffEndorsable == \A p \in CORRECT_PROCS :
    \* no endorsable value/round => no lockedvalue/round
    /\ endorsable_round[p] = 0 =>
        /\ endorsable_round[p] = locked_round[p]
        /\ endorsable_value[p] = locked_value[p]
    \* locked value/round must be the same as endorsable value/round
    /\ locked_round[p] > 0 =>
        /\ endorsable_round[p] = locked_round[p]
        /\ endorsable_value[p] = locked_value[p]

\* Liveness
Progress == \A p \in CORRECT_PROCS : []<><< Len(blockchain'[p]) > Len(blockchain[p]) >>_vars

===========================
