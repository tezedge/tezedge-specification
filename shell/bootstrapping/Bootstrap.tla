---- MODULE Bootstrap ----

EXTENDS FiniteSets, Naturals, Sequences, TLC, Hash, Samples

CONSTANTS
    NODES,              \* set og node ids
    MIN_PEERS,          \* minimum number of peers
    MAX_PEERS,          \* maximum number of peers
    MAX_OPS,            \* maximum number of operations per block
    MAX_SCORE           \* maximum peer score

VARIABLES
    greylist,           \* the node's set of greylisted peers
    messages,           \* the node's set of messages
    chain,              \* the node's local chain
    connections,        \* the node's set of connections
    current_head,       \* the node's current head
    peer_head,          \* the node's peers' current heads
    peer_score,         \* metric for peer reliability
    earliest_hashes,    \* TODO
    pending_headers,    \* TODO
    pending_operations, \* TODO
    sent_get_branch,    \* the node's set of peers to whom they have sent a Get_current_branch message
    sent_get_headers,   \* the node's function from peers to whom they have sent a Get_block_headers message to the requested headers
    sent_get_ops,       \* the node's function from peers to whom they have sent a Get_operations message to the requested operations
    recv_branch,        \* the node's set of peers from whom they have received a Current_branch message
    recv_head,          \* TODO
    recv_header,        \* the node's function from peers to the set of headers & hashes received
    recv_operation      \* the node's function from peers to set of operations received

VARIABLES
    trace,              \* TODO
    mem_size            \* each good bootstrapping node's estimated memory usage

\* inclusive variables
sent_vars    == <<sent_get_branch, sent_get_headers, sent_get_ops>>
recv_vars    == <<recv_branch, recv_head, recv_header, recv_operation>>
pending_vars == <<pending_headers, pending_operations>>

\* exclusive variables
non_conn_vars   == <<current_head, sent_vars, recv_vars>>
non_branch_vars == <<connections, current_head, sent_get_headers, sent_get_ops, recv_header, recv_operation>>
non_header_vars == <<connections, current_head, sent_get_branch, sent_get_ops, recv_branch, recv_operation>>
non_op_vars     == <<connections, current_head, sent_get_branch, sent_get_headers, recv_branch, recv_header>>
non_pipe_vars   == <<connections, current_head, recv_vars>>
non_recv_vars   == <<connections, current_head, sent_vars>>
non_node_vars   == <<connections, current_head, sent_vars, recv_vars>>
non_trace_vars  == <<connections, sent_vars, recv_vars>>
non_hd_q_vars   == <<connections, current_head, sent_vars, recv_vars>>
non_op_q_vars   == <<connections, current_head, sent_vars, recv_vars>>
non_phase_vars  == <<messages, greylist, non_trace_vars>>

\* all variables
vars == <<greylist, messages, chain, connections, current_head, peer_head, peer_score, earliest_hashes, pending_vars, sent_vars, recv_vars>>

(********)
(* Note *)
(********************************************************************************************************************)
(* pending_headers is a DAG                                                                                         *)
(* Each node is a header and an edge exists between nodes iff they have the parent-child relationship.              *)
(* The edge is directed from the child to the parent.                                                               *)
(* It is implemented in this spec as a function from levels to sets of headers, higher level headers near the Head. *)
(********************************************************************************************************************)

----

(***********)
(* Helpers *)
(***********)

\* [1] General helpers

Card(s) == Cardinality(s)

Set_op(s) == { ss \in SUBSET s : Card(ss) <= MAX_OPS }

NESet(s) == SUBSET s \ {{}}

NESeq(s) == Seq(s) \ {<<>>}

Pick(s) == CHOOSE x \in s : TRUE

Cons(x, seq) == <<x>> \o seq

RECURSIVE map(_, _, _)
map(f(_), seq, acc) ==
    IF seq = <<>> THEN acc
    ELSE
        LET x == Head(seq) IN
        map(f, Tail(seq), Append(acc, f(x)))

Map(f(_), seq) == map(f, seq, <<>>)

RECURSIVE Forall(_, _)
Forall(p(_), seq) ==
    \/ seq = <<>>
    \/ /\ p(Head(seq))
       /\ Forall(p, Tail(seq))

\* extract each element
Extract(seq) ==
    CASE seq = <<>> -> <<>>
      [] Forall(LAMBDA s : Card(s) = 1, seq) -> Map(Pick, seq)

ToSet(seq) == { seq[i] : i \in DOMAIN seq }

RECURSIVE AppendAll(_, _)
AppendAll(seq1, seq2) ==
    IF seq2 = <<>> THEN seq1
    ELSE AppendAll(Append(seq1, Head(seq2)), Tail(seq2))

\* [seq] is a sequence of sets
RECURSIVE remove(_, _, _)
remove(elem, seq, acc) ==
    IF seq = <<>> THEN acc
    ELSE
        LET s == Head(seq) IN
        IF elem \notin s THEN remove(elem, Tail(seq), Append(acc, s))
        ELSE AppendAll(Append(acc, s \ {elem}), Tail(seq))

Remove(elem, seq) == remove(elem, seq, <<>>)

RECURSIVE seq_of_set(_, _)
seq_of_set(s, acc) ==
    IF s = {} THEN acc
    ELSE
        LET x == Pick(s)
            t == s \ {x}
        IN seq_of_set(t, Append(acc, x))

SetToSeq(s) == seq_of_set(s, <<>>)

\* header level comparison
min_level_cmp(h1, h2) == h1.level <= h2.level

max_level_cmp(h1, h2) == min_level_cmp(h2, h1)

Min_level_seq(seq) ==
    CASE seq /= <<>> -> Head(SortSeq(seq, min_level_cmp))

Min_level_set(s) == Min_level_seq(SetToSeq(s))

Max_level_seq(seq) ==
    CASE seq /= <<>> -> Head(SortSeq(seq, max_level_cmp))

Max_level_set(s) == Max_level_seq(SetToSeq(s))

Max_hd_set(s) ==
    LET max_fit_hds  == { x \in s : \A y \in s : x.fitness >= y.fitness }
        max_fit_lvls == { x \in max_fit_hds : \A y \in max_fit_hds : x.level >= y.level }
    IN
    Pick(max_fit_lvls)

Max_set(s) == Pick({ x \in s : \A y \in s : x >= y })


\* [2] Spec-specific helpers

N == Card(NODES)

\* sets of connections
ConnectionSets == { ps \in SUBSET NODES : Card(ps) >= MIN_PEERS /\ Card(ps) <= MAX_PEERS }

\* block levels
Levels  == Nat \ {0}
Levels0 == Nat

\* phases
init_phase      == <<"init", {}>>
search_phase    == <<"searching_for_major_branch", {}>>
major_phase(ls) == <<"gathering_evidence", ls>>
apply_phase(ls) == <<"building_blocks", ls>>

Phase_init   == { init_phase }
Phase_search == { search_phase }
Phase_major  == { major_phase(ls) : ls \in SUBSET Levels }
Phase_apply  == { apply_phase(ls) : ls \in SUBSET Levels }

Phases == Phase_init \cup Phase_search \cup Phase_major \cup Phase_apply

\* fitness
Fitness == Nat

\* context hashes
ContextHashes == Int

\* hash types
Hashes   == Int
OpHashes == Int

header(l, pred, ctx, fit, op) ==
    [ level |-> l, predecessor |-> pred, context |-> ctx, fitness |-> fit, ops_hash |-> op ]

header_with_hash(hd, h) == [ header |-> hd, hash |-> h ]

operation(bh, op) == [ block_hash |-> bh, op |-> op ]
operations(bh, ops) == [ block_hash : {bh}, op : ops ]
block(hdr, ops) == [ header |-> hdr, ops |-> ops ]
hash(hd) == Hash(hd)

gen_header == header(0, 0, hash({}), 0, hash({}))
gen_operations == operations(hash(gen_header), {})
genesis == block(gen_header, gen_operations)

\* headers
Headers  == [
    level       : Levels0,
    context     : ContextHashes,
    fitness     : Fitness,
    predecessor : Hashes,
    ops_hash    : OpHashes
]

HeadersWithHash == [ header : Headers, hash : Hashes ]

\* operations
Ops == Nat
Operations == [ block_hash : Hashes, op : SUBSET Ops ]
OperationHashes == Int

\* blocks
Blocks == [ header : Headers, ops : SUBSET Ops ]

\* history
History == Seq(Levels \X Hashes)
Locators == [ current_head : Headers, history : History ]

\* 

received_operations_block_hash(n, bh) == { op \in recv_operation[n] : op.block_hash = bh }

all_recv_operations_block_hash(bh) == UNION { received_operations_block_hash(n, bh) : n \in NODES }

\* all fetched data
fetched_hashes_node(n)  == { p[1] : p \in recv_header[n] }
fetched_headers_node(n) == { p[2] : p \in recv_header[n] }

all_header_data    == UNION ToSet(pending_headers)
fetched_hashes     == UNION { fetched_hashes_node(n) : n \in NODES }
fetched_headers    == UNION { fetched_headers_node(n) : n \in NODES }
fetched_operations == UNION { recv_operation[n] : n \in NODES }

fetched_ops_block_hash(bh)     == { op \in fetched_operations : op.block_hash = bh }
num_fetched_ops_block_hash(bh) == Card(fetched_ops_block_hash(bh))

\* peer data

chain_levels(n) == peer_head[n].level

num_peers == Card(connections \cup greylist)

peers_at_level(l) == { n \in NODES : chain_levels(n) = l }

peers_at_or_above_level(l) == { n \in NODES : chain_levels(n) >= l }

highest_major_level ==
    LET major_levels == { l \in Levels :
        \* #(peers of  at or above level [l]) / #peers > 1/2
        (2 * Card(peers_at_or_above_level(l))) > num_peers
    } IN
    IF major_levels = {} THEN 0
    ELSE Max_set(major_levels)

recv_hashes[ n \in NODES ] ==
    LET fit_hash == { hash(peer_head[n]) }
        br_hs    == ToSet(recv_branch[n])
        bh_hs    == { hash(hd) : hd \in fetched_headers }
    IN
    fit_hash \cup br_hs \cup bh_hs

all_recv_hashes == UNION { recv_hashes[n] : n \in NODES }

major_hashes == { fh \in all_recv_hashes :
    \* majority of peers agree with [fh]
    LET seen_agreeing == { n \in NODES : fh \in recv_branch[n] } IN
    (2 * Card(seen_agreeing)) > num_peers }

has_major_hashes == major_hashes /= {}

major_headers == { hd \in fetched_headers :
    \* majority of peers agree with [hd]
    LET seen_agreeing == { n \in NODES : hd \in recv_header[n] } IN
    (2 * Card(seen_agreeing)) > num_peers }

headers_with_hash(bh) == { p \in all_header_data : p[1] = bh }

lookup_block_hash(bh) == Pick(headers_with_hash(bh))

RECURSIVE descendant(_, _)
descendant(hd1, hd2) ==
    CASE hd1.fitness = hd2.fitness -> hd1 = hd2
      [] hd1.fitness < hd2.fitness ->
        LET bh == hash(hd2) IN
        \/ bh = hd1.predecessor
        \/ \E hd \in headers_with_hash(bh): descendant(hd, hd2)

----

(***************)
(* Assumptions *)
(***************)

\* TODO

----

(************)
(* Messages *)
(************)

\* TODO messages
\* - Bootstrap
\* - Advertise
\* - Swap_request???

\* [1] Requests
\* [1.1] Good requests
GetCurrentBranchMessages == [ type : {"Get_current_branch"} ]
GetBlockHeadersMessages  == [ type : {"Get_block_headers"}, hashes : NESet(Levels \X Hashes) ]
GetOperationsMessages    == [ type : {"Get_operations"},    op_hashes : NESet(OperationHashes) ]
GoodGetMessages          == GetCurrentBranchMessages \cup GetBlockHeadersMessages \cup GetOperationsMessages

GetMessages == GoodGetMessages

\* [1.4] Request constructors
get_current_branch_msg    == [ type |-> "Get_current_branch" ]
get_block_headers_msg(hs) == [ type |-> "Get_block_headers", hashes    |-> hs ]
get_operations_msg(ohs)   == [ type |-> "Get_operations",    op_hashes |-> ohs ]

\* [1.5] Sets of request types
current_branch_msgs(n) == { msg \in messages[n] : msg.type = "Current_branch" }
block_header_msgs(n)   == { msg \in messages[n] : msg.type = "Block_header" }
operation_msgs(n)      == { msg \in messages[n] : msg.type = "Operation" }

\* [1.6] Request predicates
has_requested_branch_from(n)  == n \in sent_get_branch
has_requested_headers_from(n) == sent_get_headers[n] /= {}
has_requested_ops_from(n)     == sent_get_ops[n] /= {}

requested_branch_from  == { n \in connections : has_requested_branch_from(n) }
requested_headers_from == { n \in connections : has_requested_headers_from(n) }
requested_ops_from     == { n \in connections : has_requested_ops_from(n) }

has_received_branch(n)    == recv_branch[n] /= {}
has_received_header(n)    == recv_header[n] /= {}
has_received_operation(n) == recv_operation[n] /= {}

received_branch_from == { n \in NODES : has_received_branch(n) }
received_header_from == { n \in NODES : has_received_header(n) }
received_op_from     == { n \in NODES : has_received_operation(n) }

\* [2] Responses
CurrentBranchMessages == [ type : {"Current_branch"}, from : NODES, locator : Locators ]
BlockHeaderMessages   == [ type : {"Block_header"},   from : NODES, header : Headers ]
OperationsMessages    == [ type : {"Operation"},      from : NODES, operation : Operations ]
ResponseMessages  == CurrentBranchMessages \cup BlockHeaderMessages \cup OperationsMessages

current_branch_msg(n, l) == [ type |-> "Current_branch", from |-> n, locator   |-> l ]
block_header_msg(n, hd)  == [ type |-> "Block_header",   from |-> n, header    |-> hd ]
operation_msg(n, op)     == [ type |-> "Operation",      from |-> n, operation |-> op ]

\* [3] All messages
Messages             == GetMessages \cup ResponseMessages
AllBranchMessages    == { msg \in Messages : msg.type = "Current_branch" }
AllHeaderMessages    == { msg \in Messages : msg.type = "Block_header" }
AllOperationMessages == { msg \in Messages : msg.type = "Operation" }

----

\* TODO
\* peer_score - metric for peer reliability
\*   - max_score = 100 for example
\*   - if score[peer] < max_score then incr_score(peer) when valid message received
\*     else decr_score(peer) when timeout or disconnect
\* incr_score(peer) == peer_score' = [ peer_score EXCEPT ![peer] = min(@ + incr_amt, max_score) ]
\* decr_score(peer) == peer_score' = [ peer_score EXCEPT ![peer] = max(@ - decr_amt, 0) ]

\* header_data : [ header : HeadersWithHash, supporters : SUBSET Peers ]

header_datum(peer, hdwh) == [ header |-> hdwh.header, hash |-> hdwh.hash, supporters |-> {peer} ]
update_datum(peer, hdwh, sp) == [ header |-> hdwh.header, hash |-> hdwh.hash, supporters |-> sp \cup {peer} ]

pending_header_hashes(phs) == { ph.hash : ph \in phs }

\* add the support of [peers] to an existing header datum
\* [phds] is the set of pending headers at a specified level
add_support_to_datum(peers, datum, phds) ==
    \* update supporters for the header
    LET to_update == Pick({ hd \in phds : hd.hash = datum.hash })
        updated   == {[ to_update EXCEPT !.supporters = @ \cup peers ]}
    IN
    updated \cup (phds \ {to_update})

\* add a peer's support to a pending header
add_support(peer, hdwh, pending_hds) ==
    LET l == hdwh.header.level IN
    IF hdwh \notin pending_hds[l] THEN
        [ pending_hds EXCEPT ![l] = @ \cup {header_datum(peer, hdwh)} ]
    ELSE
        [ pending_hds EXCEPT ![l] = add_support_to_datum(peer, hdwh, @) ]

\* add a pending header to the collection
add_pending_header(peer, hdwh) ==
    LET l == hdwh.header.level IN
    IF l \notin DOMAIN pending_headers THEN
        pending_headers @@ l :> {header_datum(peer, hdwh)}
    ELSE add_support(peer, hdwh, pending_headers)

\* TODO
RECURSIVE update_support(_, _)
update_support(datum, pending_hds) ==
    LET l == datum.header.level - 1 IN
    IF l \notin DOMAIN pending_hds THEN pending_hds
    ELSE
        LET phds      == pending_hds[l]
            phashes   == { hd.hash : hd \in phds }
            pred_hash == datum.header.predecessor
        IN
        IF pred_hash \notin phashes THEN pending_hds
        ELSE
            LET pdatum      == Pick({ h \in phds : h.hash = pred_hash }) \* pending predecessor header
                supps       == datum.supporters                          \* child supporters
                new_pdatum  == [ pdatum EXCEPT !.supporters = @ \cup supps ]
                new_phds    == add_support_to_datum(supps, pdatum, phds) \* add child supporters to parent
                new_pending == [ pending_hds EXCEPT ![l] = new_phds ]
            IN
            update_support(new_pdatum, new_pending)


(***********)
(* Actions *)
(***********)

\* [0] Action helpers

Send(n, msg) ==
    messages' = [ messages EXCEPT ![n] = @ \cup {msg} ]

Drop(msg) ==
    LET n == msg.from IN
    messages' = [ messages EXCEPT ![n] = @ \ {msg} ]

\* [1] Request actions <- good bootstrapping nodes

SendGetCurrentBranch ==
    \E n \in connections :
        /\ ~has_requested_branch_from(n)
        /\ sent_get_branch' = sent_get_branch \cup {n}
        /\ UNCHANGED <<messages, greylist, non_branch_vars, recv_branch>>

\* TODO request all hashes from each peer
SendGetBlockHeaders ==
    \E n \in connections, bhs \in NESet(fetched_hashes) :
        /\ has_received_branch(n)
        /\ sent_get_headers' = [ sent_get_headers EXCEPT ![n] = @ \cup bhs ]
        /\ UNCHANGED <<messages, greylist, non_header_vars, recv_header>>

\* TODO change the operation request to take the corresponding block hash
SendGetOperations ==
    \E n \in connections, hd \in fetched_headers :
        LET bh  == hash(hd)
            ops == operations(bh, 1..hd.ops_hash)
            req == ops \ all_recv_operations_block_hash(bh)
            ohs == { <<bh, hash(op)>> : op \in req }
        IN
        /\ req /= {}
        /\ sent_get_ops' = [ sent_get_ops EXCEPT ![n] = @ \cup ohs ]
        /\ UNCHANGED <<messages, greylist, non_op_vars, recv_operation>>

\* [3] Bootstrapping nodes handle responses

HandleCurrentBranch == \E n \in NODES :
    \E msg \in current_branch_msgs(n) :
        LET hist    == msg.locator.history
            curr_hd == msg.locator.current_head
        IN
        /\ has_requested_branch_from(n)
        /\ Drop(msg)
        /\ peer_head' = [ peer_head EXCEPT ![n] =
                CASE curr_hd.level < @.level -> @
                  [] curr_hd.level > @.level -> curr_hd
                  \* curr_hd.level = @.level
                  [] curr_hd.fitness < @.fitness -> @
                  [] curr_hd.fitness < @.fitness -> curr_hd ]
        /\ recv_header'  = [ recv_header  EXCEPT ![n] = @ \cup {<<hash(curr_hd), curr_hd>>} ]
        /\ recv_branch'  = [ recv_branch  EXCEPT ![n] = @ \cup ToSet(hist) ]
        /\ UNCHANGED <<greylist, connections, current_head, sent_vars, recv_header, recv_operation>>

\* bootstrapping node receives a Block_header message
HandleBlockHeader == \E n \in NODES :
    \E msg \in block_header_msgs(n) :
        LET hd == msg.header
            h  == hash(hd)
        IN
        /\ h \in sent_get_headers[n]
        /\ hd \notin fetched_headers
        /\ Drop(msg)
        /\ recv_header' = [ recv_header EXCEPT ![n] = @ \cup {<<h, hd>>} ]
        /\ recv_branch' = [ recv_branch EXCEPT ![n] = @ \cup {h} ]
        /\ UNCHANGED <<greylist, non_recv_vars, recv_operation>>

\* bootstrapping node receives an Operation message
HandleOperation == \E n \in NODES :
    \E msg \in operation_msgs(n) :
        LET op == msg.operation
            bh == op.block_hash
        IN
        \E hd \in fetched_headers :
            /\ bh = hash(hd)
            /\ op \notin recv_operation[n]
            /\ Drop(msg)
            /\ recv_operation' = [ recv_operation EXCEPT ![n] = @ \cup {op} ]
            /\ UNCHANGED <<greylist, non_recv_vars, recv_branch, recv_header>>

\* TODO prevalidation actions
\* When in the major phase, once  has the header and operations for a block, they can must check that the operations are correct for that block
\* and move the header and set of operations to the corresponding prevalidated sets.

\* [4] Pipe enqueuing actions

\* move header from fetched_headers to header_pipe
EnqueueHeader ==
    LET phds == pending_headers IN
    /\ phds /= <<>>
    /\ LET hd == Max_level_set(phds) IN
        /\ pending_headers' = Remove(hd, pending_headers)
        \* /\ header_pipe'     = Cons(hd, header_pipe)
        /\ UNCHANGED <<messages, greylist, non_hd_q_vars>>

\* move operation from fetched_operations to operation_pipe
EnqueueOperations ==
    LET pops == pending_operations IN
    /\ pops /= <<>>
    /\ LET max  == Max_set({ op[1] : op \in pops })
           pair == Pick({ op \in pops : op[1] = max })
           ops  == pair[2]
       IN
        \* /\ pending_operations' = Remove(pending_operations)
        \* /\ operation_pipe'   = Cons(ops, operation_pipe)
        /\ UNCHANGED <<messages, greylist, non_op_q_vars>>

\* [6] Block validation

\* nodes form blocks from fetched headers and operations that have been enqueued in their respective pipes
apply_block(hd, ops) ==
    LET b == block(hd, ops) IN
    /\ pending_headers'    = Tail(pending_headers)
    /\ pending_operations' = Tail(pending_operations)
    /\ chain'              = Cons(b, chain)
    /\ UNCHANGED <<messages, greylist, non_pipe_vars>>

ApplyBlock ==
    LET hds == Extract(pending_headers)
        ops == pending_operations
    IN
    /\ hds /= <<>>
    /\ ops /= <<>>
    /\ LET hd == Head(hds)
           op == Head(ops)
        IN
        /\ op.block_hash = hash(hd)
        /\ apply_block(hd, ops)

\* [7] undesirable actions

\* [7.1] Byzantine actions

\* BadNodeSendsGoodBootstrapArbitraryMessage == \E n \in NODES :
\*     \E msg \in { m \in BadResponseMessages : m.from = n } :
\*         /\ n \in connections
\*         /\ Send(msg)
\*         /\ UNCHANGED <<n_messages, greylist, node_vars, bootstrapping_vars>>

\* [7.2] Timeout actions

greylist_node(n) == greylist' = greylist \cup {n}

filter_msgs_from(n) == messages'  = { msg \in messages : msg.from /= n }

remove_connection(n) == connections' = connections \ {n}

remove_data(n) ==
    /\ recv_branch'    = [ recv_branch    EXCEPT ![n] = {} ]
    /\ recv_header'    = [ recv_header    EXCEPT ![n] = {} ]
    /\ recv_operation' = [ recv_operation EXCEPT ![n] = {} ]

greylist_timeout(n) ==
    /\ greylist_node(n)
    /\ filter_msgs_from(n)
    /\ remove_connection(n)
    /\ UNCHANGED non_conn_vars

\* timeout => greylist but keep data
Timeout ==
    \/ \E n \in requested_branch_from :
        /\ ~has_received_branch(n)
        /\ greylist_timeout(n)
    \/ \E n \in requested_headers_from :
        /\ Card(recv_header[n]) /= Card(sent_get_headers[n])
        /\ greylist_timeout(n)
    \/ \E n \in requested_ops_from :
        /\ ~has_received_operation(n)
        /\ greylist_timeout(n)

\* [7.3] Greylist actions

Greylist ==
    \/ \E n \in connections : \E msg \in messages[n] :
        LET t == msg.type IN
        /\ n = msg.from
        /\ CASE t = "Current_branch" -> FALSE
             [] t = "Block_header" ->
                LET hd == msg.header IN
                \* send multiple headers at the same level
                \/ \E h \in recv_header[n] : h[2].level = hd.level
                \* never requested header with that hash
                \/ hash(hd) \notin sent_get_headers[n]
             [] t = "Operation" ->
                LET op == msg.operation
                    h  == op.block_hash
                IN
                \* never requested operation
                \/ h \notin sent_get_ops[n]
                \* invalid operation
                \/ \E hd \in fetched_headers :
                    /\ hash(hd) = h
                    /\ hd.ops_hash < op.op
             [] t = "bad" -> TRUE
        /\ greylist_node(n)
    \/ FALSE \* TODO fails cross validation

\* [8] Phase transitions

update_connections(ps)  == connections' = ps
update_current_head(hd) == current_head' = hd
log_transition(a)       == trace' = Cons(a, trace)

\* TODO

BanNode == FALSE

----

(*********************)
(* Initial predicate *)
(*********************)

BootstrappingInit ==
    /\ greylist           = {}
    /\ messages           = [ n \in NODES |-> {} ]
    /\ chain              = <<genesis>>
    /\ connections        = {}
    /\ current_head       = gen_header
    /\ peer_head          = [ n \in connections |-> gen_header ]
    /\ peer_score         = [ n \in connections |-> MAX_SCORE ]
    /\ earliest_hashes    = {}
    /\ pending_headers    = <<>>
    /\ pending_operations = <<>>
    /\ sent_get_branch    = {}
    /\ sent_get_headers   = [ n \in NODES |-> {} ]
    /\ sent_get_ops       = [ n \in NODES |-> {} ]
    /\ recv_branch        = [ n \in NODES |-> {} ]
    /\ recv_head          = [ n \in NODES |-> {} ]
    /\ recv_header        = [ n \in NODES |-> {} ]
    /\ recv_operation     = [ n \in NODES |-> {} ]

TraceInit == trace = <<init_phase>>

MemInit == mem_size = 0

Init ==
    /\ MemInit
    /\ TraceInit
    /\ BootstrappingInit

(****************)
(* Next actions *)
(****************)

Next ==
    \* Message passing
    \/ SendGetCurrentBranch
    \/ SendGetBlockHeaders
    \/ SendGetOperations
    \/ HandleCurrentBranch
    \/ HandleBlockHeader
    \/ HandleOperation

    \* Pipe maintanence
    \/ EnqueueHeader
    \/ EnqueueOperations
    \/ ApplyBlock

    \* Timeouts
    \/ Timeout

    \* Disciplinary actions
    \/ Greylist
    \/ BanNode

(*****************)
(* Specification *)
(*****************)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----

(**************)
(* Invariants *)
(**************)

\* [1] TypeOK - type safety

BootstrappingOK ==
    /\ greylist           \in SUBSET NODES
    /\ messages           \in [ NODES -> SUBSET ResponseMessages ]
    /\ chain              \in Seq(Blocks)
    /\ connections        \in SUBSET NODES
    /\ current_head       \in Blocks
    /\ peer_head          \in [ NODES -> Headers ]
    /\ peer_score         \in [ NODES -> Nat ]
    /\ earliest_hashes    \in SUBSET Hashes
    /\ pending_headers    \in Seq(SUBSET HeadersWithHash) 
    /\ pending_operations \in Seq(Operations)
    /\ sent_get_branch    \in SUBSET NODES
    /\ sent_get_headers   \in [ NODES -> SUBSET (Levels \X Hashes) ]
    /\ sent_get_ops       \in [ NODES -> SUBSET (Hashes \X OperationHashes) ]
    /\ recv_branch        \in [ NODES -> SUBSET (Levels \X Hashes) ]
    /\ recv_head          \in [ NODES -> SUBSET Headers ]
    /\ recv_header        \in [ NODES -> SUBSET (Hashes \X Headers) ]
    /\ recv_operation     \in [ NODES -> SUBSET Operations ]

TraceOK == trace \in Seq(Phases)

MemOK == mem_size \in Nat

TypeOK ==
    /\ MemOK
    /\ TraceOK
    /\ BootstrappingOK

\* [2] General safety properties

good_conns  == connections \cap NODES
good_headers(n) == {} \* b.header : b \in BLOCKS[n] }

ConnectionSafety ==
    /\ num_peers <= MAX_PEERS
    /\ greylist \cap connections = {}

\* A majority of good peers agree with a bootstrapping node's current head
CurrentHeadIsAlwaysMajor ==
    3 * Card({ n \in good_conns : current_head \in good_headers(n) }) > 2 * Card(good_conns)

\* Without a major branch, bootstrapping nodes do not change their head
HeadDoesNotChangeWithoutMajoritySupport ==
    highest_major_level = 0 => current_head = gen_header

\* TODO only enqueue headers and operations which correspond to our current branch
\* OnlyEnqueueCurrentBranchHeaders ==
\*     \A hd \in ToSet(header_pipe) : descendant(hd, current_head)

\* TODO only prevalidated headers and operations in the respective pipe

Safety ==
    /\ TypeOK
    /\ ConnectionSafety
    /\ CurrentHeadIsAlwaysMajor
    /\ HeadDoesNotChangeWithoutMajoritySupport

(**************)
(* Properties *)
(**************)

\* Safety properties of transitions

PeerConservation ==
    [][ IF \/ connections /= {}
           \/ greylist /= {}
        THEN connections \cup greylist = connections' \cup greylist'
        ELSE connections \cup greylist \subseteq connections' \cup greylist' ]_vars

\* fitness always increases
MonotonicFitness ==
    LET old_head  == current_head
        new_head  == current_head'
    IN
    [][ old_head /= new_head => old_head.fitness < new_head.fitness ]_vars

\* Liveness

\* Bootstrapping nodes always learn about local major branches
IfLocalMajorBranchExistsThenBootstrapppingWillHearAboutIt ==
    LET curr_hd == current_head IN
    \E hd \in major_headers :
        <>( \/ hd = curr_hd
            \/ hd.fitness < curr_hd.fitness )

\* \* Every good bootstrapping node eventually enters the search phase
\* EventuallySearch == <>(phase \in Phase_search)

\* \* Every good bootstrapping node eventually greylists a majority of their peers or enters the major phase
\* EventuallyMajor ==
\*     <>( \/ 2 * Card(greylist) >= num_peers
\*         \/ phase \in Phase_major )

\* \* Every good bootstrapping node eventually greylists a majority of their peers or enters the apply phase
\* EventuallyApply ==
\*     <>( \/ 2 * Card(greylist) >= num_peers
\*         \/ phase \in Phase_apply )

Liveness ==
    \* /\ EventuallySearch
    \* /\ EventuallyMajor
    \* /\ EventuallyApply
    /\ IfLocalMajorBranchExistsThenBootstrapppingWillHearAboutIt

==========================
