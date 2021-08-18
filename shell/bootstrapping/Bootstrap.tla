---- MODULE Bootstrap ----

EXTENDS FiniteSets, Naturals, Sequences, TLC, Hash, Samples

CONSTANTS
    BAD_NODES,          \* nodes who behave arbitrarily
    GOOD_NODES,         \* nodes who follow the protocol
    BAD_BOOTSTRAPPING,  \* bootstrapping nodes who behave arbitrarily
    GOOD_BOOTSTRAPPING, \* bootstrapping nodes who follow the protocol
    MIN_PEERS,          \* minimum number of peers
    MAX_PEERS,          \* maximum number of peers
    MAX_LEVEL,          \* maximum level of a block
    MAX_OPS,            \* maximum number of operations per block
    CURRENT_HEAD,       \* each good node's current head
    BLOCKS,             \* each good node's blocks
    VALIDATOR           \* each block's validity status

VARIABLES
    b_blacklist,        \* each good bootstrapping node's set of blacklisted peers
    b_messages,         \* each good bootstrapping node's set of messages
    n_blacklist,        \* each good node's set of blacklisted peers
    n_messages          \* each good node's set of messages

messages  == <<b_messages, n_messages>>
blacklist == <<b_blacklist, n_blacklist>>

\* bootstrapping variables
VARIABLES
    phase,              \* each good bootstrapping node's phase
    connections,        \* each good and bad bootstrapping node's set of connections
    current_head,       \* each good bootstrapping node's current head
    fittest_head,       \* each good bootstrapping node's peer's current heads
    header_pipe,        \* each good bootstrapping node's queue of fetched headers
    operation_pipe,     \* each good bootstrapping node's queue of fetched operations
    validated_blocks,   \* each good bootstrapping node's set of validated blocks
    prevalidated_hds,   \* each good bootstrapping node's set of prevalidated headers
    prevalidated_ops,   \* each good bootstrapping node's set of prevalidated operations
    sent_get_branch,    \* each good bootstrapping node's set of peers to whom they have sent a Get_current_branch message
    sent_get_headers,   \* each good bootstrapping node's function from peers to whom they have sent a Get_block_headers message to the requested headers
    sent_get_ops,       \* each good bootstrapping node's function from peers to whom they have sent a Get_operations message to the requested operations
    recv_branch,        \* each good bootstrapping node's set of peers from whom they have received a Current_branch message
    recv_header,        \* each good bootstrapping node's function from peers from whom they have received a Block_header message to set of headers received
    recv_operation      \* each good bootstrapping node's function from peers from whom they have received a Operation message to set of operations received

\* trace variables
VARIABLES
    phase_trace         \* each good bootstrapping node's phase trace

\* memory variables
VARIABLES
    mem_size            \* each good bootstrapping node's estimated memory usage

\* inclusive bootstrapping variables
pipe_vars   == <<validated_blocks, header_pipe, operation_pipe>>
b_sent_vars == <<sent_get_branch, sent_get_headers, sent_get_ops>>
b_recv_vars == <<recv_branch, recv_header, recv_operation>>
valid_vars  == <<prevalidated_hds, prevalidated_ops>>
trace_vars  == <<phase_trace>>
mem_vars    == <<mem_size>>

\* exclusive bootstrapping variables
b_non_conn_vars   == <<current_head, pipe_vars, valid_vars, b_sent_vars, b_recv_vars, trace_vars, mem_vars>>
b_non_branch_vars == <<phase, connections, current_head, pipe_vars, valid_vars, sent_get_headers, sent_get_ops, recv_header, recv_operation, trace_vars, mem_vars>>
b_non_header_vars == <<phase, connections, current_head, pipe_vars, valid_vars, sent_get_branch, sent_get_ops, recv_branch, recv_operation, trace_vars, mem_vars>>
b_non_op_vars     == <<phase, connections, current_head, pipe_vars, valid_vars, sent_get_branch, sent_get_headers, recv_branch, recv_header, trace_vars, mem_vars>>
b_non_pipe_vars   == <<phase, connections, current_head, valid_vars, b_sent_vars, b_recv_vars, trace_vars, mem_vars>>
b_non_recv_vars   == <<phase, connections, current_head, pipe_vars, valid_vars, b_sent_vars, trace_vars, mem_vars>>
b_non_node_vars   == <<phase, connections, current_head, pipe_vars, valid_vars, b_sent_vars, b_recv_vars, trace_vars, mem_vars>>
b_non_trace_vars  == <<connections, pipe_vars, valid_vars, b_sent_vars, b_recv_vars, mem_vars>>
b_non_hd_q_vars   == <<phase, connections, current_head, validated_blocks, operation_pipe, prevalidated_ops, b_sent_vars, b_recv_vars, trace_vars, mem_vars>>
b_non_op_q_vars   == <<phase, connections, current_head, validated_blocks, header_pipe, prevalidated_hds, b_sent_vars, b_recv_vars, trace_vars, mem_vars>>

\* all bootstrapping variables
bootstrapping_vars == <<phase, connections, current_head, fittest_head, pipe_vars, valid_vars, b_sent_vars, b_recv_vars, trace_vars, mem_vars>>

\* node variables
VARIABLES
    sent_branch,        \* each good node's set of peers to whom they have sent a Current_branch message
    sent_headers,       \* each good node's function from peers to whom they have sent a Block_header message to the set of headers sent
    sent_ops,           \* each good node's function from peers to whom they have sent a Operation message to the set of operations sent
    recv_get_branch,    \* each good node's set of peers from whom they have received a Get_current_branch message
    recv_get_headers,   \* each good node's set of peers from whom they have received a Get_block_headers message
    recv_get_ops,       \* each good node's set of peers from whom they have received a Get_operations message
    serving_headers,    \* each good node's function from peers from whom they have received a Get_block_headers message to the header hashes they requested
    serving_ops         \* each good node's function from peers from whom they have received a Get_operations message to the operation hashes they requested

\* inclusive node variables
n_sent_vars  == <<sent_branch, sent_headers, sent_ops>>
n_recv_vars  == <<recv_get_branch, recv_get_headers, recv_get_ops>>
serving_vars == <<serving_headers, serving_ops>>

\* exclusive node variables
n_non_branch_vars  == <<sent_headers, sent_ops, recv_get_headers, recv_get_ops, serving_vars>>
n_non_head_vars    == <<sent_branch, sent_headers, sent_ops, recv_get_branch, recv_get_headers, recv_get_ops, serving_vars>>
n_non_header_vars  == <<sent_branch, sent_ops, recv_get_branch, recv_get_ops, serving_vars>>
n_non_op_vars      == <<sent_branch, sent_headers, recv_get_branch, recv_get_headers, serving_vars>>
n_non_serving_vars == <<sent_branch, sent_headers, sent_ops, recv_get_branch, recv_get_headers, recv_get_ops>>

\* all node variables
node_vars == <<n_sent_vars, n_recv_vars, serving_vars>>

non_phase_vars == <<messages, blacklist, node_vars, b_non_trace_vars>>

\* all variables
vars == <<messages, blacklist, bootstrapping_vars, node_vars>>

----

(***********)
(* Helpers *)
(***********)

\* [1] General helpers

Card(s) == Cardinality(s)

Set_n(s) == { ss \in SUBSET s : Card(ss) <= MAX_LEVEL }

Set_hd(s) == { ss \in SUBSET s : Card(ss) <= MAX_LEVEL \div 2 }

Set_op(s) == { ss \in SUBSET s : Card(ss) <= MAX_OPS }

NESet_hd(s) == Set_hd(s) \ {{}}

NESet_op(s) == Set_op(s) \ {{}}

BSeq(s, n) == { seq \in Seq(s) : Len(s) <= n }

Seq_n(s) == BSeq(s, MAX_LEVEL)

Seq_hd(s) == { seq \in Seq(s) : Len(s) <= MAX_LEVEL \div 2 }

NESeq_n(s) == Seq_n(s) \ {<<>>}

NESeq_hd(s) == Seq_hd(s) \ {<<>>}

Pick(s) == CHOOSE x \in s : TRUE

Cons(x, seq) == <<x>> \o seq

RECURSIVE map(_, _, _)
map(f(_), seq, acc) ==
    IF seq = <<>> THEN acc
    ELSE
        LET x == Head(seq) IN
        map(f, Tail(seq), Append(acc, f(x)))

Map(f(_), seq) == map(f, seq, <<>>)

RECURSIVE map_set(_, _, _)
map_set(f(_), s, acc) ==
    IF s = {} THEN acc
    ELSE
        LET x == Pick(s) IN
        map_set(f, s \ {x}, acc \cup { f(x) })

Map_set(f(_), s) == map_set(f, s, {})

ToSet(seq) == { seq[i] : i \in DOMAIN seq }

RECURSIVE seq_of_set(_, _)
seq_of_set(s, acc) ==
    IF s = {} THEN acc
    ELSE
        LET x == Pick(s)
            t == s \ {x}
        IN seq_of_set(t, Append(acc, x))

SetToSeq(s) == seq_of_set(s, <<>>)

RECURSIVE index(_, _, _)
index(x, seq, i) ==
    IF seq = <<>> THEN 0
    ELSE
        IF x = Head(seq) THEN i + 1
        ELSE index(x, Tail(seq), i + 1)

Index(x, seq) == index(x, seq, 0)

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

Nodes == BAD_NODES \cup GOOD_NODES

Bootstrapping_nodes == BAD_BOOTSTRAPPING \cup GOOD_BOOTSTRAPPING

N == Card(Nodes)

\* sets of connections
ConnectionSets == { ps \in SUBSET Nodes : Card(ps) >= MIN_PEERS /\ Card(ps) <= MAX_PEERS }

\* block levels
Levels  == 1..MAX_LEVEL
Levels0 == Levels \cup {0}

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

Max_number  == N * MAX_LEVEL

\* fitness
Max_fitness == Max_number

\* hash types
PossibleHashes   == 0..Max_number
PossibleOpHashes == 0..(N * MAX_LEVEL * MAX_OPS)
PossibleHeaders  == [
    level       : Levels0,
    context     : PossibleHashes,
    fitness     : 0..Max_fitness,
    predecessor : PossibleHashes,
    ops_hash    : PossibleHashes
]

Ops == 0..MAX_OPS

header(l, pred, ctx, fit, op) ==
    [ level |-> l, predecessor |-> pred, context |-> ctx, fitness |-> fit, ops_hash |-> op ]

operation(bh, op) == [ block_hash |-> bh, op |-> op ]

operations(bh, ops) == [ block_hash : {bh}, op : ops ]

block(hdr, ops) == [ header |-> hdr, ops |-> ops ]

hash(hd) == Hash(hd)

gen_header == header(0, 0, hash({}), 0, hash({}))
gen_operations == operations(hash(gen_header), {})
genesis == block(gen_header, gen_operations)

\* headers

headers_at_level[ l \in Levels0 ] ==
    IF l > 0 THEN
        LET prev_hashes == { hash(hd) : hd \in headers_at_level[l - 1] } IN
        [
            level       : {l},
            context     : PossibleHashes,
            fitness     : 0..Max_fitness,
            predecessor : prev_hashes,
            ops_hash    : PossibleOpHashes
        ]
    ELSE { gen_header }

Headers == UNION { headers_at_level[l] : l \in Levels0 }

hashes_at_level[ l \in Levels0 ] ==
    IF l = 0 THEN {0}
    ELSE { hash(hd) : hd \in headers_at_level[l] }

BlockHashes == UNION { hashes_at_level[l] : l \in Levels0 }

\* operations

operations_at_level[ l \in Levels0 ] ==
    IF l > 0 THEN [ block_hash : hashes_at_level[l], op : Ops ]
    ELSE gen_operations

Operations == UNION { operations_at_level[l] : l \in Levels0 }

Fitness[ n \in GOOD_NODES, l \in Levels0 ] ==
    IF l \notin DOMAIN BLOCKS[n] THEN {0}
    ELSE
        LET min == Max_set({ b.fitness : b \in { bb \in BLOCKS[n] : bb.header.level = l } }) IN
        min..Max_fitness

\* blocks

blocks_at_level[ l \in Levels0 ] ==
    IF l = 0 THEN {genesis}
    ELSE
        LET bs == { block(hd, ops) : hd \in headers_at_level[l], ops \in SUBSET operations_at_level[l] }
            ops_block_hashes(b) == { op.block_hash : op \in b.ops }
        IN
        { b \in bs : hash(b.header) \in ops_block_hashes(b) }

Blocks == UNION { blocks_at_level[l] : l \in Levels0 }

AllBlocks == [ headers : PossibleHeaders, ops : Operations ]

History == Seq_hd(Levels \X BlockHashes)

Locators == [ current_head : Headers, history : History ]

\* operation hash

op_hash[ op \in Operations ] == <<op.block_hash, op.op>>

OperationHashes == { op_hash[op] : op \in Operations }

\* all bootstrapping nodes have connections
All_bootstrapping_initialized == \A bn \in Bootstrapping_nodes : phase[bn] /= init_phase

received_operations_block_hash(bn, n, bh) == { op \in recv_operation[bn][n] : op.block_hash = bh }

all_recv_operations_block_hash(bn, bh) == UNION { received_operations_block_hash(bn, n, bh) : n \in Nodes }

\* all fetched data
fetched_hashes_node(bn, n)  == { p[1] : p \in recv_header[bn][n] }
fetched_headers_node(bn, n) == { p[2] : p \in recv_header[bn][n] }

all_header_data(bn)    == UNION { recv_header[bn][n] : n \in Nodes }
fetched_hashes(bn)     == UNION { fetched_hashes_node(bn, n) : n \in Nodes }
fetched_headers(bn)    == UNION { fetched_headers_node(bn, n) : n \in Nodes }
fetched_operations(bn) == UNION { recv_operation[bn][n] : n \in Nodes }

validated_headers(bn)    == { b.header : b \in validated_blocks[bn] }
validated_operations(bn) == UNION { b.ops    : b \in validated_blocks[bn] }

remaining_headers(bn)      == fetched_headers(bn) \ (ToSet(header_pipe[bn]) \cup validated_headers(bn))
remaining_operations(bn)   == fetched_operations(bn) \ (ToSet(operation_pipe[bn]) \cup validated_operations(bn))
rem_ops_block_hash(bn, bh) == { op \in remaining_operations(bn) : op.block_hash = bh }

fetched_ops_block_hash(bn, bh)     == { op \in fetched_operations(bn) : op.block_hash = bh }
num_fetched_ops_block_hash(bn, bh) == Card(fetched_ops_block_hash(bn, bh))

\* node data

node_headers(n) == { b.header : b \in BLOCKS[n] }

node_hashes(n) == { hash(hd) : hd \in node_headers(n) }

node_operations(n) == { b.operation : b \in BLOCKS[n] }

node_op_hashes(n) == { op_hash[op] : op \in node_operations(n) }

chain_levels(bn, n) == fittest_head[bn][n].level

num_peers(bn) == Card(connections[bn] \cup b_blacklist[bn])

peers_at_level(bn, l) == { n \in Nodes : chain_levels(bn, n) = l }

peers_at_or_above_level(bn, l) == { n \in Nodes : chain_levels(bn, n) >= l }

highest_major_level(bn) ==
    LET major_levels == { l \in Levels :
        \* #(peers of [bn] at or above level [l]) / #peers > 1/2
        (2 * Card(peers_at_or_above_level(bn, l))) > num_peers(bn)
    } IN
    IF major_levels = {} THEN 0
    ELSE Max_set(major_levels)

recv_hashes[ bn \in GOOD_BOOTSTRAPPING, n \in Nodes ] ==
    LET fit_hash == { hash(fittest_head[bn][n]) }
        br_hs    == ToSet(recv_branch[bn][n])
        bh_hs    == { hash(hd) : hd \in fetched_headers(bn) }
    IN
    fit_hash \cup br_hs \cup bh_hs

all_recv_hashes(bn) == UNION { recv_hashes[bn, n] : n \in Nodes }

major_hashes(bn) == { fh \in all_recv_hashes(bn) :
    \* majority of peers agree with [fh]
    LET seen_agreeing == { n \in Nodes : fh \in recv_branch[bn][n] } IN
    (2 * Card(seen_agreeing)) > num_peers(bn) }

has_major_hashes(bn) == major_hashes(bn) /= {}

major_headers(bn) == { hd \in fetched_headers(bn) :
    \* majority of peers agree with [hd]
    LET seen_agreeing == { n \in Nodes : hd \in recv_header[bn][n] } IN
    (2 * Card(seen_agreeing)) > num_peers(bn) }

hash_bound == Card(BlockHashes)

HashPairs == LET Hs == 0..hash_bound IN Hs \X Hs

Hashes == 0..Card(HashPairs)

headers_with_hash(bn, bh) == { p \in all_header_data(bn) : p[1] = bh }

lookup_block_hash(bn, bh) == Pick(headers_with_hash(bn, bh))

RECURSIVE descendant(_, _, _)
descendant(bn, hd1, hd2) ==
    CASE hd1.fitness = hd2.fitness -> hd1 = hd2
      [] hd1.fitness < hd2.fitness ->
        LET bh == hash(hd2) IN
        \/ bh = hd1.predecessor
        \/ \E hd \in headers_with_hash(bn, bh): descendant(bn, hd, hd2)

prevalidate_header(bn, hd) ==
    LET pvhds == prevalidated_hds[bn] IN
    pvhds /= {} =>
        LET max_hd == Max_level_set(pvhds)
            hl     == hd.level
            ml     == max_hd.level
        IN
        IF ml = hl THEN hd = max_hd
        ELSE descendant(bn, hd, max_hd)

----

(***************)
(* Assumptions *)
(***************)

\* \* [0] Node assumptions
\* \* different sets of nodes are disjoint
\* ASSUME
\*     /\ BAD_NODES \cap GOOD_NODES = {}
\*     /\ BAD_BOOTSTRAPPING \cap GOOD_BOOTSTRAPPING = {}
\*     /\ Bootstrapping_nodes \cap Nodes = {}

\* \* [1] Peer assumptions
\* ASSUME MIN_PEERS > 0 /\ MAX_PEERS >= MIN_PEERS

\* \* [2] Block assumptions
\* \* blocks are contiguous and hash-linked
\* ASSUME
\*     \A n \in GOOD_NODES :
\*         /\ \A b \in BLOCKS[n] : \E pb \in BLOCKS[n] \ {b}, l \in Levels :
\*             /\ pb.header.level = l - 1
\*             /\ hash(pb.header) = b.header.predecessor
\*         /\ genesis = Pick({ b \in BLOCKS[n] : b.header.level = 0 })

\* \* Structure assumptions
\* ASSUME CURRENT_HEAD \in [ GOOD_NODES -> Headers ]
\* ASSUME BLOCKS \in [ GOOD_NODES -> SUBSET Blocks ]
\* ASSUME \E bs \in SUBSET Blocks : VALIDATOR \in [ bs -> { "known_valid", "known_invalid", "unknown" } ]
\* ASSUME \A b \in DOMAIN VALIDATOR : \E n \in GOOD_NODES : b \in BLOCKS[n] => VALIDATOR[b] = "known_valid"

----

(************)
(* Messages *)
(************)

\* [1] Requests
\* [1.1] Good requests
GetCurrentBranchMessages == [ type : {"Get_current_branch"}, from : GOOD_BOOTSTRAPPING ]
GetBlockHeadersMessages  == [ type : {"Get_block_headers"},  from : GOOD_BOOTSTRAPPING, hashes : NESet_hd(Levels \X BlockHashes) ]
GetOperationsMessages    == [ type : {"Get_operations"},     from : GOOD_BOOTSTRAPPING, op_hashes : NESet_op(OperationHashes) ]
GoodGetMessages          == GetCurrentBranchMessages \cup GetBlockHeadersMessages \cup GetOperationsMessages

\* [1.2] Bad requests
BadGetMessages ==
    LET BadGetCurrentBranch == [ type : {"Get_current_branch"}, from : BAD_BOOTSTRAPPING ]
        BadGetBlockHeaders  == [ type : {"Get_block_headers"},  from : BAD_BOOTSTRAPPING, hashes    : NESet_hd(BlockHashes) ]
        BadGetOperations    == [ type : {"Get_operations"},     from : BAD_BOOTSTRAPPING, op_hashes : NESet_op(OperationHashes) ]
        Bad                 == [ type : {"bad"},                from : BAD_BOOTSTRAPPING ]
    IN BadGetCurrentBranch \cup BadGetBlockHeaders \cup BadGetOperations \cup Bad

\* [1.3] All requests
GetMessages == GoodGetMessages \cup BadGetMessages

\* [1.4] Request constructors
get_current_branch_msg(bn)    == [ type |-> "Get_current_branch", from |-> bn ]
get_block_headers_msg(bn, hs) == [ type |-> "Get_block_headers",  from |-> bn, hashes    |-> hs ]
get_operations_msg(bn, ohs)   == [ type |-> "Get_operations",     from |-> bn, op_hashes |-> ohs ]

\* [1.5] Sets of request types
current_branch_msgs(bn) == { msg \in b_messages[bn] : msg.type = "Current_branch" }
block_header_msgs(bn)   == { msg \in b_messages[bn] : msg.type = "Block_header" }
operation_msgs(bn)      == { msg \in b_messages[bn] : msg.type = "Operation" }

\* [1.6] Request predicates
has_requested_branch_from(bn, n)  == n \in sent_get_branch[bn]
has_requested_headers_from(bn, n) == sent_get_headers[bn][n] /= {}
has_requested_ops_from(bn, n)     == sent_get_ops[bn][n] /= {}

requested_branch_from(bn)  == { n \in connections[bn] : has_requested_branch_from(bn, n) }
requested_headers_from(bn) == { n \in connections[bn] : has_requested_headers_from(bn, n) }
requested_ops_from(bn)     == { n \in connections[bn] : has_requested_ops_from(bn, n) }

has_received_branch(bn, n)    == recv_branch[bn][n] /= {}
has_received_header(bn, n)    == recv_header[bn][n] /= {}
has_received_operation(bn, n) == recv_operation[bn][n] /= {}

received_branch_from(bn) == { n \in Nodes : has_received_branch(bn, n) }
received_header_from(bn) == { n \in Nodes : has_received_header(bn, n) }
received_op_from(bn)     == { n \in Nodes : has_received_operation(bn, n) }

\* [2] Responses
\* [2.1] Good responses
CurrentBranchMessages == [ type : {"Current_branch"}, from : GOOD_NODES, locator : Locators ]
BlockHeaderMessages   == [ type : {"Block_header"},   from : GOOD_NODES, header : Headers ]
OperationsMessages    == [ type : {"Operation"},      from : GOOD_NODES, operation : Operations ]
GoodResponseMessages  == CurrentBranchMessages \cup BlockHeaderMessages \cup OperationsMessages

\* [2.2] Bad responses
BadResponseMessages ==
    LET BadCurrentBranch == [ type : {"Current_branch"}, from : BAD_NODES, locator : Locators ]
        BadBlockHeader   == [ type : {"Block_header"},   from : BAD_NODES, header : Headers ]
        BadOperations    == [ type : {"Operation"},      from : BAD_NODES, operation : Operations ]
        Bad              == [ type : {"bad"},            from : BAD_NODES ]
    IN BadCurrentBranch \cup BadBlockHeader \cup BadOperations \cup Bad

\* [2.3] All responses
ResponseMessages == GoodResponseMessages \cup BadResponseMessages

\* [2.4] response constructors
current_branch_msg(n, l) == [ type |-> "Current_branch", from |-> n, locator   |-> l ]
block_header_msg(n, hd)  == [ type |-> "Block_header",   from |-> n, header    |-> hd ]
operation_msg(n, op)     == [ type |-> "Operation",      from |-> n, operation |-> op ]

\* [2.5] sets of message types
get_current_branch_msgs(n) == { msg \in n_messages[n] : msg.type = "Get_current_branch" }
get_block_headers_msgs(n)  == { msg \in n_messages[n] : msg.type = "Get_block_headers" }
get_operations_msgs(n)     == { msg \in n_messages[n] : msg.type = "Get_operations" }

\* [2.6] response predicates
has_sent_branch(n, bn)    == sent_branch[n][bn] /= {}
has_sent_header(n, bn)    == sent_headers[n][bn] /= {}
has_sent_operation(n, bn) == sent_ops[n][bn] /= {}

sent_branch_to(n)    == { bn \in Bootstrapping_nodes : has_sent_branch(n, bn) }
sent_header_to(n)    == { bn \in Bootstrapping_nodes : has_sent_header(n, bn) }
sent_operation_to(n) == { bn \in Bootstrapping_nodes : has_sent_operation(n, bn) }

has_received_get_branch(n, bn)  == bn \in recv_get_branch[n]
has_received_get_headers(n, bn) == recv_get_headers[n][bn] /= {}
has_received_get_ops(n, bn)     == recv_get_ops[n][bn] /= {}

received_get_branch_from(n)  == { bn \in Bootstrapping_nodes : has_received_get_branch(n, bn) }
received_get_headers_from(n) == { bn \in Bootstrapping_nodes : has_received_get_headers(n, bn) }
received_get_ops_from(n)     == { bn \in Bootstrapping_nodes : has_received_get_ops(n, bn) }

\* [3] All messages
Messages             == GetMessages \cup ResponseMessages
AllBranchMessages    == { msg \in Messages : msg.type = "Current_branch" }
AllHeaderMessages    == { msg \in Messages : msg.type = "Block_header" }
AllOperationMessages == { msg \in Messages : msg.type = "Operation" }

----

(***********)
(* Actions *)
(***********)

\* [0] Action helpers

Send_n(n, msg) == n_messages' = [ n_messages EXCEPT ![n] = @ \cup {msg} ]
Send_b(b, msg) == b_messages' = [ b_messages EXCEPT ![b] = @ \cup {msg} ]
Drop_n(n, msg) == n_messages' = [ n_messages EXCEPT ![n] = @ \ {msg} ]
Drop_b(b, msg) == b_messages' = [ b_messages EXCEPT ![b] = @ \ {msg} ]

\* [1] Request actions <- good bootstrapping nodes

SendGetCurrentBranch == \E bn \in GOOD_BOOTSTRAPPING :
    \E n \in connections[bn] :
        /\ All_bootstrapping_initialized
        /\ phase[bn] \in Phase_search
        /\ bn \notin n_blacklist[n]
        /\ has_requested_branch_from(bn, n)
        /\ Send_n(n, get_current_branch_msg(bn))
        /\ sent_get_branch' = [ sent_get_branch EXCEPT ![bn] = @ \cup {n} ]
        /\ UNCHANGED <<b_messages, blacklist, node_vars, b_non_branch_vars, recv_branch>>

SendGetBlockHeaders == \E bn \in GOOD_BOOTSTRAPPING :
    \E n \in connections[bn], bhs \in NESet_hd(fetched_hashes(bn)) :
        /\ phase[bn] \in Phase_search \cup Phase_major
        /\ bn \notin n_blacklist[n]
        /\ Send_n(n, get_block_headers_msg(bn, bhs))
        /\ sent_get_headers' = [ sent_get_headers EXCEPT ![bn][n] = @ \cup bhs ]
        /\ UNCHANGED <<b_messages, blacklist, node_vars, b_non_header_vars, recv_header>>

SendGetOperations == \E bn \in GOOD_BOOTSTRAPPING :
    \E n \in connections[bn], hd \in fetched_headers(bn) :
        LET bh  == hash(hd)
            ops == operations(bh, 1..hd.ops_hash)
            req == ops \ all_recv_operations_block_hash(bn, bh)
            ohs == { <<bh, op_hash[op]>> : op \in req }
        IN
        /\ req /= {}
        /\ phase[bn] \in Phase_major
        /\ bn \notin n_blacklist[n]
        /\ Send_n(n, get_operations_msg(bn, ohs))
        /\ sent_get_ops' = [ sent_get_ops EXCEPT ![bn][n] = @ \cup ohs ]
        /\ UNCHANGED <<b_messages, blacklist, node_vars, b_non_op_vars, recv_operation>>

\* [2] Response actions <- good nodes

HandleGetCurrentBranch == \E n \in GOOD_NODES :
    \E msg \in get_current_branch_msgs(n) :
        LET bn  == msg.from
            hist == Samples(n, bn, Map(hash, BLOCKS[n]))
            curr_branch_msg == current_branch_msg(n, [ current_head |-> CURRENT_HEAD[n], history |-> hist ])
        IN
        /\ Drop_n(n, msg)
        /\ Send_b(bn, curr_branch_msg)
        /\ recv_get_branch' = [ recv_get_branch EXCEPT ![n] = @ \cup {bn} ]
        /\ sent_branch'     = [ sent_branch     EXCEPT ![n][bn] = @ \cup ToSet(hist) ]
        /\ UNCHANGED <<blacklist, bootstrapping_vars, n_non_branch_vars>>

\* Nodes drop block hashes they don't know
HandleGetBlockHeaders == \E n \in GOOD_NODES :
    \E msg \in get_block_headers_msgs(n) :
        LET bn == msg.from
            hs == msg.hashes \cap node_hashes(n)
        IN
        /\ Drop_n(n, msg)
        /\ recv_get_headers' = [ recv_get_headers EXCEPT ![n][bn] = @ \cup hs ]
        /\ serving_headers'  = [ serving_headers  EXCEPT ![n][bn] = @ \cup hs ]
        /\ UNCHANGED <<b_messages, blacklist, bootstrapping_vars, n_non_serving_vars, serving_ops>>

\* Nodes drop operation hashes they don't know
HandleGetOperations == \E n \in GOOD_NODES :
    \E msg \in get_operations_msgs(n) :
        LET bn  == msg.from
            ohs == msg.op_hashes \ node_op_hashes(n)
            bh  == Pick({ oh[1] : oh \in ohs })
        IN
        /\ bh \in node_hashes(n)
        /\ Drop_n(n, msg)
        /\ recv_get_ops' = [ recv_get_ops EXCEPT ![n][bn] = @ \cup ohs ]
        /\ serving_ops'  = [ serving_ops  EXCEPT ![n][bn][bh] = @ \cup { oh[2] : oh \in ohs } ]
        /\ UNCHANGED <<b_messages, blacklist, bootstrapping_vars, n_non_serving_vars, serving_headers>>

\* [3] Bootstrapping nodes handle responses

HandleCurrentBranch == \E bn \in GOOD_BOOTSTRAPPING :
    \E msg \in current_branch_msgs(bn) :
        LET n       == msg.from
            hist    == msg.locator.history
            curr_hd == msg.locator.current_head
        IN
        /\ phase[bn] \in Phase_search \cup Phase_major
        /\ has_requested_branch_from(bn, n)
        /\ Drop_b(bn, msg)
        /\ fittest_head' = [ fittest_head EXCEPT ![bn][n] = IF curr_hd.fitness > @.fitness THEN curr_hd ELSE @ ]
        /\ recv_header'  = [ recv_header  EXCEPT ![bn][n] = @ \cup {curr_hd} ]
        /\ recv_branch'  = [ recv_branch  EXCEPT ![bn][n] = @ \cup ToSet(hist) ]
        /\ UNCHANGED <<n_messages, blacklist, node_vars, connections, current_head, pipe_vars, b_sent_vars, recv_header, recv_operation>>

\* bootstrapping node receives a Block_header message
HandleBlockHeader == \E bn \in GOOD_BOOTSTRAPPING :
    \E msg \in block_header_msgs(bn) :
        LET n  == msg.from
            hd == msg.header
            h  == hash(hd)
        IN
        /\ phase[bn] \in Phase_search \cup Phase_major
        /\ h \in sent_get_headers[bn][n]
        /\ hd \notin fetched_headers(bn)
        /\ Drop_b(bn, msg)
        /\ recv_header' = [ recv_header EXCEPT ![bn][n] = @ \cup {<<h, hd>>} ]
        /\ UNCHANGED <<n_messages, blacklist, node_vars, b_non_recv_vars, recv_branch, recv_operation>>

\* bootstrapping node receives an Operation message
HandleOperation == \E bn \in GOOD_BOOTSTRAPPING :
    \E msg \in operation_msgs(bn) :
        LET n  == msg.from
            op == msg.operation
            bh == op.block_hash
        IN
        \E hd \in fetched_headers(bn) :
            /\ phase[bn] \in Phase_major
            /\ bh = hash(hd)
            /\ op \notin recv_operation[bn][n]
            /\ Drop_b(bn, msg)
            /\ recv_operation' = [ recv_operation EXCEPT ![bn][n] = @ \cup {op} ]
            /\ UNCHANGED <<n_messages, blacklist, node_vars, b_non_recv_vars, recv_branch, recv_header>>

\* [4] Pipe enqueuing actions

\* move header from fetched_headers to header_pipe
EnqueueHeader == \E bn \in GOOD_BOOTSTRAPPING :
    LET pvhds == prevalidated_hds[bn] IN
    /\ pvhds /= {}
    /\ phase[bn] \in Phase_major
    /\ LET hd == Max_level_set(pvhds) IN
        /\ prevalidated_hds' = [ prevalidated_hds EXCEPT ![bn] = @ \ {hd} ]
        /\ header_pipe'      = [ header_pipe      EXCEPT ![bn] = Cons(hd, @) ]
        /\ UNCHANGED <<messages, blacklist, node_vars, b_non_hd_q_vars>>

\* move operation from fetched_operations to operation_pipe
EnqueueOperations == \E bn \in GOOD_BOOTSTRAPPING :
    LET pvops == prevalidated_ops[bn] IN
    /\ pvops /= {}
    /\ phase[bn] \in Phase_major
    /\ LET max  == Max_set({ op[1] : op \in pvops })
           pair == Pick({ op \in pvops : op[1] = max })
           ops  == pair[2]
       IN
        /\ prevalidated_ops' = [ prevalidated_ops EXCEPT ![bn] = @ \ {pair} ]
        /\ operation_pipe'   = [ operation_pipe   EXCEPT ![bn] = Cons(ops, @) ]
        /\ UNCHANGED <<messages, blacklist, node_vars, b_non_op_q_vars>>

\* [5] Nodes serve bootstrapping nodes' requests

\* good node replies to a header request
ServeHeader == \E n \in GOOD_NODES, bn \in Bootstrapping_nodes :
    LET sh == serving_headers[n][bn] IN
    /\ sh /= {}
    /\ LET h   == Pick(sh)
           hd  == Pick({ hd \in node_headers(n) : hash(hd) = h })
           msg == block_header_msg(n, hd)
       IN
        /\ Send_b(bn, msg)
        /\ sent_headers'    = [ sent_headers    EXCEPT ![n][bn] = @ \cup {hd} ]
        /\ serving_headers' = [ serving_headers EXCEPT ![n][bn] = @ \ {h} ]
        /\ UNCHANGED <<n_messages, blacklist, n_non_serving_vars, serving_ops, bootstrapping_vars>>

\* good node replies to a operation request
ServeOperation == \E n \in GOOD_NODES, bn \in Bootstrapping_nodes, bh \in BlockHashes :
    LET ops == serving_ops[n][bn][bh] IN
    /\ ops /= {}
    /\ LET op  == operation(bh, Pick(ops))
           msg == operation_msg(n, op)
       IN
        /\ Send_b(bn, msg)
        /\ sent_ops'    = [ sent_ops    EXCEPT ![n][bn] = @ \cup {op} ]
        /\ serving_ops' = [ serving_ops EXCEPT ![n][bn][bh] = @ \ {op.op} ]
        /\ UNCHANGED <<n_messages, blacklist, n_non_serving_vars, serving_headers, bootstrapping_vars>>

\* [6] Block validation

\* nodes form blocks from fetched headers and operations that have been enqueued in their respective pipes
apply_block(bn, hd, ops) ==
    LET b == block(hd, ops) IN
    /\ header_pipe'       = [ header_pipe      EXCEPT ![bn] = Tail(@) ]
    /\ operation_pipe'    = [ operation_pipe   EXCEPT ![bn] = Tail(@) ]
    /\ validated_blocks'  = [ validated_blocks EXCEPT ![bn] = @ \cup {b} ]
    /\ UNCHANGED <<messages, blacklist, node_vars, b_non_pipe_vars>>

ApplyBlock == \E bn \in GOOD_BOOTSTRAPPING :
    LET hds == header_pipe[bn]
        ops == operation_pipe[bn]
    IN
    /\ phase[bn] \in Phase_apply
    /\ hds /= <<>>
    /\ ops /= <<>>
    /\ LET hd == Head(hds)
           op == Head(ops)
        IN
        /\ op.block_hash = hash(hd)
        /\ apply_block(bn, hd, ops)

\* [7] undesirable actions

\* [7.1] Byzantine actions

BadBootstrapSendsGoodNodeArbitraryMessage == \E bn \in BAD_BOOTSTRAPPING :
    \E n \in connections[bn], msg \in { m \in BadGetMessages : m.from = bn } :
        /\ Send_n(n, msg)
        /\ UNCHANGED <<b_messages, blacklist, node_vars, bootstrapping_vars>>

BadNodeSendsGoodBootstrapArbitraryMessage == \E n \in BAD_NODES, bn \in GOOD_BOOTSTRAPPING :
    \E msg \in { m \in BadResponseMessages : m.from = n } :
        /\ n \in connections[bn]
        /\ Send_b(bn, msg)
        /\ UNCHANGED <<n_messages, blacklist, node_vars, bootstrapping_vars>>

\* [7.2] Timeout actions

b_blacklist_node(bn, n) ==
    b_blacklist' = [ b_blacklist EXCEPT ![bn] = @ \cup {n} ]

b_filter_msgs_from(bn, n) ==
    b_messages'  = [b_messages EXCEPT ![bn] = { msg \in @ : msg.from /= n } ]

remove_connection(bn, n) ==
    connections' = [ connections EXCEPT ![bn] = @ \ {n} ]

remove_data(bn, n) ==
    /\ recv_branch'    = [ recv_branch    EXCEPT ![bn][n] = {} ]
    /\ recv_header'    = [ recv_header    EXCEPT ![bn][n] = {} ]
    /\ recv_operation' = [ recv_operation EXCEPT ![bn][n] = {} ]

b_blacklist_timeout(bn, n) ==
    /\ b_blacklist_node(bn, n)
    /\ b_filter_msgs_from(bn, n)
    /\ remove_connection(bn, n)
    /\ UNCHANGED <<n_blacklist, n_messages, node_vars, b_non_conn_vars, phase>>

\* timeout => blacklist but keep data
BootstrapTimeout == \E bn \in GOOD_BOOTSTRAPPING :
    /\ phase \in Phases \ Phase_apply
    /\ \/ \E n \in requested_branch_from(bn) :
            /\ ~has_received_branch(bn, n)
            /\ b_blacklist_timeout(bn, n)
       \/ \E n \in requested_headers_from(bn) :
            /\ Card(recv_header[bn][n]) /= Card(sent_get_headers[bn][n])
            /\ b_blacklist_timeout(bn, n)
       \/ \E n \in requested_ops_from(bn) :
            /\ ~has_received_operation(bn, n)
            /\ b_blacklist_timeout(bn, n)

n_blacklist_bootstrap(n, bn) ==
    n_blacklist' = [ n_blacklist EXCEPT ![n] = @ \cup {bn} ]

n_filter_msgs_from(n, bn) ==
    n_messages' = [ n_messages EXCEPT ![bn] = { msg \in @ : msg.from /= bn } ]

n_blacklist_timeout(n, bn) ==
    /\ n_blacklist_bootstrap(n, bn)
    /\ n_filter_msgs_from(n, bn)
    /\ UNCHANGED <<b_blacklist, b_messages, bootstrapping_vars, node_vars>>

NodeTimeout == \E n \in GOOD_NODES :
    \/ \E bn \in Bootstrapping_nodes :
        /\ bn \in recv_get_branch[n]
        /\ sent_branch[n][bn] = {}
        /\ n_blacklist_timeout(n, bn)
    \/ \E bn \in Bootstrapping_nodes :
        /\ recv_get_headers[n][bn] /= {}
        /\ sent_headers[n][bn] = {}
        /\ n_blacklist_timeout(n, bn)
    \/ \E bn \in Bootstrapping_nodes :
        /\ recv_get_ops[n][bn]
        /\ sent_ops[n][bn] = {}
        /\ n_blacklist_timeout(n, bn)

\* [7.3] Blacklist actions

BootstrapBlacklist == \E bn \in GOOD_BOOTSTRAPPING :
    \/ \E n \in connections[bn], msg \in b_messages[bn] :
        LET t == msg.type IN
        /\ n = msg.from
        /\ CASE t = "Current_branch" -> FALSE
             [] t = "Block_header" ->
                LET hd == msg.header IN
                \* send multiple headers at the same level
                \/ \E h \in recv_header[bn][n] : h.level = hd.level
                \* never requested header with that hash
                \/ hash(hd) \notin sent_get_headers[bn][n]
             [] t = "Operation" ->
                LET op == msg.operation
                    h  == op.block_hash
                IN
                \* never requested operation
                \/ h \notin sent_get_ops[bn][n]
                \* invalid operation
                \/ \E hd \in fetched_headers(bn) :
                    /\ hash(hd) = h
                    /\ hd.ops_hash < op.op
             [] t = "bad" -> TRUE
        /\ b_blacklist_node(bn, n)
    \/ FALSE \* TODO fails cross validation

\* [8] Phase transitions

update_connections(bn, ps) ==
    connections' = [ connections EXCEPT ![bn] = ps ]

update_current_head(bn, hd) ==
    current_head' = [ current_head EXCEPT ![bn] = hd ]

log_transition(bn, p) ==
    phase_trace' = [ phase_trace EXCEPT ![bn] = Cons(p, @) ]

\* [8.1] Init -> Searching
InitToSearch == \E bn \in Bootstrapping_nodes :
    \E ps \in ConnectionSets :
        /\ phase[bn] \in Phase_init
        /\ connections[bn] = {}
        /\ update_connections(bn, ps)
        /\ phase' = [ phase EXCEPT ![bn] = search_phase ]
        /\ UNCHANGED <<blacklist, messages, node_vars, b_non_conn_vars>>

\* [8.2] Searching -> Validating l
\* major brach at level l
SearchToMajor == \E bn \in GOOD_BOOTSTRAPPING :
    \E l \in Levels, hd \in fetched_headers(bn) :
        /\ phase[bn] \in Phase_search
        /\ hd \in major_headers(bn)
        /\ l = highest_major_level(bn)
        /\ current_head[bn].fitness < hd.fitness
        /\ update_current_head(bn, hd)
        /\ log_transition(bn, major_phase(1..l))
        /\ phase' = [ phase EXCEPT ![bn] = major_phase(1..l) ]
        /\ UNCHANGED non_phase_vars

\* [8.3] Validating l -> Apply l
MajorToApply == \E bn \in GOOD_BOOTSTRAPPING :
    \E l \in Levels :
        /\ phase[bn] \in Phase_major
        /\ phase[bn][2] = 1..l
        /\ Card(prevalidated_hds[bn]) = l
        /\ Card(prevalidated_ops[bn]) = l
        /\ log_transition(bn, apply_phase(1..l))
        /\ phase' = [ phase EXCEPT ![bn] = apply_phase(1..l) ]
        /\ UNCHANGED <<non_phase_vars, current_head>>

\* [8.4] Validating l -> Validating k, l <= k
MajorToMajor == \E bn \in GOOD_BOOTSTRAPPING :
    \E new \in fetched_headers(bn), l \in Levels :
        LET k == new.level IN
        /\ new.fitness > current_head[bn].fitness
        /\ phase[bn] \in Phase_major
        /\ phase[bn][2] = 1..l
        /\ update_current_head(bn, new)
        /\ log_transition(bn, major_phase(1..k))
        /\ phase' = [ phase EXCEPT ![bn] = major_phase(1..k) ]
        /\ UNCHANGED non_phase_vars

\* [8.5] Apply -> Search
ApplyToSearch == \E bn \in GOOD_BOOTSTRAPPING :
    /\ phase[bn] \in Phase_apply
    /\ prevalidated_hds[bn] = {}
    /\ prevalidated_ops[bn] = {}
    /\ header_pipe[bn] = <<>>
    /\ operation_pipe[bn] = <<>>
    /\ phase' = [ phase EXCEPT ![bn] = search_phase ]
    /\ log_transition(bn, search_phase)
    /\ UNCHANGED <<non_phase_vars, current_head>>

----

(*********************)
(* Initial predicate *)
(*********************)

MessagesInit ==
    /\ b_messages = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ n_messages = [ n \in GOOD_NODES |-> {} ]

BlacklistInit ==
    /\ b_blacklist = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ n_blacklist = [ n \in GOOD_NODES |-> {} ]

BootstrappingInit ==
    /\ phase              = [ n \in GOOD_BOOTSTRAPPING  |-> init_phase ]
    /\ connections        = [ n \in Bootstrapping_nodes |-> {} ]
    /\ current_head       = [ n \in GOOD_BOOTSTRAPPING  |-> genesis ]
    /\ fittest_head       = [ n \in GOOD_BOOTSTRAPPING  |-> gen_header ]
    /\ header_pipe        = [ n \in GOOD_BOOTSTRAPPING  |-> <<>> ]
    /\ operation_pipe     = [ n \in GOOD_BOOTSTRAPPING  |-> <<>> ]
    /\ validated_blocks   = [ n \in GOOD_BOOTSTRAPPING  |-> {genesis} ]
    /\ prevalidated_hds   = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ prevalidated_ops   = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ sent_get_branch    = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ sent_get_headers   = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ sent_get_ops       = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ recv_branch        = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ recv_header        = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ recv_operation     = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]

NodeInit ==
    /\ serving_headers    = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ serving_ops        = [ p \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ recv_get_branch    = [ n \in GOOD_NODES |-> {} ]
    /\ recv_get_headers   = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ recv_get_ops       = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ sent_branch        = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ sent_headers       = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ sent_ops           = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]

TraceInit == phase_trace  = [ n \in GOOD_BOOTSTRAPPING |-> <<init_phase>> ]

MemInit == mem_size       = [ n \in GOOD_BOOTSTRAPPING |-> 0 ]

Init ==
    /\ NodeInit
    /\ TraceInit
    /\ MemInit
    /\ MessagesInit
    /\ BlacklistInit
    /\ BootstrappingInit

(****************)
(* Next actions *)
(****************)

Next ==
    \* Phase transitions
    \/ InitToSearch
    \/ SearchToMajor
    \/ MajorToApply
    \/ MajorToMajor
    \/ ApplyToSearch

    \* Message passing
    \/ SendGetCurrentBranch
    \/ SendGetBlockHeaders
    \/ SendGetOperations
    \/ HandleGetCurrentBranch
    \/ HandleGetBlockHeaders
    \/ HandleGetOperations
    \/ HandleCurrentBranch
    \/ HandleBlockHeader
    \/ HandleOperation

    \* Pipe maintanence
    \/ EnqueueHeader
    \/ EnqueueOperations
    \/ ApplyBlock

    \*  Request service
    \/ ServeHeader
    \/ ServeOperation

    \* Timeouts
    \/ BootstrapTimeout
    \/ NodeTimeout

    \* Blacklist actions
    \/ BootstrapBlacklist

    \* Byzantine actions
    \/ BadBootstrapSendsGoodNodeArbitraryMessage
    \/ BadNodeSendsGoodBootstrapArbitraryMessage

(*****************)
(* Specification *)
(*****************)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----

(**************)
(* Invariants *)
(**************)

\* [1] TypeOK - type safety

BlacklistOK ==
    /\ b_blacklist \in [ GOOD_BOOTSTRAPPING -> SUBSET Nodes ]
    /\ n_blacklist \in [ GOOD_NODES -> SUBSET Bootstrapping_nodes ]

MessagesOK ==
    /\ b_messages \in [ GOOD_BOOTSTRAPPING -> SUBSET ResponseMessages ]
    /\ n_messages \in [ GOOD_NODES -> SUBSET GetMessages ]

BootstrappingOK ==
    /\ phase             \in [ GOOD_BOOTSTRAPPING  -> Phases ]
    /\ connections       \in [ Bootstrapping_nodes -> SUBSET Nodes ]
    /\ current_head      \in [ GOOD_BOOTSTRAPPING  -> Blocks ]
    /\ fittest_head      \in [ GOOD_BOOTSTRAPPING  -> [ Nodes -> Headers ] ]
    /\ validated_blocks  \in [ GOOD_BOOTSTRAPPING  -> SUBSET Blocks ]
    /\ header_pipe       \in [ GOOD_BOOTSTRAPPING  -> Seq(Headers) ]
    /\ operation_pipe    \in [ GOOD_BOOTSTRAPPING  -> Seq(SUBSET Operations) ]
    /\ prevalidated_hds  \in [ GOOD_BOOTSTRAPPING  -> SUBSET Headers ]
    /\ prevalidated_ops  \in [ GOOD_BOOTSTRAPPING  -> SUBSET (Levels \X SUBSET Operations) ]
    /\ sent_get_branch   \in [ GOOD_BOOTSTRAPPING  -> SUBSET Nodes ]
    /\ sent_get_headers  \in [ GOOD_BOOTSTRAPPING  -> [ Nodes -> SUBSET (Levels \X BlockHashes) ] ]
    /\ sent_get_ops      \in [ GOOD_BOOTSTRAPPING  -> [ Nodes -> SUBSET (BlockHashes \X OperationHashes) ] ]
    /\ recv_branch       \in [ GOOD_BOOTSTRAPPING  -> [ Nodes -> SUBSET (Levels \X BlockHashes) ] ]
    /\ recv_header       \in [ GOOD_BOOTSTRAPPING  -> [ Nodes -> SUBSET (BlockHashes \X Headers) ] ]
    /\ recv_operation    \in [ GOOD_BOOTSTRAPPING  -> [ Nodes -> SUBSET (BlockHashes \X SUBSET Operations) ] ]

TraceOK == phase_trace   \in [ GOOD_BOOTSTRAPPING  -> Seq(Phases) ]

MemOK == mem_size        \in [ GOOD_BOOTSTRAPPING  -> Int ]

NodesOK ==
    /\ serving_headers   \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET BlockHashes ] ]
    /\ serving_ops       \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET (BlockHashes \X Ops) ] ]
    /\ sent_branch       \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET (Levels \X BlockHashes) ] ]
    /\ sent_headers      \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET Headers ] ]
    /\ sent_ops          \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET Operations ] ]
    /\ recv_get_branch   \in [ GOOD_NODES -> SUBSET Bootstrapping_nodes ]
    /\ recv_get_headers  \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET (Levels \X BlockHashes) ] ]
    /\ recv_get_ops      \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET OperationHashes ] ]

TypeOK ==
    /\ TraceOK
    /\ MemOK
    /\ NodesOK
    /\ MessagesOK
    /\ BlacklistOK
    /\ BootstrappingOK

\* [2] General safety properties

good_conns(bn)  == connections[bn] \cap GOOD_NODES
good_headers(n) == { b.header : b \in BLOCKS[n] }

ConnectionSafety ==
    /\ \A bn \in GOOD_BOOTSTRAPPING :
        /\ num_peers(bn) <= MAX_PEERS
        /\ b_blacklist[bn] \cap connections[bn] = {}
    /\ \A bn \in GOOD_BOOTSTRAPPING : { msg.from : msg \in b_messages } \subseteq connections[bn]
    \* phase conjectures
    /\ \A bn \in GOOD_BOOTSTRAPPING :
        LET p == phase[bn] IN
        /\ p \notin Phase_init => num_peers(bn) >= MIN_PEERS
        /\ \E l \in Levels :
            p = major_phase(1..l) <=> l = highest_major_level(bn)
        /\ \E l \in Levels :
            p = apply_phase(1..l) <=> l = highest_major_level(bn)

\* A majority of good peers agree with a bootstrapping node's current head
CurrentHeadIsAlwaysMajor == \A bn \in GOOD_BOOTSTRAPPING :
    2 * Card({ n \in good_conns(bn) : current_head[bn] \in good_headers(n) }) > Card(good_conns(bn))

\* Without a major branch, bootstrapping nodes do not change their head
HeadDoesNotChangeWithoutMajoritySupport == \A bn \in GOOD_BOOTSTRAPPING :
    highest_major_level(bn) = 0 => current_head[bn] = gen_header

\* TODO only enqueue headers and operations which correspond to our current branch
OnlyEnqueueCurrentBranchHeaders == \A bn \in GOOD_BOOTSTRAPPING :
    \A hd \in ToSet(header_pipe[bn]) : descendant(bn, hd, current_head[bn])

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
    \A bn \in GOOD_BOOTSTRAPPING :
        [][ IF \/ connections[bn] /= {}
               \/ b_blacklist[bn] /= {}
            THEN connections[bn] \cup b_blacklist[bn] = connections'[bn] \cup b_blacklist'[bn]
            ELSE connections[bn] \cup b_blacklist[bn] \subseteq connections'[bn] \cup b_blacklist'[bn] ]_vars

\* fitness always increases
MonotonicFitness == \A bn \in GOOD_BOOTSTRAPPING :
    LET old_head  == current_head[bn]
        new_head  == current_head'[bn]
    IN
    [][ old_head /= new_head => old_head.fitness < new_head.fitness ]_vars

\* Allowable phase transitions
\* Init -> Search
FromInit == \A bn \in GOOD_BOOTSTRAPPING :
    LET old_phase == phase[bn]
        new_phase == phase'[bn]
    IN
    [][ /\ old_phase \in Phase_init
        /\ old_phase /= new_phase
        =>
        /\ new_phase \in Phase_search
        /\ connections[bn] = {}
        /\ connections'[bn] /= {} ]_vars

\* Search -> Major
FromSearch == \A bn \in GOOD_BOOTSTRAPPING :
    LET old_phase == phase[bn]
        old_head  == current_head[bn]
        new_phase == phase'[bn]
        new_head  == current_head'[bn]
    IN
    [][ /\ old_phase \in Phase_search
        /\ old_phase /= new_phase
        =>
        /\ new_phase \in Phase_major
        /\ old_head.fitness < new_head.fitness
        /\ old_head.level < new_head.level ]_vars

\* Major -> { Major, Apply }
FromMajor == \A bn \in GOOD_BOOTSTRAPPING :
    LET old_phase == phase[bn]
        old_head  == current_head[bn]
        new_phase == phase'[bn]
        new_head  == current_head'[bn]
    IN
    \* Major -> Apply
    /\ [][ (old_phase \in Phase_major) => new_phase \in Phase_major \cup Phase_apply ]_vars
    \* Major -> Major
    /\ [][ \E l \in Levels :
            /\ old_phase = major_phase(1..l)
            /\ old_head.level = l
            /\ new_phase \in Phase_major
            =>
            \E k \in Levels :
                /\ k > l
                /\ new_head.level = k
                /\ new_phase = major_phase(1..k) ]_vars

\* Apply -> Search
FromApply == \A bn \in GOOD_BOOTSTRAPPING :
    LET old_phase == phase[bn]
        old_head  == current_head[bn]
        new_phase == phase'[bn]
        new_head  == current_head'[bn]
    IN
    /\ [][ /\ old_phase \in Phase_apply
           /\ new_phase /= new_phase
           => new_phase \in Phase_search \cup Phase_major ]_vars

AllowableTransitions ==
    /\ FromInit
    /\ FromApply
    /\ FromMajor
    /\ FromSearch

TransitionSafety ==
    /\ PeerConservation
    /\ MonotonicFitness
    /\ AllowableTransitions

\* Liveness

\* Bootstrapping nodes always learn about local major branches
IfLocalMajorBranchExistsThenBootstrapppingWillHearAboutIt == \A bn \in GOOD_BOOTSTRAPPING :
    LET curr_hd == current_head[bn] IN
    \E hd \in major_headers(bn) :
        <>( \/ hd = curr_hd
            \/ hd.fitness < curr_hd.fitness )

\* Every good bootstrapping node eventually enters the search phase
EventuallySearch == \A bn \in GOOD_BOOTSTRAPPING : <>(phase[bn] \in Phase_search)

\* Every good bootstrapping node eventually blacklists a majority of their peers or enters the major phase
EventuallyMajor == \A bn \in GOOD_BOOTSTRAPPING :
    <>( \/ 2 * Card(blacklist[bn]) >= num_peers(bn)
        \/ phase[bn] \in Phase_major )

\* Every good bootstrapping node eventually blacklists a majority of their peers or enters the apply phase
EventuallyApply == \A bn \in GOOD_BOOTSTRAPPING :
    <>( \/ 2 * Card(blacklist[bn]) >= num_peers(bn)
        \/ phase[bn] \in Phase_apply )

Liveness ==
    /\ EventuallySearch
    /\ EventuallyMajor
    /\ EventuallyApply
    /\ IfLocalMajorBranchExistsThenBootstrapppingWillHearAboutIt

==========================
