---- MODULE Bootstrap_pipeline ----

EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS
    \* @typeAlias: NODE = Int;
    \* @type: NODE;
    BAD_NODES,          \* nodes who behave arbitrarily
    \* @type: NODE;
    GOOD_NODES,         \* nodes who follow the protocol
    \* @type: NODE;
    BAD_BOOTSTRAPPING,  \* bootstrapping nodes who behave arbitrarily
    \* @type: NODE;
    GOOD_BOOTSTRAPPING, \* bootstrapping nodes who follow the protocol
    \* @type: Int;
    MIN_PEERS,          \* minimum number of peers
    \* @type: Int;
    MAX_PEERS,          \* maximum number of peers
    \* @typeAlias: LEVEL = Int;
    \* @type: LEVEL;
    MAX_LEVEL,          \* maximum level of a block
    \* @type: Int;
    MAX_OPS,            \* maximum number of operations per block
    \* @typeAlias: HEADER = [ level: Int, pred_hash: Int, branch: Int ];
    \* @type: NODE -> HEADER;
    CURRENT_HEAD,       \* each good node's current head
    \* @typeAlias: BLOCK_HASH = Int;
    \* @typeAlias: OPERATION = [ block_hash: BLOCK_HASH, op: Int ];
    \* @typeAlias: BLOCK = [ header: HEADER, ops: Set(OPERATION) ];
    \* @type: NODE -> Set(BLOCK);
    BLOCKS,             \* each good node's blocks
    \* @type: BLOCK -> Str;
    VALIDATOR,          \* each block's validity status
    \* @type: NODE -> NODE -> Seq(LEVEL);
    SAMPLES             \* GOOD_NODES -> Bootstrapping_nodes -> Seq_hd(Levels)

VARIABLES
    b_blacklist,        \* each good bootstrapping node's set of blacklisted peers
    b_messages,         \* each good bootstrapping node's set of messages
    n_blacklist,        \* each good node's set of blacklisted peers
    n_messages          \* each good node's set of messages

messages  == <<b_messages, n_messages>>
blacklist == <<b_blacklist, n_blacklist>>

\* bootstrapping variables
VARIABLES
    connections,        \* each good and bad bootstrapping node's set of connections
    current_head,       \* each good bootstrapping node's current head
    locator,            \* each good bootstrapping node's function from nodes to the sample history ((level, hash) pairs) they provided
    fetched_headers,    \* each good bootstrapping node's set of fetched headers (fetched from top to bottom)
    fetched_operations, \* each good bootstrapping node's set of fetched operations (fetched from bottom to top)
    level_to_validate,  \* each good bootstrapping node's next level to validate
    validated_blocks,   \* each good bootstrapping node's function from level to validated block at that level
    header_pipe,        \* each good bootstrapping node's queue of fetched headers
    operation_pipe,     \* each good bootstrapping node's queue of fetched operations
    sent_get_branch,    \* each good bootstrapping node's set of peers to whom they have sent a Get_current_branch message
    sent_get_headers,   \* each good bootstrapping node's function from peers to whom they have sent a Get_block_headers message to the requested headers
    sent_get_ops,       \* each good bootstrapping node's function from peers to whom they have sent a Get_operations message to the requested operations
    recv_branch,        \* each good bootstrapping node's set of peers from whom they have received a Current_branch message
    recv_header,        \* each good bootstrapping node's function from peers from whom they have received a Block_header message to set of headers received
    recv_operation      \* each good bootstrapping node's function from peers from whom they have received a Operation message to set of operations received

\* inclusive bootstrapping variables
fetch_vars  == <<fetched_headers, fetched_operations>>
pipe_vars   == <<validated_blocks, header_pipe, operation_pipe, level_to_validate>>
b_sent_vars == <<sent_get_branch, sent_get_headers, sent_get_ops>>
b_recv_vars == <<recv_branch, recv_header, recv_operation>>

\* exclusive bootstrapping variables
b_non_conn_vars       == <<current_head, locator, fetch_vars, pipe_vars, b_sent_vars, b_recv_vars>>
b_non_branch_vars     == <<connections, current_head, locator, fetch_vars, pipe_vars, sent_get_headers, sent_get_ops, recv_header, recv_operation>>
b_non_header_vars     == <<connections, current_head, locator, fetch_vars, pipe_vars, sent_get_branch, sent_get_ops, recv_branch, recv_operation>>
b_non_op_vars         == <<connections, current_head, locator, fetch_vars, pipe_vars, sent_get_branch, sent_get_headers, recv_branch, recv_header>>
b_non_pipe_vars       == <<connections, current_head, locator, fetch_vars, b_sent_vars, b_recv_vars>>
b_non_fetch_vars      == <<connections, current_head, locator, pipe_vars, b_sent_vars, b_recv_vars>>
b_non_fetch_pipe_vars == <<connections, current_head, locator, b_sent_vars, b_recv_vars>>
b_non_fetch_recv_vars == <<connections, current_head, locator, pipe_vars, b_sent_vars>>

\* all bootstrapping variables
bootstrapping_vars == <<connections, current_head, locator, fetch_vars, pipe_vars, b_sent_vars, b_recv_vars>>

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

\* all variables
vars == <<messages, blacklist, bootstrapping_vars, node_vars>>

----

(***********)
(* Helpers *)
(***********)

\* @type: Set(a) => Set(Set(a));
Set_n(s) == { ss \in SUBSET s : Cardinality(ss) <= MAX_LEVEL }

\* @type: Set(a) => Set(Set(a));
Set_hd(s) == { ss \in SUBSET s : Cardinality(ss) <= MAX_LEVEL \div 2 }

\* @type: Set(a) => Set(Set(a));
Set_op(s) == { ss \in SUBSET s : Cardinality(ss) <= MAX_OPS }

\* @type: Set(a) => Set(Set(a));
NESet_hd(s) == Set_hd(s) \ {{}}

\* @type: Set(a) => Set(Set(a));
NESet_op(s) == Set_op(s) \ {{}}

\* @type: Set(a) => Set(Seq(a));
Seq_n(s) == { seq \in Seq(s) : Len(s) <= MAX_LEVEL }

\* @type: Set(a) => Set(Seq(a));
Seq_hd(s) == { seq \in Seq(s) : Len(s) <= MAX_LEVEL \div 2 }

\* @type: Set(a) => Set(Seq(a));
NESeq_n(s) == Seq_n(s) \ {<<>>}

\* @type: Set(a) => Set(Seq(a));
NESeq_hd(s) == Seq_hd(s) \ {<<>>}

\* @type: Set(a) => a;
Pick(s) == CHOOSE x \in s : TRUE

\* @type: (a, Seq(a)) => Seq(a);
Cons(x, seq) == <<x>> \o seq

\* @type: (a => b, Seq(a), Seq(b)) => Seq(b);
RECURSIVE map(_, _, _)
map(f(_), seq, acc) ==
    IF seq = <<>> THEN acc
    ELSE
        LET x == Head(seq) IN
        map(f, Tail(seq), Append(acc, f(x)))

\* @type: (a => b, Seq(a)) => Seq(b);
Map(f(_), seq) == map(f, seq, <<>>)

\* @type: Seq(a) => Set(a);
ToSet(seq) == { seq[i] : i \in DOMAIN seq }

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

\* @type: (a, Seq(a), Int) => Int;
RECURSIVE index(_, _, _)
index(x, seq, i) ==
    IF seq = <<>> THEN 0
    ELSE
        IF x = Head(seq) THEN i + 1
        ELSE index(x, Tail(seq), i + 1)

\* @type: (a, Seq(a)) => Int;
Index(x, seq) == index(x, seq, 0)

\* header level comparison
\* @type: (HEADER, HEADER) => Bool;
min_level_cmp(h1, h2) == h1.level <= h2.level

\* @type: (HEADER, HEADER) => Bool;
max_level_cmp(h1, h2) == min_level_cmp(h2, h1)

\* @type: Seq(HEADER) => HEADER;
Min_level_seq(seq) ==
    CASE seq /= <<>> -> Head(SortSeq(seq, min_level_cmp))

\* @type: Set(HEADER) => HEADER;
Min_level_set(s) == Min_level_seq(SetToSeq(s))

\* @type: Seq(HEADER) => HEADER;
Max_level_seq(seq) ==
    CASE seq /= <<>> -> Head(SortSeq(seq, max_level_cmp))

\* @type: Set(HEADER) => HEADER;
Max_level_set(s) == Max_level_seq(SetToSeq(s))

----

Nodes == BAD_NODES \cup GOOD_NODES

N == Cardinality(Nodes)

Branches == 0..(N - 1)

Bootstrapping_nodes == BAD_BOOTSTRAPPING \cup GOOD_BOOTSTRAPPING

ConnectionSets == { ps \in SUBSET Nodes : Cardinality(ps) >= MIN_PEERS /\ Cardinality(ps) <= MAX_PEERS }

Levels == 1..MAX_LEVEL

Samples == { s \in NESeq_hd(Levels) : \A i \in DOMAIN s \ {1} : s[i - 1] < s[i] }

PartialHeaders == [ level : Levels, branch : Branches, op_num : 0..MAX_OPS ]

BlockHashes == 0..Cardinality(PartialHeaders)

\* @type: (Int, BLOCK_HASH, Int) => HEADER;
header(l, p, b, o) == [ level |-> l, pred_hash |-> p, branch |-> b, op_num |-> o ]

\* @type: NODE => Set(HEADER);
headers(bn) == UNION { recv_header[bn][n] : n \in connections[bn] }

\* @type: (BLOCK_HASH, Int) => OPERATION;
operation(bh, op) == [ block_hash |-> bh, op |-> op ]

\* @type: (BLOCK_HASH, Set(Int)) => Set(OPERATION);
operations(bh, ops) == [ block_hash : {bh}, op : ops ]

\* @type: HEADER;
gen_header == header(0, 0, 0, 0)

\* @type: Set(OPERATION);
gen_operations == operations(0, {})

\* @type: (HEADER, Set(OPERATION)) => BLOCK;
block(hd, ops) == [ header |-> hd, ops |-> ops ]

\* @type: BLOCK;
genesis == block(gen_header, gen_operations)

\* block/header hash
\* @type: HEADER => BLOCK_HASH;
hash(hd) ==
    IF hd = gen_header THEN 0
    ELSE Index([ level |-> hd.level, branch |-> hd.branch, op_num |-> hd.op_num ], SetToSeq(PartialHeaders))

\* headers
\* @type: LEVEL -> Set(HEADER);
headers_at_level[ l \in Levels \cup {0} ] ==
    LET prev_hashes == { hash(hd) : hd \in headers_at_level[l - 1] } IN
    IF l > 0 THEN [ level : {l}, pred_hash : prev_hashes, branch : Branches, op_num : 0..MAX_OPS ]
    ELSE {gen_header}

\* @type: Set(HEADER);
Headers == UNION { headers_at_level[l] : l \in Levels \cup {0} }

\* @type: LEVEL -> Set(BLOCK_HASH);
hashes_at_level[ l \in Levels \cup {0} ] == { hash(hd) : hd \in headers_at_level[l] }

\* operations
\* @type: LEVEL -> Set(OPERATION);
operations_at_level[ l \in Levels \cup {0} ] ==
    IF l > 0 THEN [ block_hash : hashes_at_level[l], operations : 0..MAX_OPS ]
    ELSE {gen_operations}

History == Seq_hd(BlockHashes)

\* @type: Set(OPERATION);
Operations == UNION { operations_at_level[l] : l \in Levels \cup {0} }

\* blocks
\* @type: LEVEL -> Set(BLOCK);
blocks_at_level[ l \in Levels \cup {0} ] ==
    LET bs == { block(hd, ops) : hd \in headers_at_level[l], ops \in SUBSET operations_at_level[l] } IN
    { b \in bs : hash(b.header) = Pick({ op.block_hash : op \in b.ops }) }

\* @type: Set(BLOCK);
Blocks == UNION { blocks_at_level[l] : l \in Levels \cup {0} }

\* @typeAlias: LOCATOR = [ current_head: HEADER, history: Seq(Int) ];
\* @type: Set(LOCATOR);
Locators ==
    LET Heads == UNION { CURRENT_HEAD[n] : n \in Nodes } IN
    [ current_head : Heads, history : History ]

\* @type: BLOCK_HASH -> HEADER;
lookup_block_hash[ h \in BlockHashes ] == Pick({ bh \in Headers : hash(bh) = h })

\* operation hash
\* @typeAlias: OPERATION_HASH = <<BLOCK_HASH, Int>>;
\* @type: OPERATION -> OPERATION_HASH;
op_hash[ op \in Operations ] == <<op.block_hash, op.op>>

\* @type: Set(OPERATION_HASH);
OperationHashes == { op_hash[op] : op \in Operations }

\* @type: NODE => Set(NODE);
sent_get_branch_to(bn) == { n \in Nodes : sent_get_branch[bn][n] /= {} }

\* @type: NODE => Set(NODE);
sent_get_headers_to(bn) == { n \in Nodes : sent_get_headers[bn][n] /= {} }

\* @type: NODE => Set(NODE);
sent_get_ops_to(bn) == { n \in Nodes : sent_ops[bn][n] /= {} }

\* @type: NODE => Set(NODE);
recv_branch_from(bn) == { n \in Nodes : recv_branch[bn][n] /= {} }

\* @type: NODE => Set(NODE);
recv_header_from(bn) == { n \in Nodes : recv_header[bn][n] /= {} }

\* @type: NODE => Set(NODE);
recv_operation_from(bn) == { n \in Nodes : recv_operation[bn][n] /= {} }

\* @type: NODE => Set(BLOCK_HASH);
hashes(bn) == { hash(hd) : hd \in headers(bn) }

\* all bootstrapping nodes have connections
All_bootstrapping_initialized == \A bn \in Bootstrapping_nodes : connections[bn] \in ConnectionSets

\* @type: (NODE, NODE, BLOCK_HASH) => Set(OPERATION);
received_operations_block_hash(bn, n, bh) == { op \in recv_operation[bn][n] : op.block_hash = bh }

\* @type: (NODE, BLOCK_HASH) => Set(OPERATION);
all_recv_operations_block_hash(bn, bh) == UNION { received_operations_block_hash(bn, n, bh) : n \in Nodes }

\* node data
\* @type: NODE => Set(HEADER);
node_headers(n) == { b.header : b \in BLOCKS[n] }

\* @type: NODE => Set(BLOCK_HASH);
node_hashes(n) == { hash(hd) : hd \in node_headers(n) }

\* @type: NODE => Set(OPERATION);
node_operations(n) == { b.operation : b \in BLOCKS[n] }

\* @type: NODE => Set(OPERATION_HASH);
node_op_hashes(n) == { op_hash[op] : op \in node_operations(n) }

----

(***************)
(* Assumptions *)
(***************)

ASSUME
    /\ BAD_NODES \cap GOOD_NODES = {}
    /\ BAD_BOOTSTRAPPING \cap GOOD_BOOTSTRAPPING = {}
    /\ Bootstrapping_nodes \cap Nodes = {}

ASSUME MIN_PEERS > 0
ASSUME MAX_PEERS > MIN_PEERS
ASSUME CURRENT_HEAD \in [ GOOD_NODES -> Headers ]
ASSUME BLOCKS \in [ GOOD_NODES -> SUBSET Blocks ]
ASSUME \A n \in GOOD_NODES : genesis \in BLOCKS[n]
ASSUME
    LET non_gen_blocks(n) == { b \in BLOCKS[n] : b /= genesis } IN
    \A n \in GOOD_NODES : \A b \in non_gen_blocks(n) : \E pb \in BLOCKS[n] \ {b} :
        hash(pb.header) = b.header.pred_hash

ASSUME \E bs \in SUBSET Blocks : VALIDATOR \in [ bs -> { "known_valid", "known_invalid", "unknown" } ]
ASSUME \A b \in DOMAIN VALIDATOR :
        /\ \E n \in GOOD_NODES : b \in BLOCKS[n] => VALIDATOR[b] = "known_valid"
        /\ \A n \in GOOD_NODES : b \notin BLOCKS[n] => VALIDATOR[b] \in { "known_invalid", "unknown" }

----

(************)
(* messages *)
(************)

\* good requests

\* @typeAlias: GET_BRANCH_MSG = [ type: Str, from: NODE, sample: Seq(Int)];
\* @type: Set(GET_BRANCH_MSG);
GetCurrentBranchMessages == [ type : {"Get_current_branch"}, from : GOOD_BOOTSTRAPPING, sample : Seq_hd(Levels) ]

\* @typeAlias: GET_HEADERS_MSG = [ type: Str, from: NODE, hashes: Set(BLOCK_HASH) ];
\* @type: Set(GET_HEADERS_MSG);
GetBlockHeadersMessages == [ type : {"Get_block_headers"}, from : GOOD_BOOTSTRAPPING, hashes : NESet_hd(BlockHashes) ]

\* @typeAlias: GET_OPERATIONS_MSG = [ type: Str, from: NODE, op_hashes: Set(OPERATION_HASH) ];
\* @type: Set(GET_OPERATIONS_MSG);
GetOperationsMessages == [ type : {"Get_operations"}, from : GOOD_BOOTSTRAPPING, op_hashes : NESet_op(OperationHashes) ]

GoodGetMessages == GetCurrentBranchMessages \cup GetBlockHeadersMessages \cup GetOperationsMessages

\* bad requests
BadGetMessages ==
    LET BadGetCurrentBranch == [ type : {"Get_current_branch"}, from : BAD_BOOTSTRAPPING, sample : Seq_hd(Levels) ]
        BadGetBlockHeaders  == [ type : {"Get_block_headers"},  from : BAD_BOOTSTRAPPING, hashes : NESet_hd(BlockHashes) ]
        BadGetOperations    == [ type : {"Get_operations"},     from : BAD_BOOTSTRAPPING, op_hashes : NESet_op(OperationHashes) ]
        Bad                 == [ type : {"bad"},                from : BAD_BOOTSTRAPPING ]
    IN BadGetCurrentBranch \cup BadGetBlockHeaders \cup BadGetOperations \cup Bad

\* all requests
GetMessages == GoodGetMessages \cup BadGetMessages

\* request constructors
get_current_branch_msg(bn, s) == [ type |-> "Get_current_branch", from |-> bn, sample |-> s ]
get_block_headers_msg(bn, hs) == [ type |-> "Get_block_headers",  from |-> bn, hashes |-> hs ]
get_operations_msg(bn, ohs)   == [ type |-> "Get_operations",     from |-> bn, op_hashes |-> ohs ]

\* sets of message types
current_branch_msgs(bn) == { msg \in b_messages[bn] : msg.type = "Current_branch" }
block_header_msgs(bn)   == { msg \in b_messages[bn] : msg.type = "Block_header" }
operation_msgs(bn)      == { msg \in b_messages[bn] : msg.type = "Operation" }

\* request predicates
has_requested_headers(bn, n) == sent_get_headers[bn][n] /= {}
has_requested_ops(bn, n)     == sent_get_ops[bn][n] /= {}

\* good responses
CurrentBranchMessages == [ type : {"Current_branch"}, from : GOOD_NODES, locator : Locators ]
BlockHeaderMessages   == [ type : {"Block_header"},   from : GOOD_NODES, header : Headers ]
OperationsMessages    == [ type : {"Operation"},      from : GOOD_NODES, operation : Operations ]
GoodResponseMessages  == CurrentBranchMessages \cup BlockHeaderMessages \cup OperationsMessages

\* bad responses
BadResponseMessages ==
    LET BadCurrentBranch == [ type : {"Current_branch"}, from : BAD_NODES, locator : Locators ]
        BadBlockHeader   == [ type : {"Block_header"},   from : BAD_NODES, header : Headers ]
        BadOperations    == [ type : {"Operation"},      from : BAD_NODES, operation : Operations ]
        Bad              == [ type : {"bad"},            from : BAD_NODES ]
    IN BadCurrentBranch \cup BadBlockHeader \cup BadOperations \cup Bad

\* all responses
ResponseMessages == GoodResponseMessages \cup BadResponseMessages

\* response constructors
current_branch_msg(n, l) == [ type |-> "Current_branch", from |-> n, locator |-> l ]
block_header_msg(n, hd)  == [ type |-> "Block_header",   from |-> n, header |-> hd ]
operation_msg(n, op)     == [ type |-> "Operation",      from |-> n, operation |-> op ]

\* sets of message types
get_current_branch_msgs(n) == { msg \in n_messages[n] : msg.type = "Get_current_branch" }
get_block_headers_msgs(n)  == { msg \in n_messages[n] : msg.type = "Get_block_headers" }
get_operations_msgs(n)     == { msg \in n_messages[n] : msg.type = "Get_operations" }

\* response predicates
has_sent_header(n, bn)    == sent_headers[n][bn] /= {}
has_sent_operation(n, bn) == sent_ops[n][bn] /= {}

\* all messages
Messages == GetMessages \cup ResponseMessages

AllBranchMessages    == { msg \in Messages : msg.type = "Current_branch" }
AllHeaderMessages    == { msg \in Messages : msg.type = "Block_header" }
AllOperationMessages == { msg \in Messages : msg.type = "Operation" }

----

(***********)
(* Actions *)
(***********)

\* header_timeout
\* operation_timeout
\* other errors?

\* helpers
Send_n(n, msg) == n_messages' = [ n_messages EXCEPT ![n] = @ \cup {msg} ]
Send_b(b, msg) == b_messages' = [ b_messages EXCEPT ![b] = @ \cup {msg} ]
Drop_n(n, msg) == n_messages' = [ n_messages EXCEPT ![n] = @ \ {msg} ]
Drop_b(b, msg) == b_messages' = [ b_messages EXCEPT ![b] = @ \ {msg} ]

\* requests - bootstrapping nodes

SendGetCurrentBranch == \E bn \in GOOD_BOOTSTRAPPING :
    \E n \in connections[bn], s \in Samples :
        /\ All_bootstrapping_initialized
        /\ n \notin sent_get_branch_to(bn)
        /\ Send_n(n, get_current_branch_msg(bn, s))
        /\ sent_get_branch' = [ sent_get_branch EXCEPT ![bn][n] = @ \cup ToSet(s) ]
        /\ UNCHANGED <<b_messages, blacklist, node_vars, b_non_branch_vars, recv_branch>>

SendGetBlockHeaders == \E bn \in GOOD_BOOTSTRAPPING :
    \E n \in connections[bn] :
        LET locs == UNION { {locator[bn][m]} : m \in Nodes } IN
        \E hs \in locs :
            /\ hs /= <<>>
            /\ Send_n(n, get_block_headers_msg(bn, hs))
            /\ sent_get_headers' = [ sent_get_headers EXCEPT ![bn][n] = @ \cup ToSet(hs) ]
            /\ UNCHANGED <<b_messages, blacklist, node_vars, b_non_header_vars, recv_header>>

SendGetOperations == \E bn \in GOOD_BOOTSTRAPPING :
    \E n \in connections[bn], hd \in headers(bn) :
        LET bh    == hash(hd)
            ops   == operations(bh, 1..hd.op_num)
            req   == ops \ all_recv_operations_block_hash(bn, bh)
            op_hs == { op_hash[op] : op \in req }
        IN
        /\ req /= {}
        /\ Send_n(n, get_operations_msg(bn, op_hs))
        /\ sent_get_ops' = [ sent_get_ops EXCEPT ![bn][n] = @ \cup op_hs ]
        /\ UNCHANGED <<b_messages, blacklist, node_vars, b_non_op_vars, recv_operation>>

\* responses - nodes

HandleGetCurrentBranch == \E n \in GOOD_NODES :
    \E msg \in get_current_branch_msgs(n) :
        LET bn == msg.from
            hs == msg.sample
            hash_of_level(l) ==
                LET b == Pick({ bb \in BLOCKS[n] : bb.header.level = l }) IN hash(b.header)
            history == IF hs = <<>> THEN Map(hash_of_level, SAMPLES[n][bn]) ELSE Map(hash_of_level, hs)
            curr_branch_msg == current_branch_msg(n, [ current_head |-> CURRENT_HEAD[n], history |-> history ])
        IN
        /\ Drop_n(n, msg)
        /\ Send_b(bn, curr_branch_msg)
        /\ recv_get_branch' = [ recv_get_branch EXCEPT ![n][bn] = @ \cup ToSet(hs) ]
        /\ sent_branch'     = [ sent_branch     EXCEPT ![n][bn] = @ \cup ToSet(history) ]
        /\ UNCHANGED <<blacklist, bootstrapping_vars, n_non_branch_vars>>

\* TODO how should nodes handle block hashes they don't know?
HandleGetBlockHeaders == \E n \in GOOD_NODES :
    \E msg \in get_block_headers_msgs(n) :
        LET bn == msg.from
            hs == msg.hashes \cap node_hashes(n)
        IN
        /\ Drop_n(n, msg)
        /\ recv_get_headers' = [ recv_get_headers EXCEPT ![n][bn] = @ \cup hs ]
        /\ serving_headers'  = [ serving_headers  EXCEPT ![n][bn] = @ \cup hs ]
        /\ UNCHANGED <<b_messages, blacklist, bootstrapping_vars, n_non_serving_vars, serving_ops>>

\* TODO how should nodes handle operation hashes they don't know?
HandleGetOperations == \E n \in GOOD_NODES :
    \E msg \in get_operations_msgs(n) :
        LET bn  == msg.from
            ohs == msg.op_hashes \ node_op_hashes(n)
            bh  == Pick({ oh[1] : oh \in ohs })
        IN
        /\ bh \in node_hashes(n)
        /\ Drop_n(n, msg)
        /\ recv_get_ops' = [ recv_get_ops EXCEPT ![n][bn] = @ \cup ohs ]
        /\ serving_ops'  = [ serving_ops  EXCEPT ![n, bn][bh] = @ \cup { oh[2] : oh \in ohs } ]
        /\ UNCHANGED <<b_messages, blacklist, bootstrapping_vars, n_non_serving_vars, serving_headers>>

\* bootstrapping nodes handle responses

\* bootstrapping node receives a Current_branch message
\* adjust current_head if the received head is at a higher level
\* UpdateCurrentHead == \E bn \in GOOD_BOOTSTRAPPING :
\*     LET locs == UNION { locator[bn][n] : n \in Nodes } IN
\*     /\ locs /= {}
\*     /\ LET max_hd == Max_level_set({ l.current_head : l \in locs }) IN
\*         CASE current_head[bn].level < max_hd.level ->
\*                 /\ current_head' = [ current_head EXCEPT ![bn] = max_hd ]
\*                 /\ UNCHANGED <<messages, blacklist, connections, locator, fetch_vars, pipe_vars, b_sent_vars, b_recv_vars, node_vars>>
\*           [] /\ current_head[bn].level = max_hd.level
\*              /\ current_head[bn] /= max_hd
\*              -> FALSE \* TODO what to do in this case?
\*           [] OTHER -> FALSE
HandleCurrentBranch == \E bn \in GOOD_BOOTSTRAPPING :
    \E msg \in current_branch_msgs(bn) :
        LET n  == msg.from
            hs == msg.locator.history
            ch == msg.current_head
        IN
        /\ n \in sent_get_branch_to(bn)
        /\ Drop_b(bn, msg)
        /\ current_head' = [ current_head EXCEPT ![bn] = IF ch.level > @.level THEN ch ELSE @ ]
        /\ locator'      = [ locator      EXCEPT ![bn][n] = hs ]
        /\ recv_branch'  = [ recv_branch  EXCEPT ![bn][n] = @ \cup ToSet(hs) ]
        /\ UNCHANGED <<n_messages, blacklist, node_vars, connections, fetch_vars, pipe_vars, b_sent_vars, recv_header, recv_operation>>

\* bootstrapping node receives a Block_header message
HandleBlockHeader == \E bn \in GOOD_BOOTSTRAPPING :
    \E msg \in block_header_msgs(bn) :
        LET n  == msg.from
            hd == msg.header
        IN
        /\ hash(hd) \in sent_get_headers[bn][n]
        /\ hd \notin recv_header[bn][n]
        /\ Drop_b(bn, msg)
        /\ fetched_headers' = [ fetched_headers EXCEPT ![bn, n][hd.level] = @ \cup {hd} ]
        /\ recv_header' = [ recv_header EXCEPT ![bn][n] = @ \cup {hd} ]
        /\ UNCHANGED <<n_messages, blacklist, node_vars, b_non_fetch_vars, fetched_operations, level_to_validate>>

\* bootstrapping node receives an Operation message
HandleOperation == \E bn \in GOOD_BOOTSTRAPPING :
    \E msg \in operation_msgs(bn) :
        LET n  == msg.from
            op == msg.operation
            bh == op.block_hash
        IN
        \E hd \in headers(bn) :
            /\ bh = hash(hd)
            /\ op \notin recv_operation[bn][n]
            /\ Drop_b(bn, msg)
            /\ fetched_operations' = [ fetched_operations EXCEPT ![bn][hd.level] = @ \cup {op} ]
            /\ recv_operation'     = [ recv_operation EXCEPT ![bn][n] = @ \cup {op} ]
            /\ UNCHANGED <<n_messages, blacklist, node_vars, b_non_fetch_recv_vars, fetched_headers, level_to_validate, recv_branch, recv_header>>

\* move header from fetched_headers to header_pipe
EnqueueHeader == \E bn \in GOOD_BOOTSTRAPPING :
    \E n \in connections[bn], l \in Levels :
        LET hd == Min_level_set(fetched_headers[bn, n][l]) IN
        /\ fetched_headers' = [ fetched_headers EXCEPT ![bn, n][l] = @ \ {hd} ]
        /\ header_pipe'     = [ header_pipe     EXCEPT ![bn] = SortSeq(Cons(hd, @), min_level_cmp) ]
        /\ UNCHANGED <<messages, blacklist, node_vars, b_non_fetch_pipe_vars, fetched_operations, level_to_validate, validated_blocks, operation_pipe>>

\* move operation from fetched_operations to operation_pipe
EnqueueOperations == \E bn \in GOOD_BOOTSTRAPPING :
    \E n \in connections[bn], l \in Levels :
        LET fetched_ops == fetched_operations[bn, n][l] IN
        /\ fetched_ops /= {}
        /\ LET bh  == (Pick(fetched_ops)).block_hash
               ops == { op \in fetched_ops : op.block_hash = bh }
           IN
            /\ bh \in { hash(hd) : hd \in ToSet(header_pipe[bn]) }
            /\ fetched_operations' = [ fetched_operations EXCEPT ![bn, n][l] = @ \ ops ]
            /\ operation_pipe' = [ operation_pipe EXCEPT ![bn] =
                    LET block_hash_at_index(i) == Pick({ op.block_hash : op \in @[i] }) IN
                    IF bh \in { block_hash_at_index(i) : i \in DOMAIN @ } THEN
                        LET i == { ii \in DOMAIN @ : bh \in block_hash_at_index(ii) } IN [ @ EXCEPT ![i] = @ \cup ops ]
                    ELSE Cons(ops, @) ]
            /\ UNCHANGED <<messages, blacklist, node_vars, b_non_fetch_pipe_vars, fetched_headers, level_to_validate, validated_blocks, header_pipe, vars>>

\* nodes serve bootstrapping nodes' requests

ServeHeader == \E n \in GOOD_NODES, bn \in Bootstrapping_nodes :
    LET sh == serving_headers[n][bn] IN
    /\ sh /= {}
    /\ LET h   == Pick(sh)
           hd  == lookup_block_hash[h]
           msg == block_header_msg(n, hd)
       IN
        /\ Send_b(bn, msg)
        /\ sent_headers'    = [ sent_headers    EXCEPT ![n][bn] = @ \cup {hd} ]
        /\ serving_headers' = [ serving_headers EXCEPT ![n][bn] = @ \ {h} ]
        /\ UNCHANGED <<n_messages, blacklist, n_non_serving_vars, serving_ops, bootstrapping_vars>>

ServeOperation == \E n \in GOOD_NODES, bn \in Bootstrapping_nodes, bh \in BlockHashes :
    LET ops == serving_ops[n, bn][bh] IN
    /\ ops /= {}
    /\ LET op  == operation(bh, Pick(ops))
           msg == operation_msg(n, op)
       IN
        /\ Send_b(bn, msg)
        /\ sent_ops'    = [ sent_ops    EXCEPT ![n][bn] = @ \cup {op} ]
        /\ serving_ops' = [ serving_ops EXCEPT ![n, bn][bh] = @ \ {op.op} ]
        /\ UNCHANGED <<n_messages, blacklist, n_non_serving_vars, serving_headers, bootstrapping_vars>>

\* nodes form blocks from fetched headers and operations
\* TODO how to handle non-known_valid cases?
validate_block(bn, hd, ops) ==
    LET b == block(hd, ops)
        v == VALIDATOR[b]
    IN
    CASE v = "known_valid" ->
        /\ level_to_validate' = [ level_to_validate EXCEPT ![bn] = @ + 1 ]
        /\ header_pipe'       = [ header_pipe       EXCEPT ![bn] = Tail(@) ]
        /\ operation_pipe'    = [ operation_pipe    EXCEPT ![bn] = Tail(@) ]
        /\ validated_blocks'  = [ validated_blocks  EXCEPT ![bn] = @ \cup {b} ]
        /\ UNCHANGED <<messages, blacklist, b_non_pipe_vars, node_vars>>
      [] v = "known_invalid" -> FALSE
      [] v = "unknown" -> FALSE

ValidateBlock == \E bn \in GOOD_BOOTSTRAPPING :
    \E n \in Nodes :
        LET hds == header_pipe[bn]
            ops == operation_pipe[bn]
        IN
        /\ hds /= <<>>
        /\ ops /= <<>>
        /\ LET hd == Head(hds)
               op == Head(ops)
           IN
            /\ hd.level = level_to_validate[bn]
            /\ op.block_hash = hash(hd)
            /\ validate_block(bn, hd, ops)

\* undesirable actions

BadBootstrapSendsGoodNodeArbitraryMessage == \E bn \in BAD_BOOTSTRAPPING, n \in GOOD_NODES :
    \E msg \in { m \in BadGetMessages : m.from = bn } :
        /\ Send_n(n, msg)
        /\ UNCHANGED <<b_messages, blacklist, node_vars, bootstrapping_vars>>

BadNodeSendsGoodBootstrapArbitraryMessage == \E n \in BAD_NODES, bn \in GOOD_BOOTSTRAPPING :
    \E msg \in { m \in BadResponseMessages : m.from = n } :
        /\ n \in connections[bn]
        /\ Send_b(bn, msg)
        /\ UNCHANGED <<n_messages, blacklist, node_vars, bootstrapping_vars>>

\* TODO
BootstrapTimeout == \E bn \in GOOD_BOOTSTRAPPING :
    \/ \E n \in sent_get_branch[bn] :
        /\ n \notin recv_branch[bn]
        /\ FALSE
    \/ FALSE
\* waiting for branch response
\* waiting for header response
\* waiting for operation response

\* TODO
NodeTimeout == FALSE
\* handling branch request
\* handling headers request
\* handling operations request

BootstrapBlacklist == FALSE
\* TODO

NodeBlacklist == FALSE
\* TODO

\* intialize connections
InitConnections == \E bn \in Bootstrapping_nodes :
    \E ps \in ConnectionSets :
        /\ connections[bn] = {}
        /\ connections' = [ connections EXCEPT ![bn] = ps ]
        /\ UNCHANGED <<blacklist, messages, locator, b_non_conn_vars, node_vars>>

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
    /\ connections        = [ n \in Bootstrapping_nodes |-> {} ]
    /\ current_head       = [ n \in GOOD_BOOTSTRAPPING  |-> genesis ]
    /\ locator            = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> <<>> ] ]
    /\ fetched_headers    = [ p \in GOOD_BOOTSTRAPPING \X Nodes |-> [ l \in Levels |-> {} ] ]
    /\ fetched_operations = [ p \in GOOD_BOOTSTRAPPING \X Nodes |-> [ l \in Levels |-> {} ] ]
    /\ validated_blocks   = [ n \in GOOD_BOOTSTRAPPING  |-> [ l \in Levels |-> {} ] ]
    /\ level_to_validate  = [ n \in GOOD_BOOTSTRAPPING  |-> 1 ]
    /\ header_pipe        = [ n \in GOOD_BOOTSTRAPPING  |-> <<>> ]
    /\ operation_pipe     = [ n \in GOOD_BOOTSTRAPPING  |-> <<>> ]
    /\ sent_get_branch    = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ sent_get_headers   = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ sent_get_ops       = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ recv_branch        = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ recv_header        = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ recv_operation     = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]

NodeInit ==
    /\ recv_get_branch   = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ recv_get_headers  = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ recv_get_ops      = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ sent_branch       = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ sent_headers      = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ sent_ops          = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ serving_headers   = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ serving_ops       = [ p \in GOOD_NODES \X Bootstrapping_nodes |-> [ h \in BlockHashes |-> {} ] ]

Init ==
    /\ NodeInit
    /\ MessagesInit
    /\ BlacklistInit
    /\ BootstrappingInit

(****************)
(* Next actions *)
(****************)

Next ==
    \/ SendGetCurrentBranch
    \/ SendGetBlockHeaders
    \/ SendGetOperations
    \/ HandleGetCurrentBranch
    \/ HandleGetBlockHeaders
    \/ HandleGetOperations
    \/ HandleCurrentBranch
    \/ HandleBlockHeader
    \/ HandleOperation
    \/ EnqueueHeader
    \/ EnqueueOperations
    \/ ServeHeader
    \/ ServeOperation
    \/ ValidateBlock
    \/ BadBootstrapSendsGoodNodeArbitraryMessage
    \/ BadNodeSendsGoodBootstrapArbitraryMessage
    \/ BootstrapTimeout
    \/ NodeTimeout
    \/ BootstrapBlacklist
    \/ NodeBlacklist
    \/ InitConnections

(*****************)
(* Specification *)
(*****************)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----

(**************)
(* Invariants *)
(**************)

BlacklistOK ==
    /\ b_blacklist \in [ GOOD_BOOTSTRAPPING -> SUBSET Nodes ]
    /\ n_blacklist \in [ GOOD_NODES -> SUBSET Bootstrapping_nodes ]

MessagesOK ==
    /\ b_messages \in [ GOOD_BOOTSTRAPPING -> SUBSET ResponseMessages ]
    /\ n_messages \in [ GOOD_NODES -> SUBSET GetMessages ]

BootstrappingOK ==
    /\ connections        \in [ Bootstrapping_nodes -> SUBSET Nodes ]
    /\ current_head       \in [ GOOD_BOOTSTRAPPING -> Headers ]
    /\ locator            \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> Seq_hd(BlockHashes) ] ]
    /\ fetched_headers    \in [ GOOD_BOOTSTRAPPING \X Nodes -> [ Levels -> SUBSET Headers ] ]
    /\ fetched_operations \in [ GOOD_BOOTSTRAPPING \X Nodes -> [ Levels -> SUBSET Operations ] ]
    /\ level_to_validate  \in [ GOOD_BOOTSTRAPPING -> 1..MAX_LEVEL ]
    /\ validated_blocks   \in [ GOOD_BOOTSTRAPPING -> SUBSET Blocks ]
    /\ header_pipe        \in [ GOOD_BOOTSTRAPPING -> Seq_n(Headers) ]
    /\ operation_pipe     \in [ GOOD_BOOTSTRAPPING -> Seq_n(Set_op(Operations)) ]
    /\ sent_get_branch    \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET Levels ] ]
    /\ sent_get_headers   \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET BlockHashes ] ]
    /\ sent_get_ops       \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET OperationHashes ] ]
    /\ recv_branch        \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET BlockHashes ] ]
    /\ recv_header        \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET Headers ] ]
    /\ recv_operation     \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET Operations ] ]

NodesOK ==
    /\ sent_branch       \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET BlockHashes ] ]
    /\ sent_headers      \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET Headers ] ]
    /\ sent_ops          \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET Operations ] ]
    /\ recv_get_branch   \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET Levels ] ]
    /\ recv_get_headers  \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET BlockHashes ] ]
    /\ recv_get_ops      \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET OperationHashes ] ]
    /\ serving_headers   \in [ GOOD_NODES -> [ Bootstrapping_nodes -> Set_n(BlockHashes) ] ]
    /\ serving_ops       \in [ GOOD_NODES \X Bootstrapping_nodes -> [ BlockHashes -> SUBSET 0..MAX_OPS ] ]

TypeOK ==
    /\ NodesOK
    /\ MessagesOK
    /\ BlacklistOK
    /\ BootstrappingOK

\* TODO safety properties

Safety ==
    /\ TypeOK

(**************)
(* Properties *)
(**************)

\* TODO liveness properties

===================================
