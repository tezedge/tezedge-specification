---- MODULE Bootstrap_pipeline ----

EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS
    BAD_NODES,          \* nodes who behave arbitrarily
    GOOD_NODES,         \* nodes who follow the protocol
    BAD_BOOTSTRAPPING,  \* bootstrapping nodes who behave arbitrarily
    GOOD_BOOTSTRAPPING, \* bootstrapping nodes who follow the protocol
    MIN_PEERS,          \* minimum number of peers
    MAX_PEERS,          \* maximum number of peers
    MAX_LEVEL,          \* maximum level of a block
    CURRENT_HEAD,       \* each good node's current head
    BLOCKS,             \* each good node's blocks
    VALIDATOR           \* function: Blocks -> { "known_valid", "known_invalid", "unknown" }

VARIABLES
    b_blacklist,        \* each good bootstrapping node's set of blacklisted peers
    b_messages,         \* each good bootstrapping node's set of messages
    n_blacklist,        \* each good node's set of blacklisted peers
    n_messages          \* each good node's set of messages

messages  == <<b_messages, n_messages>>
blacklist == <<b_blacklist, n_blacklist>>

\* bootstrapping variables
VARIABLES
    connections,        \* each bootstrapping node's set of connections
    current_head,       \* each good bootstrapping node's current head
    ddb,                \* each good bootstrapping node's ddb
    locator,            \* each good bootstrapping node's function from nodes to the sample history ((level, hash) pairs) they provided
    fetched_headers,    \* each good bootstrapping node's set of fetched headers (fetched from top to bottom)
    fetched_operations, \* each good bootstrapping node's set of fetched operations (fetched from bottom to top)
    validated_blocks,   \* each good bootstrapping node's function from level to validated block at that level
    header_pipe,        \* each good bootstrapping node's queue of fetched headers
    operation_pipe,     \* each good bootstrapping node's queue of fetched operations
    sent_get_branch,    \* each good bootstrapping node's set of peers to whom they have sent a Get_current_branch message
    sent_get_headers,   \* each good bootstrapping node's function from peers to whom they have sent a Get_block_headers message to the requested headers
    sent_get_ops,       \* each good bootstrapping node's function from peers to whom they have sent a Get_operations message to the requested operations
    recv_branch,        \* each good bootstrapping node's set of peers from whom they have received a Current_branch message
    recv_header,        \* each good bootstrapping node's function from peers from whom they have received a Block_header message to set of headers received
    recv_ops,           \* each good bootstrapping node's function from peers from whom they have received a Operation message to set of operations received
    lowest_fetched      \* each good bootstrapping node's lowest common level of fetched headers and operations

bootstrapping_vars == <<connections, current_head, ddb, locator, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
    sent_get_branch, sent_get_headers, sent_get_ops, recv_branch, recv_header, recv_ops>>

b_non_branch_vars == <<connections, current_head, ddb, locator, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
    sent_get_headers, sent_get_ops, recv_header, recv_ops>>

b_non_head_vars == <<connections, current_head, ddb, locator, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
    sent_get_branch, sent_get_headers, sent_get_ops, recv_branch, recv_header, recv_ops>>

b_non_header_vars == <<connections, current_head, ddb, locator, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
    sent_get_branch, sent_get_ops, recv_branch, recv_ops>>

b_non_op_vars == <<connections, current_head, ddb, locator, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
    sent_get_branch, sent_get_headers, recv_branch, recv_header>>

\* node variables
VARIABLES
    activated,          \* each good node's set of activated peers
    sent_branch,        \* each good node's set of peers to whom they have sent a Current_branch message
    sent_headers,       \* each good node's function from peers to whom they have sent a Block_header message to the set of headers sent
    sent_ops,           \* each good node's function from peers to whom they have sent a Operation message to the set of operations sent
    recv_get_branch,    \* each good node's set of peers from whom they have received a Get_current_branch message
    recv_get_headers,   \* each good node's set of peers from whom they have received a Get_block_headers message
    recv_get_ops,       \* each good node's set of peers from whom they have received a Get_operations message
    servicing_headers,  \* each good node's function from peers from whom they have received a Get_block_headers message to the headers they requested
    servicing_ops       \* each good node's function from peers from whom they have received a Get_operations message to the operations they requested

node_vars == <<activated, sent_branch, sent_headers, sent_ops,
    recv_get_branch, recv_get_headers, recv_get_ops, servicing_headers, servicing_ops>>

n_non_branch_vars == <<activated, sent_headers, sent_ops, recv_get_headers, recv_get_ops, servicing_headers, servicing_ops>>

n_non_head_vars == <<activated, sent_branch, sent_headers, sent_ops, recv_get_branch, recv_get_headers, recv_get_ops, servicing_headers, servicing_ops>>

n_non_header_vars == <<activated, sent_branch, sent_ops, recv_get_branch, recv_get_ops, servicing_headers, servicing_ops>>

n_non_op_vars == <<activated, sent_branch, sent_headers, recv_get_branch, recv_get_headers, servicing_headers, servicing_ops>>

node_nonservice_vars == <<activated, sent_branch, sent_headers, sent_ops, recv_get_branch, recv_get_headers, recv_get_ops>>

vars == <<messages, blacklist, bootstrapping_vars, node_vars>>

----

\* four disjoint sets of node IDs
ASSUME BAD_NODES \cap GOOD_NODES = {}
ASSUME BAD_BOOTSTRAPPING \cap GOOD_BOOTSTRAPPING = {}
ASSUME
    LET bootstrapping == BAD_BOOTSTRAPPING \cup GOOD_BOOTSTRAPPING
        nodes == BAD_NODES \cup GOOD_NODES
    IN bootstrapping \cap nodes = {}
\* TODO

----

(***********)
(* Helpers *)
(***********)

NESeq(s) == Seq(s) \ {<<>>}

Seq_n(s) == { seq \in Seq(s) : Len(s) < MAX_LEVEL }

ToSet(seq) == { seq[i] : i \in DOMAIN seq }

Cons(x, seq) == <<x>> \o seq

Min_level_set(set) == CHOOSE x \in set : \A y \in set : x.level <= y.level

Min_level_seq(seq) == Min_level_set(ToSet(seq))

RECURSIVE seq_of_set(_, _)
seq_of_set(s, acc) ==
    IF s = {} THEN acc
    ELSE
        LET x == CHOOSE xx \in s : TRUE
            t == s \ {x}
        IN
        seq_of_set(t, Append(acc, x))

SetToSeq(s) == seq_of_set(s, <<>>)

RECURSIVE index(_, _, _)
index(x, seq, i) ==
    IF seq = <<>> THEN 0
    ELSE
        IF x = Head(seq) THEN i + 1
        ELSE index(x, Tail(seq), i + 1)

Index(x, seq) == index(x, seq, 0)

----

Nodes == BAD_NODES \cup GOOD_NODES

N == Cardinality(Nodes)

Bootstrapping_nodes == BAD_BOOTSTRAPPING \cup GOOD_BOOTSTRAPPING

ConnectionSets == { ps \in SUBSET Nodes : Cardinality(ps) >= MIN_PEERS /\ Cardinality(ps) <= MAX_PEERS }

Levels == 0..MAX_LEVEL

Headers == [ level : Levels, pred : Nat, fitness : Nat ] \* TODO fitness

level_cmp(h1, h2) == h1.level <= h2.level

History == Seq_n(Nat)

Locators == [ current_head : Headers, history : History ]

\* set of lists of operations for each block
Operations == [ block_hash : Nat, op : Seq_n(Nat) ]

Blocks == [ header : Headers, ops : Operations ]

block(hd, op) == [ header |-> hd, ops |-> op ]

genesis == [ header |-> [ level |-> 0, pred |-> 0, fitness |-> N ], ops |-> 0 ]

has_requested_headers(bn, n) == sent_get_headers[bn][n] /= {}
has_requested_ops(bn, n)     == sent_get_ops[bn][n] /= {}

has_sent_header(n, bn)    == sent_headers[n][bn] /= {}
has_sent_operation(n, bn) == sent_ops[n][bn] /= {}

\* block/header hash
hash(hd) == Index(hd, SetToSeq(Headers))

lookup_block_hash(h) == CHOOSE b \in { bh \in Headers : hash(bh) = h } : TRUE

\* operation hash
op_hash(op) == <<op.block_hash, op.op>>

(************)
(* messages *)
(************)

\* good requests
GetCurrentBranchMessages == [ type : {"Get_current_branch"}, from : GOOD_BOOTSTRAPPING ]
GetBlockHeadersMessages  == [ type : {"Get_block_headers"}, from : GOOD_BOOTSTRAPPING, hashes : NESeq(Nat) ]
GetOperationsMessages    == [ type : {"Get_operations"}, from : GOOD_BOOTSTRAPPING, blocks : NESeq(Nat \X Nat) ]
GoodGetMessages          == GetCurrentBranchMessages \cup GetBlockHeadersMessages \cup GetOperationsMessages

\* bad requests
BadGetMessages ==
    LET BadGetCurrentBranch == [ type : {"Get_current_branch"}, from : BAD_BOOTSTRAPPING ]
        BadGetBlockHeaders  == [ type : {"Get_block_headers"}, from : BAD_BOOTSTRAPPING, hashes : NESeq(Nat) ]
        BadGetOperations    == [ type : {"Get_operations"}, from : BAD_BOOTSTRAPPING, blocks : NESeq(Nat) ]
        Bad                 == [ type : {"bad"}, from : BAD_BOOTSTRAPPING ]
    IN BadGetCurrentBranch \cup BadGetBlockHeaders \cup BadGetOperations \cup Bad

\* all requests
GetMessages == GoodGetMessages \cup BadGetMessages

\* request constructors
get_current_branch_msg(n)    == [ type |-> "Get_current_branch", from |-> n ]
get_block_headers_msg(n, hs) == [ type |-> "Get_block_headers", from |-> n, hashes |-> hs ]
get_operations_msg(n, bs)    == [ type |-> "Get_operations", from |-> n, blocks |-> bs ]

\* sets of message types
current_branch_msgs(n) == { msg \in b_messages[n] : msg.type = "Current_branch" }
block_header_msgs(n)   == { msg \in b_messages[n] : msg.type = "Block_header" }
operation_msgs(n)      == { msg \in b_messages[n] : msg.type = "Operation" }

\* good responses
CurrentBranchMessages == [ type : {"Current_branch"}, from : GOOD_NODES, locator : Locators ]
BlockHeaderMessages   == [ type : {"Block_header"}, from : GOOD_NODES, header : Headers ]
OperationsMessages    == [ type : {"Operation"}, from : GOOD_NODES, operation : Operations ]
GoodResponseMessages  == CurrentBranchMessages \cup BlockHeaderMessages \cup OperationsMessages

\* bad responses
BadResponseMessages ==
    LET BadCurrentBranch == [ type : {"Current_branch"}, from : BAD_NODES, locator : Locators ]
        BadBlockHeader   == [ type : {"Block_header"}, from : BAD_NODES, header : Headers ]
        BadOperations    == [ type : {"Operation"}, from : BAD_NODES, operation : Operations ]
        Bad              == [ type : {"bad"}, from : BAD_NODES ]
    IN BadCurrentBranch \cup BadBlockHeader \cup BadOperations \cup Bad

\* all responses
ResponseMessages == GoodResponseMessages \cup BadResponseMessages

\* response constructors
current_branch_msg(n, l) == [ type |-> "Current_branch", from |-> n, locator   |-> l  ]
block_header_msg(n, hd)  == [ type |-> "Block_header",   from |-> n, header    |-> hd ]
operation_msg(n, op)     == [ type |-> "Operation",      from |-> n, operation |-> op ]

\* sets of message types
get_current_branch_msgs(n) == { msg \in n_messages[n] : msg.type = "Get_current_branch" }
get_block_headers_msgs(n)  == { msg \in n_messages[n] : msg.type = "Get_block_headers" }
get_operations_msgs(n)     == { msg \in n_messages[n] : msg.type = "Get_operations" }

\* all messages
Messages == GetMessages \cup ResponseMessages

(******************)
(* Action helpers *)
(******************)
Send_n(n, msg) == n_messages' = [ n_messages EXCEPT ![n] = @ \cup {msg} ]
Send_b(b, msg) == b_messages' = [ b_messages EXCEPT ![b] = @ \cup {msg} ]
Drop_n(n, msg) == n_messages' = [ n_messages EXCEPT ![n] = @ \ {msg}]
Drop_b(b, msg) == b_messages' = [ b_messages EXCEPT ![b] = @ \ {msg}]

----

(***********)
(* Actions *)
(***********)

\* fetch_step(sndr, rcvr, step)
\* 1. check that locator is valid
\* 2. get block header associated to hash
\* 3. check if received header is acceptable
\* 4. loop on the predeessor of the current block

\* fetch_headers(sndr, rcvr, hash_list)

\* fetch_operations(sndr, rcvr, op_hash_list_list)

\* validate_blocks - args?

\* header_timeout
\* operation_timeout
\* other errors?

\* Block_validator
\* type result =
\*   | Already_commited
\*   | Outdated_block
\*   | Validated
\*   | Validation_error of error trace

\* block validity
\* type validity = Unkown | Known_valid | Known_invalid

\* requests - bootstrapping nodes

send_get_current_branch(bn, n) ==
    /\ Send_n(n, get_current_branch_msg(bn))
    /\ sent_get_branch' = [ sent_get_branch EXCEPT ![bn] = @ \cup {n} ]
    /\ UNCHANGED <<b_messages, blacklist, node_vars, b_non_branch_vars, recv_branch>>

SendGetCurrentBranch == \E bn \in GOOD_BOOTSTRAPPING :
    \E n \in connections[bn] :
        /\ n \notin sent_get_branch[bn]
        /\ send_get_current_branch(bn, n)

send_get_block_headers(bn, n, hs) ==
    /\ Send_n(n, get_block_headers_msg(bn, hs))
    /\ sent_get_headers' = [ sent_get_headers EXCEPT ![bn][n] = @ \cup ToSet(hs) ]
    /\ UNCHANGED <<b_messages, blacklist, node_vars, b_non_header_vars, recv_header>>

SendGetBlockHeaders == \E bn \in GOOD_BOOTSTRAPPING :
    \E n \in connections[bn] :
        /\ n \in sent_get_branch[bn]
        /\ n \in recv_branch[bn]
        /\ locator[bn][n] /= <<>>
        /\ ~has_requested_headers(bn, n)
        /\ send_get_block_headers(bn, n, locator[bn][n])

send_get_operations(bn, n, bs) ==
    /\ Send_n(n, get_operations_msg(bn, bs))
    /\ sent_get_ops' = [ sent_get_ops EXCEPT ![bn][n] = @ \cup ToSet(bs) ]
    /\ UNCHANGED <<b_messages, blacklist, node_vars, b_non_op_vars, recv_ops>>

\* TODO which headers to request operations for?
SendGetOperations == \E bn \in GOOD_BOOTSTRAPPING :
    \E n \in connections[bn] :
        /\ n \in sent_get_branch[bn]
        /\ n \in recv_branch[bn]
        /\ has_requested_headers(bn, n)
        /\ has_sent_header(n, bn)
        /\ ~has_requested_ops(bn, n)
        /\ send_get_operations(bn, n, fetched_headers[bn])

\* responses - nodes

\* TODO what locator (header, history) to send?
\* TODO enabling conditions + add [bn] to appropriate recv set
HandleGetCurrentBranch == \E n \in GOOD_NODES :
    \E msg \in get_current_branch_msgs(n) :
        LET bn == msg.from IN
        /\ Drop_n(n, msg)
        /\ Send_b(bn, current_branch_msg(n, [ current_head |-> CURRENT_HEAD[n], history |-> <<>> ]))
        /\ recv_get_branch' = [ recv_get_branch EXCEPT ![n] = @ \cup {bn} ]
        /\ sent_branch' = [ sent_branch EXCEPT ![n] = @ \cup {bn} ]
        /\ UNCHANGED <<blacklist, bootstrapping_vars, n_non_branch_vars, recv_get_branch>>

HandleGetBlockHeaders == \E n \in GOOD_NODES :
    \E msg \in get_block_headers_msgs(n) :
        LET bn == msg.from
            hs == msg.hashes
        IN
        /\ Drop_n(n, msg)
        /\ recv_get_headers' = [ recv_get_headers EXCEPT ![n] = @ \cup {bn} ] \* TODO
        /\ servicing_headers' = [ servicing_headers EXCEPT ![n][bn] = Append(@, hs) ]
        /\ UNCHANGED <<b_messages, blacklist, bootstrapping_vars, node_nonservice_vars, servicing_ops>>

HandleGetOperations == \E n \in GOOD_NODES :
    \E msg \in get_operations_msgs(n) :
        LET bn == msg.from
            bs == msg.blocks
        IN
        /\ Drop_n(n, msg)
        /\ recv_get_ops' = [ recv_get_ops EXCEPT ![n] = @ \cup {bn} ]
        /\ servicing_ops' = [ servicing_ops EXCEPT ![n][bn] = Append(@, bs) ]
        /\ UNCHANGED <<b_messages, blacklist, bootstrapping_vars, node_nonservice_vars, servicing_headers>>

\* bootstrapping node handle responses
HandleCurrentBranch == \E bn \in GOOD_BOOTSTRAPPING :
    \E msg \in current_branch_msgs(bn) :
        LET n == msg.from
            l == msg.locator
        IN
        /\ Drop_b(bn, msg)
        /\ locator' = [ locator EXCEPT ![bn][n] = l ]
        /\ recv_branch' = [ recv_branch EXCEPT ![bn] = @ \cup {n} ]
        /\ UNCHANGED <<n_messages, blacklist, node_vars>>
        /\ UNCHANGED <<connections, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
                       sent_get_branch, sent_get_headers, sent_get_ops, recv_header, recv_ops>>

HandleBlockHeader == \E bn \in GOOD_BOOTSTRAPPING :
    \E msg \in block_header_msgs(bn) :
        LET n  == msg.from
            hd == msg.header
        IN
        /\ fetched_headers' = [ fetched_headers EXCEPT ![bn] = @ \cup {hd} ]
        /\ UNCHANGED <<>> \* TODO

HandleOperation == \E bn \in GOOD_BOOTSTRAPPING :
    \E msg \in operation_msgs(bn) :
        LET n  == msg.from
            bh == msg.block_hash
            op == msg.operation
        IN
        /\ fetched_operations' = [ fetched_operations EXCEPT ![bn] =
                IF bh \in DOMAIN @ THEN @[bh] \cup {op}
                ELSE @ @@ bh :> {op} ]
        /\ UNCHANGED <<>> \* TODO

EnqueueHeader == \E bn \in GOOD_BOOTSTRAPPING :
    LET hd == Min_level_set(fetched_headers[bn]) IN
    /\ hd \notin ToSet(header_pipe[bn])
    /\ header_pipe' = [ header_pipe EXCEPT ![bn] = Cons(hd, @) ]
    /\ UNCHANGED <<>> \* TODO

EnqueueOperation == \E bn \in GOOD_BOOTSTRAPPING :
    /\ operation_pipe[bn] /= <<>>
    /\ LET op == Head(operation_pipe[bn])
           bh == lookup_block_hash(Head(op).block_hash)
       IN FALSE \* TODO

\* nodes serve bootstrapping nodes' requests

\* TODO
ServeHeader == \E n \in GOOD_NODES, bn \in Bootstrapping_nodes :
    /\ servicing_headers[n][bn] /= <<>>
    /\ LET hd == Head(servicing_headers[n][bn]) IN
        /\ Send_b(bn, block_header_msg(n, hd))
        /\ sent_headers' = [ sent_headers EXCEPT ![n][bn] = Append(@, hd) ]
        /\ servicing_headers' = [ servicing_headers EXCEPT ![n][bn] = Tail(@) ]
        /\ UNCHANGED <<n_messages, blacklist, node_nonservice_vars, servicing_ops, bootstrapping_vars>>

ServeOperation == \E n \in GOOD_NODES, bn \in Bootstrapping_nodes :
    LET ops == servicing_ops[n][bn] IN
    /\ ops /= <<>>
    /\ LET op == Head(ops) IN
        /\ Send_b(bn, operation_msg(n, op))
        /\ sent_ops' = [ sent_ops EXCEPT ![n][bn] = @ \o <<op>> ]
        /\ servicing_ops' = [ servicing_ops EXCEPT ![n][bn] = Tail(@) ]
        /\ UNCHANGED <<n_messages, blacklist, node_nonservice_vars, servicing_headers, bootstrapping_vars>>

\* nodes form blocks from fetched headers and operations
\* TODO check that all operations for block are present in operations_pipe before validating
validate_block(bn, hd, op) ==
    LET v  == VALIDATOR[hd, op] IN
    CASE v = "known_valid" ->
        /\ fetched_headers' = [ fetched_headers EXCEPT ![bn] = Tail(@) ]
        /\ fetched_operations' = [ fetched_operations EXCEPT ![bn] = Tail(@) ]
        /\ validated_blocks' = [ validated_blocks EXCEPT ![bn] = @ \cup {block(hd, op)} ]
        /\ UNCHANGED <<>>
      [] v = "known_invalid" -> FALSE
      [] v = "unknown" -> FALSE

ValidateBlock == \E bn \in GOOD_BOOTSTRAPPING :
    /\ header_pipe[bn] /= <<>>
    /\ operation_pipe[bn] /= <<>>
    /\ LET hd == Head(header_pipe[bn])
           op == Head(operation_pipe[bn])
       IN validate_block(bn, hd, op)

\* undesirable actions

\* TODO
BadBootstrapperSendsGoodNodeArbitraryMessage == \E bn \in BAD_BOOTSTRAPPING, n \in Nodes :
    \E msg \in { m \in BadGetMessages : m.from = bn } :
        /\ Send_n(n, msg)
        \* send request for known invalid block header/operations

BadNodeSendsGoodBootstrapperArbitraryMessage == \E n \in BAD_NODES, bn \in Bootstrapping_nodes :
    \E msg \in { m \in BadResponseMessages : m.from = n } :
        LET t == msg.type IN
        CASE t = "Block_header" ->
            \E hd \in { bh \in Headers : bh \notin recv_get_headers[n][bn] } :
                /\ block_header_msg(n, hd)
                /\ UNCHANGED <<>> \* TODO
        \/ /\ FALSE

Blacklist == FALSE \* TODO

BootstrapTimeout == \E bn \in GOOD_BOOTSTRAPPING :
    \/ \E n \in sent_get_branch[bn] :
        /\ n \notin recv_branch[bn]
        /\ FALSE \* TODO
    \/ FALSE

NodeTimeout == FALSE \* TODO

\* intialize connections
init_connections(bn) == \E ps \in ConnectionSets :
    /\ connections' = [ connections EXCEPT ![bn] = ps ]
    /\ UNCHANGED <<node_vars, blacklist, messages, locator, fetched_headers, fetched_operations, validated_blocks>>

InitConnections == \E n \in Bootstrapping_nodes :
    /\ connections[n] = {}
    /\ init_connections(n)

----

(*********************)
(* Initial predicate *)
(*********************)

\* TODO check all variabels accounted for

MessagesInit ==
    /\ b_messages = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ n_messages = [ n \in GOOD_NODES |-> {} ]

BlacklistInit ==
    /\ b_blacklist = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ n_blacklist = [ n \in GOOD_NODES |-> {} ]

\* bootstrapping_vars == <<connections, locator, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
\* sent_get_branch, sent_get_head, sent_get_headers, sent_get_ops, recv_branch, recv_head, recv_header, recv_ops>>
BootstrappingInit ==
    /\ connections        = [ n \in Bootstrapping_nodes |-> {} ]
    /\ current_head       = [ n \in GOOD_BOOTSTRAPPING  |-> genesis ]
    \* /\ ddb                = [ n \in GOOD_BOOTSTRAPPING  |-> [ l \in {} ] ] TODO
    /\ locator            = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ fetched_headers    = [ n \in GOOD_BOOTSTRAPPING  |-> [ l \in Levels |-> {} ] ]
    /\ fetched_operations = [ n \in GOOD_BOOTSTRAPPING  |-> [ l \in Levels |-> {} ] ]
    /\ validated_blocks   = [ n \in GOOD_BOOTSTRAPPING  |-> [ l \in {0} |-> genesis ] ]
    /\ header_pipe        = [ n \in GOOD_BOOTSTRAPPING  |-> <<>> ]
    /\ operation_pipe     = [ n \in GOOD_BOOTSTRAPPING  |-> <<>> ]
    /\ sent_get_branch    = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ sent_get_headers   = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ sent_get_ops       = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ recv_branch        = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ recv_header        = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ recv_ops           = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]

\* node_vars == <<activated, sent_branch, sent_head, sent_header, sent_ops, recv_get_branch, recv_get_head, recv_get_headers, recv_get_ops>>
NodeInit ==
    /\ activated         = [ n \in GOOD_NODES |-> {} ]
    /\ recv_get_branch   = [ n \in GOOD_NODES |-> {} ]
    /\ recv_get_headers  = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ recv_get_ops      = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ sent_branch       = [ n \in GOOD_NODES |-> {} ]
    /\ sent_headers      = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ sent_ops          = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ servicing_headers = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> <<>> ] ]
    /\ servicing_ops     = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]

Init ==
    /\ NodeInit
    /\ MessagesInit
    /\ BlacklistInit
    /\ BootstrappingInit

(****************)
(* Next actions *)
(****************)

\* TODO check that all actions are accounted for

Next ==
    \/ SendGetCurrentBranch
    \/ SendGetBlockHeaders
    \/ SendGetOperations
    \/ HandleCurrentBranch
    \/ HandleBlockHeader
    \/ HandleOperation
    \/ ServeHeader
    \/ ServeOperation
    \/ ValidateBlock
    \/ BadBootstrapperSendsGoodNodeArbitraryMessage
    \/ BadNodeSendsGoodBootstrapperArbitraryMessage
    \/ Blacklist
    \/ BootstrapTimeout
    \/ NodeTimeout
    \/ InitConnections

(*****************)
(* Specification *)
(*****************)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----

(**************)
(* Invariants *)
(**************)

\* TODO check all variabels accounted for

BlacklistOK ==
    /\ b_blacklist \in [ GOOD_BOOTSTRAPPING -> SUBSET Nodes ]
    /\ n_blacklist \in [ GOOD_NODES -> SUBSET Bootstrapping_nodes ]

MessagesOK ==
    /\ b_messages \in [ GOOD_BOOTSTRAPPING -> SUBSET ResponseMessages ]
    /\ n_messages \in [ GOOD_NODES -> SUBSET GetMessages ]

BootstrappingOK ==
    /\ connections        \in [ GOOD_BOOTSTRAPPING -> SUBSET Nodes ]
    /\ current_head       \in [ GOOD_BOOTSTRAPPING -> [ Levels -> Headers ] ]
    \* /\ ddb
    /\ locator            \in [ GOOD_BOOTSTRAPPING -> History ]
    /\ fetched_headers    \in [ GOOD_BOOTSTRAPPING -> [ Levels -> SUBSET Headers ] ]
    /\ fetched_operations \in [ GOOD_BOOTSTRAPPING -> [ Levels ->SUBSET Operations ] ]
    /\ validated_blocks   \in [ GOOD_BOOTSTRAPPING -> SUBSET Blocks ]
    /\ header_pipe        \in [ GOOD_BOOTSTRAPPING -> Seq_n(Headers) ]
    /\ operation_pipe     \in [ GOOD_BOOTSTRAPPING -> Seq_n(Operations) ]
    /\ sent_get_branch    \in [ GOOD_BOOTSTRAPPING -> SUBSET Nodes ]
    /\ sent_get_headers   \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET Headers ] ]
    /\ sent_get_ops       \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET Operations ] ]
    /\ recv_branch        \in [ GOOD_BOOTSTRAPPING -> SUBSET Nodes ]
    /\ recv_header        \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET Headers ] ]
    /\ recv_ops           \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET Operations ] ]

NodesOK ==
    /\ activated         \in [ GOOD_NODES -> SUBSET Bootstrapping_nodes ]
    /\ sent_branch       \in [ GOOD_NODES -> SUBSET Bootstrapping_nodes ]
    /\ sent_headers      \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET Headers ] ]
    /\ sent_ops          \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET Operations ] ]
    /\ recv_get_branch   \in [ GOOD_NODES -> SUBSET Bootstrapping_nodes ]
    /\ recv_get_headers  \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET Headers ] ]
    /\ recv_get_ops      \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET Operations ] ]
    /\ servicing_headers \in [ GOOD_NODES -> [ Bootstrapping_nodes -> Seq_n(Headers) ] ]
    /\ servicing_ops     \in [ GOOD_NODES -> [ Bootstrapping_nodes -> Seq_n(Operations) ] ]

TypeOK ==
    /\ NodesOK
    /\ MessagesOK
    /\ BlacklistOK
    /\ BootstrappingOK

(**************)
(* Properties *)
(**************)

===================================
