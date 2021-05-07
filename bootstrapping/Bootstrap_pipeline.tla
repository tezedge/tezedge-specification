---- MODULE Bootstrap_pipeline ----

EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS
    BAD_NODES,          \* nodes who behave arbitrarily
    GOOD_NODES,         \* nodes who follow the protocol
    BAD_BOOTSTRAPPING,  \* bootstrapping nodes who behave arbitrarily
    GOOD_BOOTSTRAPPING, \* bootstrapping nodes who follow the protocol
    MIN_PEERS,          \* minimum number of peers
    MAX_PEERS,          \* maximum number of peers
    MAX_LEVEL,          \* maximum level of a block
    CURRENT_HEAD,       \* each good node's current head
    BLOCKS              \* each good node's blocks

VARIABLES
    b_blacklist,        \* each good bootstrapping node's set of blacklisted peers
    b_messages,         \* each good bootstrapping node's set of messages
    n_blacklist,        \* each good node's set of blacklisted peers
    n_messages          \* each good node's set of messages

messages == <<b_messages, n_messages>>

blacklist == <<b_blacklist, n_blacklist>>

\* bootstrapping variables
VARIABLES
    connections,        \* each bootstrapping node's set of connections
    locators,           \* each good bootstrapping node's function from nodes to the locators they provided
    fetched_headers,    \* each good bootstrapping node's set of fetched headers (fetched from top to bottom)
    fetched_operations, \* each good bootstrapping node's set of fetched operations (fetched from bottom to top)
    validated_blocks,   \* each good bootstrapping node's set of validated blocks
    header_pipe,        \* each good bootstrapping node's queue of fetched headers
    operation_pipe,     \* each good bootstrapping node's queue of fetched operations
    sent_get_branch,    \* each good bootstrapping node's set of peers to whom they have sent a Get_current_branch message
    sent_get_head,      \* each good bootstrapping node's set of peers to whom they have sent a Get_current_head message
    sent_get_headers,   \* each good bootstrapping node's function from peers to whom they have sent a Get_block_headers message to the requested headers
    sent_get_ops,       \* each good bootstrapping node's function from peers to whom they have sent a Get_operations message to the requested operations
    recv_branch,        \* each good bootstrapping node's set of peers from whom they have received a Current_branch message
    recv_head,          \* each good bootstrapping node's set of peers from whom they have received a Current_head message
    recv_header,        \* each good bootstrapping node's function from peers from whom they have received a Block_header message to set of headers received
    recv_ops            \* each good bootstrapping node's function from peers from whom they have received a Operation message to set of operations received

bootstrapping_vars == <<connections, locators, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
    sent_get_branch, sent_get_head, sent_get_headers, sent_get_ops, recv_branch, recv_head, recv_header, recv_ops>>

b_non_branch_vars == <<connections, locators, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
    sent_get_head, sent_get_headers, sent_get_ops, recv_head, recv_header, recv_ops>>

b_non_head_vars == <<connections, locators, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
    sent_get_branch, sent_get_headers, sent_get_ops, recv_branch, recv_header, recv_ops>>

b_non_header_vars == <<connections, locators, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
    sent_get_branch, sent_get_head, sent_get_ops, recv_branch, recv_head, recv_ops>>

b_non_op_vars == <<connections, locators, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
    sent_get_branch, sent_get_head, sent_get_headers, recv_branch, recv_head, recv_header>>

\* node variables
VARIABLES
    activated,          \* each good node's set of activated peers
    sent_branch,        \* each good node's set of peers to whom they have sent a Current_branch message
    sent_head,          \* each good node's set of peers to whom they have sent a Current_head message
    sent_headers,       \* each good node's function from peers to whom they have sent a Block_header message to the set of headers sent
    sent_ops,           \* each good node's function from peers to whom they have sent a Operation message to the set of operations sent
    recv_get_branch,    \* each good node's set of peers from whom they have received a Get_current_branch message
    recv_get_head,      \* each good node's set of peers from whom they have received a Get_current_head message
    recv_get_headers,   \* each good node's set of peers from whom they have received a Get_block_headers message
    recv_get_ops,       \* each good node's set of peers from whom they have received a Get_operations message
    servicing_headers,  \* each good node's function from peers from whom they have received a Get_block_headers message to the headers they requested
    servicing_ops       \* each good node's function from peers from whom they have received a Get_operations message to the operations they requested

node_vars == <<activated, sent_branch, sent_head, sent_headers, sent_ops,
    recv_get_branch, recv_get_head, recv_get_headers, recv_get_ops, servicing_headers, servicing_ops>>

n_non_branch_vars == <<activated, sent_head, sent_headers, sent_ops, recv_get_head, recv_get_headers, recv_get_ops, servicing_headers, servicing_ops>>

n_non_head_vars == <<activated, sent_branch, sent_headers, sent_ops, recv_get_branch, recv_get_headers, recv_get_ops, servicing_headers, servicing_ops>>

n_non_header_vars == <<activated, sent_branch, sent_head, sent_ops, recv_get_branch, recv_get_head, recv_get_ops, servicing_headers, servicing_ops>>

n_non_op_vars == <<activated, sent_branch, sent_head, sent_headers, recv_get_branch, recv_get_head, recv_get_headers, servicing_headers, servicing_ops>>

node_nonservice_vars == <<activated, sent_branch, sent_head, sent_headers, sent_ops, recv_get_branch, recv_get_head, recv_get_headers, recv_get_ops>>

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

Headers == [ level : Nat, pred : Nat, fitness : Nat ] \* TODO fitness

\* head has higher level, end has lower level
Steps == [ head : Nat, end : Nat ]

Locators == [ current_head : Headers, history : Seq_n(Nat) ]

Operations == [ block_hash : Nat, op : Nat ]

Blocks == [ header : Headers, ops : Operations ]

Mempool == [ known_valid : Seq(Nat), pending : SUBSET Nat ]

genesis == [ header |-> [ level |-> 0, fitness |-> N ], ops |-> 0 ]

has_requested_headers(bn, n) == sent_get_headers[bn][n] /= {}

has_requested_ops(bn, n) == sent_get_ops[bn][n] /= {}

has_sent_header(n, bn) == sent_headers[n][bn] /= {}

has_sent_operation(n, bn) == sent_ops[n][bn] /= {}

\* block/header hash
hash(hd) == Index(hd, SetToSeq(Headers))

\* operation hash
op_hash(op) == <<op.block_hash, op.op>>

(************)
(* messages *)
(************)

\* good requests
GetCurrentBranchMessages == [ type : {"Get_current_branch"}, from : GOOD_BOOTSTRAPPING ]

GetBlockHeadersMessages == [ type : {"Get_block_headers"}, from : GOOD_BOOTSTRAPPING, hashes : NESeq(Nat) ]

GetOperationsMessages == [ type : {"Get_operations"}, from : GOOD_BOOTSTRAPPING, blocks : NESeq(Nat) ]

GoodGetMessages == GetCurrentBranchMessages \cup GetBlockHeadersMessages \cup GetOperationsMessages

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
get_current_branch_msg(n) == [ type |-> "Get_current_branch", from |-> n ]

get_block_headers_msg(n, hs) == [ type |-> "Get_block_headers", from |-> n, hashes |-> hs ]

get_operations_msg(n, bs) == [ type |-> "Get_operations", from |-> n, blocks |-> bs ]

\* sets of message types
current_branch_msgs(n) == { msg \in b_messages[n] : msg.type = "Current_branch" }

block_header_msgs(n) == { msg \in b_messages[n] : msg.type = "Block_header" }

operation_msgs(n) == { msg \in b_messages[n] : msg.type = "Operation" }

\* good responses
CurrentBranchMessages == [ type : {"Current_branch"}, from : GOOD_NODES, locator : Locators ]

BlockHeaderMessages == [ type : {"Block_header"}, from : GOOD_NODES, header : Headers ]

OperationsMessages == [ type : {"Operation"}, from : GOOD_NODES, operation : Operations ]

GoodResponseMessages == CurrentBranchMessages \cup BlockHeaderMessages \cup OperationsMessages

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
current_branch_msg(n, l) == [ type |-> "Current_branch", from |-> n, locator |-> l ]

block_header_msg(n, hd) == [ type |-> "Block_header", from |-> n, header |-> hd ]

operation_msg(n, op) == [ type |-> "Operation", from |-> n, operation |-> op ]

\* sets of message types
get_current_branch_msgs(n) == { msg \in n_messages[n] : msg.type = "Get_current_branch" }

get_block_headers_msgs(n) == { msg \in n_messages[n] : msg.type = "Get_block_headers" }

get_operations_msgs(n) == { msg \in n_messages[n] : msg.type = "Get_operations" }

\* all messages
Messages == GetMessages \cup ResponseMessages

(******************)
(* Action helpers *)
(******************)
Send_n(n, msg) == n_messages' = [ n_messages EXCEPT ![n] = @ \cup {msg} ]

Send_b(bn, msg) == b_messages' = [ b_messages EXCEPT ![bn] = @ \cup {msg} ]

Drop_n(n, msg) == n_messages' = [ n_messages EXCEPT ![n] = @ \ {msg}]

Drop_b(bn, msg) == b_messages' = [ b_messages EXCEPT ![bn] = @ \ {msg}]

----

(***********)
(* Actions *)
(***********)

\* Q: how to specify fitness?

\* fetch_step(sndr, rcvr, step)
\* 1. check that locator is valid
\* 2. get block header associated to hash
\* 3. check if received header is acceptable
\* 4. loop on the predeessor of the current block

\* fetch_headers(sndr, rcvr, )

\* fetch_operations

\* validate_blocks

\* header_timeout
\* operation_timeout
\* other errors?
\* logging?

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
        /\ n \in sent_get_head[bn]
        /\ n \in recv_head[bn]
        /\ locators[bn][n] /= <<>>
        /\ ~has_requested_headers(bn, n)
        /\ send_get_block_headers(bn, n, locators[bn][n])

send_get_operations(bn, n, bs) ==
    /\ Send_n(n, get_operations_msg(bn, bs))
    /\ sent_get_ops' = [ sent_get_ops EXCEPT ![bn][n] = @ \cup ToSet(bs) ]
    /\ UNCHANGED <<b_messages, blacklist, node_vars, b_non_op_vars, recv_ops>>

\* TODO which headers to request operations for?
SendGetOperations == \E bn \in GOOD_BOOTSTRAPPING :
    \E n \in connections[bn] :
        /\ n \in sent_get_branch[bn]
        /\ n \in recv_branch[bn]
        /\ n \in sent_get_head[bn]
        /\ n \in recv_head[bn]
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
        /\ Send_b(bn, current_branch_msg(n, [ current_head |-> {}, history |-> <<>> ]))
        /\ sent_branch' = [ sent_branch EXCEPT ![n] = @ \cup {bn} ]
        /\ UNCHANGED <<blacklist, bootstrapping_vars, n_non_branch_vars, recv_get_branch>>

HandleGetBlockHeaders == \E n \in GOOD_NODES :
    \E msg \in get_block_headers_msgs(n) :
        LET bn == msg.from
            hs == msg.hashes
        IN
        /\ Drop_n(n, msg)
        /\ servicing_headers' = [ servicing_headers EXCEPT ![n][bn] = Append(hs, @) ]
        /\ UNCHANGED <<b_messages, blacklist, bootstrapping_vars, node_nonservice_vars, servicing_ops>>

HandleGetOperations == \E n \in GOOD_NODES :
    \E msg \in get_operations_msgs(n) :
        LET bn == msg.from
            bs == msg.blocks
        IN
        /\ Drop_n(n, msg)
        /\ servicing_ops' = [ servicing_ops EXCEPT ![n][bn] = Append(bs, @) ]
        /\ UNCHANGED <<b_messages, blacklist, bootstrapping_vars, node_nonservice_vars, servicing_headers>>

\* bootstrapping node handle messagesresponses
HandleCurrentBranch == \E bn \in GOOD_BOOTSTRAPPING :
    \E msg \in current_branch_msgs(bn) :
        LET n == msg.from
            l == msg.locator
        IN
        /\ Drop_b(bn, msg)
        /\ locators' = [ locators EXCEPT ![bn][n] = l ]
        /\ recv_branch' = [ recv_branch EXCEPT ![bn] = @ \cup {n} ]
        /\ UNCHANGED <<n_messages, blacklist, node_vars>>
        /\ UNCHANGED <<connections, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
                       sent_get_branch, sent_get_head, sent_get_headers, sent_get_ops, recv_head, recv_header, recv_ops>>

\* TODO

HandleBlockHeader == {}

HandleOperation == {}

\* nodes serve bootstrapping nodes

\* TODO
ServeHeader == \E n \in GOOD_NODES, bn \in Bootstrapping_nodes :
    LET hdrs == servicing_headers[n][bn] IN
    /\ hdrs /= <<>>
    /\ LET hd == Head(hdrs) IN
        /\ Send_b(bn, block_header_msg(n, hd))
        /\ sent_headers' = [ sent_headers EXCEPT ![n][bn] = @ \o <<hd>> ]
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

ValidateBlock == {} \* TODO combine header and operations and validate

\* undesirable actions

BadBootstrapperSendsGoodNodeArbitraryMessage == {} \* TODO

BadNodeSendsGoodBootstrapperArbitraryMessage == {} \* TODO

Blacklist == {} \* TODO

Timeout == {} \* TODO

\* intialize connections
init_connections(bn) == \E ps \in ConnectionSets :
    /\ connections' = [ connections EXCEPT ![bn] = ps ]
    /\ UNCHANGED <<node_vars, b_blacklist, b_messages, locators, fetched_headers, fetched_operations, validated_blocks>>

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

\* bootstrapping_vars == <<connections, locators, fetched_headers, fetched_operations, validated_blocks, header_pipe, operation_pipe,
\* sent_get_branch, sent_get_head, sent_get_headers, sent_get_ops, recv_branch, recv_head, recv_header, recv_ops>>
BootstrappingInit ==
    /\ connections        = [ n \in Bootstrapping_nodes |-> {} ]
    /\ locators           = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> <<>> ] ]
    /\ fetched_headers    = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ fetched_operations = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ validated_blocks   = [ n \in GOOD_BOOTSTRAPPING  |-> {genesis} ]
    /\ header_pipe        = [ n \in GOOD_BOOTSTRAPPING  |-> <<>> ]
    /\ operation_pipe     = [ n \in GOOD_BOOTSTRAPPING  |-> <<>> ]
    /\ sent_get_branch    = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ sent_get_head      = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ sent_get_headers   = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ sent_get_ops       = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ recv_branch        = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ recv_head          = [ n \in GOOD_BOOTSTRAPPING  |-> {} ]
    /\ recv_header        = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]
    /\ recv_ops           = [ n \in GOOD_BOOTSTRAPPING  |-> [ m \in Nodes |-> {} ] ]

\* node_vars == <<activated, sent_branch, sent_head, sent_header, sent_ops, recv_get_branch, recv_get_head, recv_get_headers, recv_get_ops>>
NodeInit ==
    /\ activated         = [ n \in GOOD_NODES |-> {} ]
    /\ recv_get_branch   = [ n \in GOOD_NODES |-> {} ]
    /\ recv_get_head     = [ n \in GOOD_NODES |-> {} ]
    /\ recv_get_headers  = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ recv_get_ops      = [ n \in GOOD_NODES |-> [ m \in Bootstrapping_nodes |-> {} ] ]
    /\ sent_branch       = [ n \in GOOD_NODES |-> {} ]
    /\ sent_head         = [ n \in GOOD_NODES |-> {} ]
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
    \/ Timeout
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
    /\ locators           \in [ GOOD_BOOTSTRAPPING -> Seq_n(Steps) ]
    /\ fetched_headers    \in [ GOOD_BOOTSTRAPPING -> SUBSET Headers ]
    /\ fetched_operations \in [ GOOD_BOOTSTRAPPING -> SUBSET Operations ]
    /\ validated_blocks   \in [ GOOD_BOOTSTRAPPING -> SUBSET Blocks ]
    /\ header_pipe        \in [ GOOD_BOOTSTRAPPING -> Seq_n(Headers) ]
    /\ operation_pipe     \in [ GOOD_BOOTSTRAPPING -> Seq_n(Operations) ]
    /\ sent_get_branch    \in [ GOOD_BOOTSTRAPPING -> SUBSET Nodes ]
    /\ sent_get_head      \in [ GOOD_BOOTSTRAPPING -> SUBSET Nodes ]
    /\ sent_get_headers   \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET Headers ] ]
    /\ sent_get_ops       \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET Operations ] ]
    /\ recv_branch        \in [ GOOD_BOOTSTRAPPING -> SUBSET Nodes ]
    /\ recv_head          \in [ GOOD_BOOTSTRAPPING -> SUBSET Nodes ]
    /\ recv_header        \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET Headers ] ]
    /\ recv_ops           \in [ GOOD_BOOTSTRAPPING -> [ Nodes -> SUBSET Operations ] ]

NodesOK ==
    /\ activated         \in [ GOOD_NODES -> SUBSET Bootstrapping_nodes ]
    /\ sent_branch       \in [ GOOD_NODES -> SUBSET Bootstrapping_nodes ]
    /\ sent_head         \in [ GOOD_NODES -> SUBSET Bootstrapping_nodes ]
    /\ sent_headers      \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET Headers ] ]
    /\ sent_ops          \in [ GOOD_NODES -> [ Bootstrapping_nodes -> SUBSET Operations ] ]
    /\ recv_get_branch   \in [ GOOD_NODES -> SUBSET Bootstrapping_nodes ]
    /\ recv_get_head     \in [ GOOD_NODES -> SUBSET Bootstrapping_nodes ]
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
