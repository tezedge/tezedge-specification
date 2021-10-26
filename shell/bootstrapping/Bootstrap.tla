---- MODULE Bootstrap ----

EXTENDS FiniteSets, Naturals, Sequences, TLC, Hash, Samples

\* TODO should we make these variables
CONSTANTS
    NODES,              \* set of node ids
    MIN_PEERS,          \* minimum number of peers
    MAX_PEERS,          \* maximum number of peers
    MAX_OPS,            \* maximum number of operations per block
    MAX_SCORE,          \* maximum peer score
    INCR_SCORE,         \* increment score
    DECR_SCORE,         \* decrement score
    INIT_CHAIN,         \* initial chain
    INIT_HEAD,          \* initial head
    INIT_CONNECTIONS,   \* initial connections
    NONE                \* null value

VARIABLES
    banned,             \* set of banned peers
    greylist,           \* the node's set of greylisted peers
    messages,           \* the node's set of messages
    chain,              \* the node's local chain
    connections,        \* the node's set of connections
    current_head,       \* the node's current head (header with hash)
    peer_head,          \* the node's peers' current heads
    peer_score,         \* metric for peer reliability
    earliest_hashes,    \* the earliest non-fetched hashes supplied by peers' current branches
    target_hash,        \* the block hash we build our segment up to
    target_level,       \* the level of the block we're building our segemtn to
    pending_headers,    \* the segment of headers retrieved up to the current checkpoint
    pending_operations, \* the corresponding operations for the pending headers
    sent_get_branch,    \* the node's set of peers to whom they have sent a Get_current_branch message
    sent_get_headers,   \* the node's function from peers to whom they have sent a Get_block_headers message to the requested headers
    sent_get_ops,       \* the node's function from peers to whom they have sent a Get_operations message to the requested operations
    recv_branch,        \* the node's set of peers from whom they have received a Current_branch message
    recv_head,          \* the node's set of received peer heads
    recv_header,        \* the node's function from peers to the set of headers with hashes received
    recv_operation      \* the node's function from peers to set of operations received

VARIABLES
    mem_size            \* each good bootstrapping node's estimated memory usage

\* inclusive variables
sent_vars    == <<sent_get_branch, sent_get_headers, sent_get_ops>>
recv_vars    == <<recv_branch, recv_head, recv_header, recv_operation>>
local_vars   == <<banned, greylist, messages, chain, connections, current_head>>
peer_vars    == <<peer_head, peer_score, earliest_hashes, target_hash, target_level>>
pending_vars == <<pending_headers, pending_operations>>

\* exclusive variables
non_conn_vars    == <<greylist, messages, chain, current_head, peer_vars, pending_vars, sent_vars, recv_vars>>
non_branch_vars  == <<local_vars, peer_vars, pending_vars, sent_get_headers, sent_get_ops, recv_header, recv_operation>>
non_header_vars  == <<local_vars, peer_vars, pending_vars, sent_get_branch, sent_get_ops, recv_branch, recv_operation>>
non_op_vars      == <<local_vars, peer_vars, pending_vars, sent_get_branch, sent_get_headers, recv_branch, recv_header>>
non_recv_vars    == <<local_vars, peer_vars, pending_vars, sent_vars>>
non_trace_vars   == <<connections, sent_vars, recv_vars>>
non_hd_q_vars    == <<connections, current_head, sent_vars, recv_vars>>
non_op_q_vars    == <<connections, current_head, sent_vars, recv_vars>>
non_phase_vars   == <<messages, greylist, non_trace_vars>>
non_pending_vars == <<local_vars, peer_vars, sent_vars, recv_vars, mem_size>>

\* all variables
vars == <<local_vars, peer_vars, pending_vars, sent_vars, recv_vars, mem_size>>

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

Option(s) == s \cup {NONE}

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

ToSet(seq)    == { seq[i] : i \in DOMAIN seq }

RECURSIVE AppendAll(_, _)
AppendAll(seq1, seq2) ==
    IF seq2 = <<>> THEN seq1
    ELSE AppendAll(Append(seq1, Head(seq2)), Tail(seq2))

\* remove the first occurence of [elem] from [seq]
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

Max_set(s) == Pick({ x \in s : \A y \in s : x >= y })

Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b


\* [2] Spec-specific helpers

N == Card(NODES)

\* block levels
Levels  == Nat \ {0}
Levels0 == Nat

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
block(hdr, ops) == [ header |-> hdr, ops |-> { op.op : op \in ops } ]
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

HashLevels == [ hash : Hashes, level : Levels ]
HeadersWithHash == [ header : Headers, hash : Hashes ]

\* operations
Ops == Nat
Operations == [ block_hash : Hashes, op : SUBSET Ops ]
OperationHashes == Int

\* blocks
Blocks == [ header : Headers, ops : SUBSET Ops ]
BlockOpHashes == [ block_hash : Hashes, op_hash : OperationHashes ]

\* history
History == Seq(Levels \X Hashes)
Locators == [ current_head : Headers, history : History ]

\* 

received_operations_block_hash(n, bh) == { op \in recv_operation[n] : op.block_hash = bh }

all_recv_operations_block_hash(bh) == UNION { received_operations_block_hash(n, bh) : n \in NODES }

\* all fetched data
fetched_hashes_node(n)  == { h.hash : h \in recv_header[n] }
fetched_headers_node(n) == { h.header : h \in recv_header[n] }

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

headers_with_hash(bh) == { p \in all_header_data : p.header = bh }

RECURSIVE descendant(_, _)
descendant(hd1, hd2) ==
    CASE hd1.fitness = hd2.fitness -> hd1 = hd2
      [] hd1.fitness < hd2.fitness ->
        LET bh == hash(hd2) IN
        \/ bh = hd1.predecessor
        \/ \E hd \in headers_with_hash(bh): descendant(hd, hd2)

\* only applied to sequences of headers and sets of operations of the same length
\* checks that hash of header matches the block hash in the operations and
\* that the hash of the operations matches the operations hash in the header
RECURSIVE Check(_, _)
Check(hds, ops) ==
    IF hds = <<>> THEN TRUE
    ELSE
        LET hd == Head(hds)
            op == Head(ops)
            check(h, o) ==
                \* header ops_hash matches hash of ops
                /\ h.ops_hash = hash(o.op)
                \* operations block_hash matches hash of block
                /\ hash(h) = o.block_hash
        IN
        /\ check(hd, op)
        /\ Check(Tail(hds), Tail(ops))

----

(***************)
(* Assumptions *)
(***************)

\* TODO

----

(************)
(* Messages *)
(************)

\* [1] Requests
\* [1.1] Good requests
GetCurrentBranchMessages == [ type : {"Get_current_branch"} ]
GetBlockHeadersMessages  == [ type : {"Get_block_headers"}, hashes : NESet(HashLevels) ]
GetOperationsMessages    == [ type : {"Get_operations"},    op_hashes : NESet(OperationHashes) ]
\* GetCheckpointMessages    == [ type : {"Get_checkpoint"} ]
\* GetPredHeaderMessages    == [ type : {"Get_predecessor_header"}, hash : Hashes, offset : Nat ]

GetMessages == GetCurrentBranchMessages \cup GetBlockHeadersMessages \cup GetOperationsMessages

\* [1.2] Request constructors
get_current_branch_msg    == [ type |-> "Get_current_branch" ]
get_block_headers_msg(hs) == [ type |-> "Get_block_headers", hashes    |-> hs ]
get_operations_msg(ohs)   == [ type |-> "Get_operations",    op_hashes |-> ohs ]

\* [1.3] Sets of request types
current_branch_msgs(n) == { msg \in messages[n] : msg.type = "Current_branch" }
block_header_msgs(n)   == { msg \in messages[n] : msg.type = "Block_header" }
operation_msgs(n)      == { msg \in messages[n] : msg.type = "Operation" }

\* [1.4] Request predicates
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
\* CheckpointMessages    == [ type : {"Checkpoint"},    from : NODES, hash : Hashes ]
\* PredHeaderMessages    == [ type : {"Pred_header"},   from : NODES, hash : Hashes, offset : Nat, header : Headers ]

ResponseMessages == CurrentBranchMessages \cup BlockHeaderMessages \cup OperationsMessages

current_branch_msg(n, l) == [ type |-> "Current_branch", from |-> n, locator   |-> l ]
block_header_msg(n, hd)  == [ type |-> "Block_header",   from |-> n, header    |-> hd ]
operation_msg(n, op)     == [ type |-> "Operation",      from |-> n, operation |-> op ]

\* [3] P2p messages
AdvertiseMessages   == [ type : {"Advertise"},  from : NODES, peers : NESet(NODES) ]
DisconnectMessages  == [ type : {"Disconnect"}, from : NODES ]
SwapAckMessages     == [ type : {"Swap_ack"},   from : NODES ]
SwapRequestMessages == [ type : {"Swap_req"},   from : NODES, peer : NODES ]

P2pMessages == AdvertiseMessages \cup DisconnectMessages \cup SwapRequestMessages \cup SwapAckMessages

\* node p2p messages

NodeAdvertiseMessages  == [ type : {"Advertise"}, peers : NESet(NODES) ]
NodeDisconnectMessages == [ type : {"Disconnect"} ]
NodeSwapAckMessages    == [ type : {"Swap_ack"},  peer : NODES ]
NodeSwapReqMessages    == [ type : {"Swap_req"},  peer : NODES ]

NodeP2pMessages == NodeAdvertiseMessages \cup NodeDisconnectMessages \cup NodeSwapAckMessages \cup NodeSwapReqMessages

advertise_msgs(n)  == { msg \in messages[n] : msg.type = "Advertise" }
disconnect_msgs(n) == { msg \in messages[n] : msg.type = "Disconnect" }
swap_req_msgs(n)   == { msg \in messages[n] : msg.type = "Swap_request" }
swap_ack_msgs(n)   == { msg \in messages[n] : msg.type = "Swap_ack" }

advertise_msg(n, ps) == [ type |-> "Advertise",    from |-> n, peers |-> ps ]
disconnect_msg(n)    == [ type |-> "Disconnect",   from |-> n ]
swap_req_msg(n, p)   == [ type |-> "Swap_request", from |-> n, peer |-> p ]
swap_ack_msg(n)      == [ type |-> "Swap_ack",     from |-> n ]

\* [4] All messages
Messages          == GetMessages \cup ResponseMessages \cup P2pMessages \cup NodeP2pMessages
BranchMessages    == { msg \in Messages : msg.type = "Current_branch" }
HeaderMessages    == { msg \in Messages : msg.type = "Block_header" }
OperationMessages == { msg \in Messages : msg.type = "Operation" }

----

(***********)
(* Actions *)
(***********)

\* [0] Action helpers

Send(n, msg) ==
    messages' = [ messages EXCEPT ![n] = @ \cup {msg} ]

Drop(msg) ==
    LET n == msg.from IN
    messages' = [ messages EXCEPT ![n] = @ \ {msg} ]

update_connections(ps)    == connections' = ps
update_current_head(hdwh) == current_head' = hdwh

incr_score(peer) == peer_score' = [ peer_score EXCEPT ![peer] = Min(@ + INCR_SCORE, MAX_SCORE) ]
decr_score(peer) == peer_score' = [ peer_score EXCEPT ![peer] = Max(@ - DECR_SCORE, 0) ]

\* [1] Request actions

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

\* [3] Bootstrapping node handles responses

HandleAdvertise == \E n \in connections :
    \E msg \in advertise_msgs(n) :
        \E ps \in NESet(msg.peers) :
            /\ connections' = connections \cup ps
            /\ UNCHANGED non_conn_vars

\* TODO is this correct?
HandleSwapRequest == \E n \in connections :
    \E msg \in swap_req_msgs(n) :
        /\ connections' = connections \ {msg.peer}
        /\ UNCHANGED non_conn_vars

HandleSwapAck == \E n \in connections :
    \E msg \in swap_ack_msgs(n) :
        /\ connections' = connections \ {n}
        /\ UNCHANGED non_conn_vars

HandleCurrentBranch == \E n \in connections :
    \E msg \in current_branch_msgs(n) :
        LET hist    == msg.locator.history
            curr_hd == msg.locator.current_head
        IN
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
HandleBlockHeader == \E n \in connections :
    \E msg \in block_header_msgs(n) :
        LET hd == msg.header
            h  == hash(hd)
        IN
        /\ h \in sent_get_headers[n]
        /\ hd \notin fetched_headers
        /\ Drop(msg)
        /\ recv_header' = [ recv_header EXCEPT ![n] = @ \cup {header_with_hash(hd, h)} ]
        /\ recv_branch' = [ recv_branch EXCEPT ![n] = @ \cup {h} ]
        /\ UNCHANGED <<greylist, non_recv_vars, recv_operation>>

\* bootstrapping node receives an Operation message
HandleOperation == \E n \in connections :
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

\* TODO P2p messages

\* [4] Block validation

\* TODO apply all at once?
\* nodes form blocks from fetched headers and operations that have been enqueued in their respective pipes
apply_block(hd, ops) ==
    LET b == block(hd, ops) IN
    /\ pending_headers'    = Tail(pending_headers)
    /\ pending_operations' = Tail(pending_operations)
    /\ chain'              = Cons(b, chain)
    /\ UNCHANGED non_pending_vars

ApplyBlock ==
    LET hds == pending_headers
        ops == pending_operations
    IN
    /\ hds /= <<>>
    /\ ops /= <<>>
    /\ Check(hds, ops)
    /\ LET hd == Head(hds)
           op == Head(ops)
        IN
        /\ op.block_hash = hash(hd)
        /\ apply_block(hd, ops)

\* [5] undesirable actions

\* [5.1] Timeout actions

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

\* TODO
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

\* [5.2] Punative actions

\* TODO peer_score = 0 => greylist
Greylist ==
    \E n \in connections : \E msg \in messages[n] :
        LET t == msg.type IN
        /\ n = msg.from
        /\ CASE t = "Current_branch" -> FALSE
             [] t = "Block_header" ->
                LET hd == msg.header IN
                \* send multiple headers at the same level
                \/ \E h \in recv_header[n] : h.header.level = hd.level
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
            \* p2p messages
              [] t = "Advertise" -> FALSE \* TODO
              [] t = "Advertise" -> FALSE \* TODO
              [] t = "Advertise" -> FALSE \* TODO
              [] t = "Advertise" -> FALSE \* TODO
        /\ greylist_node(n)

\* ban a peer
BanNode == \E n \in connections :
    /\ banned' = banned \cup {n}
    /\ update_connections(connections \ {n})
    \* TODO drop messages and data

----

(*********************)
(* Initial predicate *)
(*********************)

BootstrappingInit ==
    /\ banned             = {}
    /\ greylist           = {}
    /\ messages           = [ n \in NODES |-> {} ]
    /\ chain              = INIT_CHAIN
    /\ connections        = INIT_CONNECTIONS
    /\ current_head       = INIT_HEAD
    /\ peer_head          = [ n \in connections |-> INIT_HEAD ]
    /\ peer_score         = [ n \in connections |-> MAX_SCORE ]
    /\ earliest_hashes    = {}
    /\ target_hash        = NONE
    /\ target_level       = NONE
    /\ pending_headers    = <<>>
    /\ pending_operations = <<>>
    /\ sent_get_branch    = {}
    /\ sent_get_headers   = [ n \in NODES |-> {} ]
    /\ sent_get_ops       = [ n \in NODES |-> {} ]
    /\ recv_branch        = [ n \in NODES |-> {} ]
    /\ recv_head          = [ n \in NODES |-> {} ]
    /\ recv_header        = [ n \in NODES |-> {} ]
    /\ recv_operation     = [ n \in NODES |-> {} ]

MemInit == mem_size = 0

Init ==
    /\ MemInit
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

    \* Block application
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
    /\ banned             \in SUBSET NODES
    /\ greylist           \in SUBSET NODES
    /\ messages           \in [ NODES -> SUBSET (ResponseMessages \cup P2pMessages) ]
    /\ chain              \in Seq(Blocks)
    /\ connections        \in SUBSET NODES
    /\ current_head       \in Headers
    /\ peer_head          \in [ NODES -> Headers ]
    /\ peer_score         \in [ NODES -> Nat ]
    /\ earliest_hashes    \in SUBSET Hashes
    /\ target_hash        \in Option(Hashes)
    /\ target_level       \in Option(Levels)
    /\ pending_headers    \in Seq(HeadersWithHash)
    /\ pending_operations \in Seq(Operations)
    /\ sent_get_branch    \in SUBSET NODES
    /\ sent_get_headers   \in [ NODES -> SUBSET HashLevels ]
    /\ sent_get_ops       \in [ NODES -> SUBSET BlockOpHashes ]
    /\ recv_branch        \in [ NODES -> SUBSET HashLevels ]
    /\ recv_head          \in [ NODES -> SUBSET Headers ]
    /\ recv_header        \in [ NODES -> SUBSET HeadersWithHash ]
    /\ recv_operation     \in [ NODES -> SUBSET Operations ]

MemOK == mem_size \in Nat

TypeOK ==
    /\ MemOK
    /\ BootstrappingOK

\* [2] General safety properties

ConnectionSafety ==
    /\ num_peers <= MAX_PEERS
    /\ greylist \cap connections = {}

MessageSafety == \A n \in NODES :
    \/ n \in connections
    \/ messages[n] = {}

\* The node has seen a quorum of support for their current head
CurrentHeadIsAlwaysMajor ==
    \/ current_head = INIT_HEAD
    \/ 3 * Card({ n \in connections : current_head \in recv_header[n] }) > 2 * Card(connections)

\* TODO properties

Safety ==
    /\ TypeOK
    /\ ConnectionSafety
    /\ CurrentHeadIsAlwaysMajor

(**************)
(* Properties *)
(**************)

\* PeerConservation ==
\*     [][ IF \/ connections /= {}
\*            \/ greylist /= {}
\*         THEN connections \cup greylist = connections' \cup greylist'
\*         ELSE connections \cup greylist \subseteq connections' \cup greylist' ]_vars

\* fitness always increases
MonotonicFitness ==
    LET old_head  == current_head
        new_head  == current_head'
    IN
    [][ old_head /= new_head => old_head.header.fitness < new_head.header.fitness ]_vars

\* Liveness

\* Bootstrapping node always learns about local major branches
\* IfLocalMajorBranchExistsThenBootstrapppingWillHearAboutIt ==
\*     LET curr_hd == current_head IN
\*     \E hd \in major_headers :
\*         <>( \/ hd = curr_hd
\*             \/ hd.fitness < curr_hd.fitness )

\* Liveness ==
\*     /\ IfLocalMajorBranchExistsThenBootstrapppingWillHearAboutIt

==========================
