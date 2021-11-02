---- MODULE Mempool_global ----

EXTENDS FiniteSets, Integers, Sequences, Utils

CONSTANTS
    INIT_PEERS,         \* initial peers
    INIT_CONNECTIONS,   \* initial connections
    INIT_PREDECESSOR,   \* initial predecessors/heads
    MAX_HOPS,           \* maximum number of hops between any nodes along the shortest path
    MIN_CONNECTIONS,    \* minimum number of connections
    MAX_CONNECTIONS,    \* maximum number of connections
    MIN_ENDORSEMENTS,   \* minimum number of endorsements needed to bake a block
    NONE                \* null value

\* to bound the models
CONSTANTS
    MAX_HASH

\* shell
VARIABLES
    peers,              \* set of each node's peers
    connections,        \* set of each node's connections
    messages            \* queue of messages for each peer

shell_vars == <<peers, connections, messages>>
shell_non_msg_vars  == <<peers, connections>>

\* prevalidator
VARIABLES
    block_ops,          \* sequence of each node's blocks
    predecessor,        \* the current head on which a dummy block is baked
    branch_delayed,     \* set of operations which are for a future block on this branch
    branch_refused,     \* set of operations which are for a different branch
    refused,            \* set of operations which are not valid on any branch
    pending,            \* set of pending operations
    advertisement       \* set of operations to advertise

pv_vars == <<block_ops, predecessor, branch_delayed, branch_refused, refused, pending, advertisement>>
pv_non_pending_vars   == <<block_ops, predecessor, branch_delayed, branch_refused, refused, advertisement>>
pv_non_advertise_vars == <<block_ops, predecessor, branch_delayed, branch_refused, refused, pending>>

\* mempool
VARIABLES
    known_valid,        \* list of operations which have been successfully pre-applied
    mp_pending          \* set of pending operations in mempool

mp_vars == <<known_valid, mp_pending>>

\* auxiliary
VARIABLES
    all_operations,     \* set of all operations which have been generated
    all_blocks          \* set of all block hashes

aux_vars == <<all_operations, all_blocks>>

\* all variables
vars == <<shell_vars, pv_vars, mp_vars, aux_vars>>

----

(* basic definitions *)

NODES == STRING
Nodes == DOMAIN INIT_CONNECTIONS

\* MAX_HOPS constrains the network topology
INSTANCE Topology WITH connections <- INIT_CONNECTIONS

INSTANCE Operations

live_operations(n) ==
    branch_delayed[n] \cup branch_refused[n] \cup refused[n] \cup ToSet(known_valid[n]) \cup mp_pending[n]

nonrefused_operations(n) ==
    branch_delayed[n] \cup branch_refused[n] \cup advertisement[n] \cup ToSet(known_valid[n]) \cup mp_pending[n]

Mempool == [ known_valid : Seq(Operations), pending : SUBSET Operations ]

mempool(kv, p) == [ known_valid |-> kv, pending |-> p ]

set_of_mempool(mp) == ToSet(mp.known_valid) \cup mp.pending

empty_mempool == mempool(<<>>, {})

INSTANCE Blocks

INSTANCE Messages

\* advertise current head
head_msg(n) ==
    [ type |-> "Head",
      from |-> n,
      contents |->
        <<predecessor[n], mempool(known_valid[n], advertisement[n] \cup mp_pending[n])>> ]

new_head_msg(n, blk) ==
    [ type |-> "Head",
      from |-> n,
      contents |-> <<blk, empty_mempool>> ]

get_head_msg(n) == [ type |-> "GetHead", from |-> n ]

operation_msg(n, op) ==
    [ type |-> "Operation",
      from |-> n,
      contents |-> op ]

\* classification
isPending(n, op) == op \in pending[n]
isApplied(n, op) == op \in ToSet(known_valid[n]) \cup mp_pending[n]
isBranchD(n, op) == op \in branch_delayed[n]
isBranchR(n, op) == op \in branch_refused[n]
isRefused(n, op) == op \in refused[n]

classification(n, op) ==
    CASE isPending(n, op) -> "Pending"
      [] isApplied(n, op) -> "Applied"
      [] isBranchD(n, op) -> "Branch_delayed"
      [] isBranchR(n, op) -> "Branch_refused"
      [] isRefused(n, op) -> "Refused"

isEndorsement(op) == op.type = "Endorsement"

----

(* Assumptions *)

\* the longest minimal path from any node to another is <= MAX_HOPS
ASSUME lte(Max_path_len(Nodes), MAX_HOPS)

\* connections are symmetric
ASSUME
    \A x, y \in Nodes :
        y \in INIT_CONNECTIONS[x] <=> x \in INIT_CONNECTIONS[y]

----

(* Actions *)

Send(msg, rcvr) ==
    LET sndr == msg.from IN
    messages' = [ messages EXCEPT ![rcvr][sndr] = Append(@, msg) ]

Drop(n, from) ==
    messages' = [ messages EXCEPT ![n][from] = Tail(@) ]

RECURSIVE broadcast(_, _, _)
broadcast(msg, rs, acc) ==
    LET s == msg.from IN
    IF rs = {} THEN acc
    ELSE
        LET r == Pick(rs) IN
        broadcast(msg, rs \ {r}, [ acc EXCEPT ![r][s] = Append(@, msg) ])

Broadcast(msg) ==
    LET sndr == msg.from IN
    messages' = broadcast(msg, connections[sndr], messages)

connect(m, n) ==
    /\ connections' = [ connections EXCEPT ![m] = @ \cup {n}, ![n] = @ \cup {m} ]
    /\ messages'    = [ messages    EXCEPT ![m] = @ @@ n :> <<>>, ![n] = @ @@ m :> <<>> ]

disconnect(m, n) ==
    /\ connections' = [ connections EXCEPT ![m] = @ \ {n}, ![n] = @ \ {m} ]
    /\ messages'    = [ messages    EXCEPT ![m] = Dom_drop(@, n), ![n] = Dom_drop(@, m) ]

Connect == \E n \in Nodes : \E m \in peers[n] :
    /\ Cardinality(connections[m]) < MAX_CONNECTIONS
    /\ Cardinality(connections[n]) < MAX_CONNECTIONS
    /\ connect(m, n)
    /\ UNCHANGED <<peers, pv_vars, mp_vars, aux_vars>>

Disconnect == \E n \in Nodes : \E m \in connections[n] :
    /\ Cardinality(connections[m]) > MIN_CONNECTIONS
    /\ Cardinality(connections[n]) > MIN_CONNECTIONS
    /\ disconnect(m, n)
    /\ UNCHANGED <<peers, pv_vars, mp_vars, aux_vars>>

\* advertise current head
Advertise == \E n \in Nodes :
    /\ advertisement[n] /= {}
    /\ Broadcast(head_msg(n))
    /\ advertisement' = [ advertisement EXCEPT ![n] = {} ]
    /\ UNCHANGED <<shell_non_msg_vars, pv_non_advertise_vars, mp_vars, aux_vars>>

add_op(op) ==
    all_operations' = [ all_operations EXCEPT !.next = @ + 1, !.ops = @ \cup {op} ]

add_block(blk) ==
    all_blocks' = [ all_blocks EXCEPT !.next = @ + 1, !.blocks = @ \cup {blk} ]

add_pending(n, op) ==
    pending' = [ pending EXCEPT ![n] = @ \cup {op} ]

flush(n) ==
    /\ branch_delayed' = [ branch_delayed EXCEPT ![n] = {} ]
    /\ branch_refused' = [ branch_refused EXCEPT ![n] = {} ]
    /\ advertisement'  = [ advertisement  EXCEPT ![n] = {} ]
    /\ UNCHANGED <<block_ops, refused>>

\* [mp] operations are included into [n]'s mempool and all other operations are moved back to pending
declassify(n, mp) ==
    /\ flush(n)
    /\ known_valid' = [ known_valid EXCEPT ![n] = mp.known_valid ]
    /\ mp_pending'  = [ mp_pending  EXCEPT ![n] = mp.pending ]
    /\ pending'     = [ pending     EXCEPT ![n] = @ \cup nonrefused_operations(n) ]

reclassify(n) ==
    LET p == branch_delayed[n] \cup branch_refused[n] IN
    /\ pending'        = [ pending        EXCEPT ![n] = @ \cup p ]
    /\ branch_delayed' = [ branch_delayed EXCEPT ![n] = {} ]
    /\ branch_refused' = [ branch_refused EXCEPT ![n] = {} ]
    /\ advertisement'  = [ advertisement  EXCEPT ![n] = @ \cup ToSet(known_valid[n]) \cup mp_pending[n] ]
    /\ mp_pending'     = [ mp_pending     EXCEPT ![n] = {} ]
    /\ known_valid'    = [ known_valid    EXCEPT ![n] = <<>> ]
    /\ UNCHANGED <<block_ops, refused>>

\* a node requests the head of a peer
RequestHead == \E n \in Nodes :
    \E m \in connections[n] :
        LET msg == get_head_msg(n) IN
        /\ Send(msg, m)
        /\ UNCHANGED <<shell_non_msg_vars, pv_vars, mp_vars, aux_vars>>

\* [n] handles to an advertised head
HandleHead(n, from, pmp) ==
    LET pred == pmp[1]
        mp   == pmp[2]
    IN
    /\ Drop(n, from)
    /\ CASE pred.hash = predecessor[n].hash ->
                LET new_ops == set_of_mempool(mp) \ live_operations(n) IN
                /\ pending' = [ pending EXCEPT ![n] = @ \cup new_ops ]
                /\ UNCHANGED <<pv_non_pending_vars, mp_vars>>
         [] pred.hash > predecessor[n].hash ->
                /\ block_ops'   = [ block_ops   EXCEPT ![n] = @ \cup block_ops[from] ]
                /\ predecessor' = [ predecessor EXCEPT ![n] = pred ]
                /\ declassify(n, mp)
         [] pred.hash < predecessor[n].hash -> UNCHANGED <<pv_vars, mp_vars>>
    /\ UNCHANGED <<shell_non_msg_vars, aux_vars>>

\* [n] responds to a head request
HandleGetHead(n, from) ==
    LET msg == head_msg(n) IN
    /\ Send(msg, from)
    /\ UNCHANGED <<shell_non_msg_vars, pv_vars, mp_vars, aux_vars>>

\* consume message and add operation to [pending] unless outdated
HandleOperation(n, from, op) ==
    /\ Drop(n, from)
    /\ \/ /\ op \notin live_operations(n)
          /\ add_pending(n, op)
       \/ UNCHANGED pending
    /\ UNCHANGED <<shell_non_msg_vars, pv_non_pending_vars, mp_vars, aux_vars>>

\* a node handles one of their messages
HandleMessage == \E n \in Nodes : \E m \in connections[n] :
    /\ messages[n][m] /= <<>>
    /\ LET msg == Head(messages[n][m])
           t   == msg.type
       IN
       CASE t = "Head"      -> HandleHead(n, m, msg.contents)
         [] t = "GetHead"   -> HandleGetHead(n, m)
         [] t = "Operation" -> HandleOperation(n, m, msg.contents)

\* pending operations are preapplied and classified
RECURSIVE preapply(_, _, _, _, _, _, _, _)
preapply(n, ops, cs, app, brd, brr, ref, adv) ==
    IF ops = {} THEN <<app, brd, brr, ref, adv>>
    ELSE
        LET op      == Pick(ops)
            c       == Head(cs)
            rem_ops == ops \ {op}
            rem_cs  == Tail(cs)
        IN
        CASE
          \* applied
              c = 1 ->
                LET new_app == [ app EXCEPT ![n] = @ \cup {op} ]
                    new_adv == [ adv EXCEPT ![n] = @ \cup {op} ]
                IN
                preapply(n, rem_ops, rem_cs, new_app, brd, brr, ref, new_adv)
          \* branch_delayed
          [] c = 2 ->
                LET new_brd == [ brd EXCEPT ![n] = @ \cup {op} ]
                    new_adv == IF isEndorsement(op)
                               THEN [ adv EXCEPT ![n] = @ \cup {op} ]
                               ELSE adv
                IN
                preapply(n, rem_ops, rem_cs, app, new_brd, brr, ref, new_adv)
          \* branch_refused
          [] c = 3 ->
                LET new_brr == [ brr EXCEPT ![n] = @ \cup {op} ] IN
                preapply(n, rem_ops, rem_cs, app, brd, new_brr, ref, adv)
          \* refused
          [] c = 4 ->
                LET new_ref == [ ref EXCEPT ![n] = @ \cup {op} ] IN
                preapply(n, rem_ops, rem_cs, app, brd, brr, new_ref, adv)

\* a node preapplies all pending operations and moves some to the mempool
PreapplyPending == \E n \in Nodes :
    /\ pending[n] /= {}
    /\ \E cs \in SeqOfLen(1..4, Cardinality(pending[n])) :
            LET res == preapply(n, pending[n], cs, mp_pending, branch_delayed, branch_refused, refused, advertisement) IN
            /\ mp_pending'     = res[1]
            /\ branch_delayed' = res[2]
            /\ branch_refused' = res[3]
            /\ refused'        = res[4]
            /\ advertisement'  = res[5]
            /\ UNCHANGED predecessor
    /\ pending' = [ pending EXCEPT ![n] = {} ]
    /\ UNCHANGED <<shell_vars, block_ops, known_valid, aux_vars>>

apply(n, tfs) ==
    LET RECURSIVE _apply(_, _, _, _)
        _apply(ops, ttfs, acc_t, acc_f) ==
            IF ttfs = <<>> THEN <<acc_t, acc_f>>
            ELSE
                LET op == Pick(ops) IN
                IF Head(ttfs) THEN
                    _apply(ops \ {op}, Tail(ttfs), Append(acc_t, op), acc_f)
                ELSE
                    _apply(ops \ {op}, Tail(ttfs), acc_t, acc_f \cup {op})
    IN
    _apply(mp_pending[n], tfs, <<>>, {})

\* a node applies their pending mempool operations
\* - some are added to [known_valid]
\* - some are returned to [pending]
ApplyMempool == \E n \in Nodes :
    /\ mp_pending[n] /= {}
    /\ \E tfs \in SeqOfLen(BOOLEAN, Cardinality(mp_pending[n])) :
            LET res    == apply(n, tfs)
                new_kv == res[1]
                pnd    == res[2]
            IN
            /\ pending'     = [ pending     EXCEPT ![n] = @ \cup pnd ]
            /\ mp_pending'  = [ mp_pending  EXCEPT ![n] = {} ]
            /\ known_valid' = [ known_valid EXCEPT ![n] = @ \o new_kv ]
    /\ UNCHANGED <<shell_vars, pv_non_pending_vars, aux_vars>>

get_hash(op) == op.hash
num_endorsements(n) == Cardinality(Map_set(ToSet(known_valid[n]), isEndorsement))

\* a node bakes a new block
BakeBlock == \E n \in Nodes :
    LET ops == Map(get_hash, known_valid[n])
        blk == block(all_blocks.next, ops)
    IN
    /\ num_endorsements(n) >= MIN_ENDORSEMENTS
    /\ mp_pending[n] = {}
    /\ block_ops'   = [ block_ops   EXCEPT ![n] = @ \cup ToSet(ops) ]
    /\ predecessor' = [ predecessor EXCEPT ![n] = blk ]
    /\ add_block(blk)
    /\ reclassify(n)
    /\ Broadcast(new_head_msg(n, blk))
    /\ UNCHANGED <<shell_non_msg_vars, all_operations>>

\* a new operation is introduced into a node's pending collection
NewOperation == \E n \in Nodes :
    \E op \in OperationsWithHash(all_operations.next) :
        /\ add_op(op)
        /\ add_pending(n, op)
        /\ UNCHANGED <<shell_vars, pv_non_pending_vars, mp_vars, all_blocks>>

----

(* Specification *)

EmptySet == [ n \in Nodes |-> {} ]
N == Cardinality({ INIT_PREDECESSOR[n] : n \in Nodes })

Init ==
    (* shell *)
    /\ peers           = INIT_PEERS
    /\ connections     = INIT_CONNECTIONS
    /\ messages        = [ n \in Nodes |-> [ m \in connections[n] |-> <<>> ] ]
    (* prevalidator *)
    /\ block_ops       = [ n \in Nodes |-> ToSet(INIT_PREDECESSOR[n].ops) ]
    /\ predecessor     = INIT_PREDECESSOR
    /\ branch_delayed  = EmptySet
    /\ branch_refused  = EmptySet
    /\ refused         = EmptySet
    /\ pending         = EmptySet
    /\ advertisement   = EmptySet
    (* mempool *)
    /\ known_valid     = [ n \in Nodes |-> <<>> ]
    /\ mp_pending      = EmptySet
    (* auxiliary *)
    /\ all_operations  = [ next |-> 0, ops |-> {} ]
    /\ all_blocks      = [ next |-> N,
                           blocks |-> { INIT_PREDECESSOR[n] : n \in Nodes } ]

Next ==
    \* \/ Connect
    \* \/ Disconnect
    \/ Advertise
    \/ RequestHead
    \/ HandleMessage
    \/ PreapplyPending
    \/ ApplyMempool
    \/ NewOperation
    \/ BakeBlock

(* Constraints *)

\* on top of the same predecessor, the protocol makes consistent decisions
ProtocolConsistency == \A m, n \in Nodes :
    predecessor[m] = predecessor[n] =>
        \A op \in live_operations(m) \cap live_operations(n) :
            LET c1 == classification(m, op)
                c2 == classification(n, op)
            IN
            \/ c1 = "Pending"
            \/ c2 = "Pending"
            \/ c1 = c2

Constraints == []ProtocolConsistency

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ Constraints

----

(* Safety properties *)

TypeOK ==
    (* shell *)
    /\ peers           \in [ Nodes -> SUBSET Nodes ]
    /\ connections     \in [ Nodes -> SUBSET Nodes ]
    \* messages
    /\ \A n \in Nodes : messages[n] \in [ connections[n] -> Seq(Messages) ]
    (* prevalidator *)
    /\ block_ops       \in [ Nodes -> SUBSET OpHashes ]
    /\ predecessor     \in [ Nodes -> Blocks ]
    /\ branch_delayed  \in [ Nodes -> SUBSET Operations ]
    /\ branch_refused  \in [ Nodes -> SUBSET Operations ]
    /\ refused         \in [ Nodes -> SUBSET Operations ]
    /\ pending         \in [ Nodes -> SUBSET Operations ]
    /\ advertisement   \in [ Nodes -> SUBSET Operations ]
    (* mempool *)
    /\ known_valid     \in [ Nodes -> Seq(Operations) ]
    /\ mp_pending      \in [ Nodes -> SUBSET Operations ]
    (* auxiliary *)
    /\ all_operations  \in { r \in [ next : OpHashes, ops : SUBSET Operations ] : r.next = Cardinality(r.ops) }
    /\ all_blocks      \in { r \in [ next : BlockHashes, blocks : SUBSET Blocks ] : r.next = Cardinality(r.blocks) }

\* connection symmetry
ConnectionSymmetry == \A m, n \in Nodes : n \in connections[m] <=> m \in connections[n]

\* operations have unique classifications
ClassificationDisjointness == \A n \in Nodes :
    disjoint_n(<<pending[n], branch_delayed[n], branch_refused[n], refused[n], mp_pending[n], ToSet(known_valid[n])>>)

----

(* Liveness properties *)

\* nodes with the same predecessors will eventually classify operations the same way
OperationClassification == \A m, n \in Nodes :
    predecessor[m] = predecessor[n] ~>
        \/ predecessor[m] /= predecessor[n]
        \/ \A op \in live_operations(m) \cap live_operations(n) :
                classification(m, op) = classification(n, op)

\* classification sets are monotone increasing until predecessor changes

BranchDelayedMonotonicity == [][ \A n \in Nodes :
    \/ predecessor[n] /= predecessor'[n]
    \/ branch_delayed[n] \subseteq branch_delayed'[n] ]_vars

BranchRefusedMonotonicity == [][ \A n \in Nodes :
    \/ predecessor[n] /= predecessor'[n]
    \/ branch_refused[n] \subseteq branch_refused'[n] ]_vars

RefusedMonotonicity == [][ \A n \in Nodes : refused[n] \subseteq refused'[n] ]_vars

\* endorsements are propagated to all nodes
EndorsementPropagation == \A n \in Nodes :
    LET endorsements == { op \in all_operations.ops :
            /\ isEndorsement(op)
            /\ \E m \in Nodes : op \in block_ops[m] }
    IN
    \A op \in [ type : {"Endorsement"}, hash : 0..MAX_HASH ] :
        op \in endorsements ~> op \in block_ops[n]

\* "fittest" blocks are propagated to all nodes
BlockPropagation ==
    LET Max_hash_block(blks) == CHOOSE b \in blks :
            \/ blks = {b}
            \/ b.hash > Max({ bb.hash : bb \in blks \ {b} })
        preds == { predecessor[m] : m \in Nodes }
        blk   == Max_hash_block(preds)
    IN
    <>( \/ Max_hash_block({ predecessor[m] : m \in Nodes }).hash > blk.hash
        \/ \A n \in Nodes : predecessor[n] = blk )


\* Tuesday - Emmy* & mempool spec presentation
\* Zura - use & review new architecture

===============================
