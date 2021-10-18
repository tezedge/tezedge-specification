---- MODULE Mempool_global ----

EXTENDS FiniteSets, Integers, Sequences, Utils

CONSTANTS
    INIT_PEERS,
    INIT_CONNECTIONS,
    INIT_PREDECESSOR,
    INIT_PREDECESSORS,
    MAX_HOPS,
    NONE

\* shell peers and messages
VARIABLES
    peers,              \* set of each node's peers
    connections,        \* set of each node's connections
    greylist,           \* set of each node's greylisted peers
    messages            \* queue of messages for each peer

shell_vars == <<peers, connections, greylist, messages>>

shell_non_msg_vars == <<peers, connections, greylist>>

\* prevalidators
VARIABLES
    predecessor,        \* the current head on which a dummy block is baked
    branch_delayed,     \* set of operations which have this classification
    branch_refused,     \* set of operations which have this classification
    refused,            \* set of operations which have this classification
    pending,            \* set of pending operations
    advertisement       \* set of operations to advertise

pv_vars == <<predecessor, branch_delayed, branch_refused, refused, pending, advertisement>>

pv_non_pending_vars   == <<predecessor, branch_delayed, branch_refused, refused, advertisement>>
pv_non_advertise_vars == <<predecessor, branch_delayed, branch_refused, refused, pending>>

\* mempool
VARIABLES
    known_valid,        \* list of operations which have been successfully pre-applied
    mp_pending          \* set of pending operations in mempool

mp_vars == <<known_valid, mp_pending>>

\* auxiliary
VARIABLES
    all_operations      \* set of all operations which have been generated

aux_vars == <<all_operations>>

\* all variables
vars == <<shell_vars, pv_vars, mp_vars, aux_vars>>

----

(* basic definitions *)

NODES == STRING
Nodes == DOMAIN INIT_CONNECTIONS

BlockHashes == Int

\* MAX_HOPS constrains the network topology
INSTANCE Topology WITH connections <- INIT_CONNECTIONS

INSTANCE Operations

Mempool == [ known_valid : Seq(Operations), pending : SUBSET Operations ]

mempool(kv, p) == [ known_valid |-> kv, pending |-> p ]

set_of_mempool(mp) == ToSet(mp.known_valid) \cup mp.pending

INSTANCE Messages

live_operations(n) == branch_delayed[n] \cup branch_refused[n] \cup refused[n] \cup ToSet(known_valid[n]) \cup mp_pending[n]

\* advertise current head
advertise_msg(n) ==
    [ type |-> "Head",
      from |-> n,
      contents |->
        <<predecessor[n], mempool(known_valid[n], advertisement[n] \cup mp_pending[n])>> ]

request_msg(n) == [ type |-> "GetHead", from |-> n ]

operation_msg(n, op) ==
    [ type |-> "Operation",
      from |-> n,
      contents |-> op ]

ops_request_msg(n, ohs) ==
    [ type |-> "GetOperations",
      from |-> n,
      contents |-> ohs ]

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
ASSUME Max_path_len(Nodes) <= MAX_HOPS

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

\* advertise current head
Advertise == \E n \in Nodes :
    /\ advertisement[n] /= {}
    /\ Broadcast(advertise_msg(n))
    /\ advertisement' = [ advertisement EXCEPT ![n] = {} ]
    /\ UNCHANGED <<shell_non_msg_vars, pv_non_advertise_vars, mp_vars, aux_vars>>

add_op(op) ==
    all_operations' = [ all_operations EXCEPT !.next = @ + 1, !.ops = @ \cup {op} ]

add_pending(n, op) ==
    pending' = [ pending EXCEPT ![n] = @ \cup {op} ]

flush(n) ==
    /\ branch_delayed' = [ branch_delayed EXCEPT ![n] = {} ]
    /\ branch_refused' = [ branch_refused EXCEPT ![n] = {} ]
    /\ UNCHANGED refused
    /\ advertisement'  = [ advertisement  EXCEPT ![n] = {} ]

declassify(n, mp) ==
    /\ known_valid' = [ known_valid EXCEPT ![n] = mp.known_valid ]
    /\ mp_pending'  = [ mp_pending  EXCEPT ![n] = mp.pending ]
    /\ flush(n)
    /\ pending' = [ pending EXCEPT ![n] = @ \cup live_operations(n) ]

HandleHead(n, from, pmp) ==
    LET pred == pmp[1]
        mp   == pmp[2]
    IN
    /\ Drop(n, from)
    /\ CASE pred = predecessor[n] ->
                /\ pending' = [ pending EXCEPT ![n] = @ \cup set_of_mempool(mp) ]
                /\ UNCHANGED <<pv_non_pending_vars, mp_vars>>
         [] pred > predecessor[n] ->
                /\ predecessor' = [ predecessor EXCEPT ![n] = pred ]
                /\ declassify(n, mp)
         [] pred < predecessor[n] -> UNCHANGED <<pv_vars, mp_vars>>
    /\ UNCHANGED <<shell_non_msg_vars, aux_vars>>

HandleGetHead(n, from) ==
    LET msg == advertise_msg(n) IN
    /\ Send(msg, from)
    /\ UNCHANGED <<shell_non_msg_vars, pv_vars, mp_vars, aux_vars>>

\* consume message and add operation to [pending]
HandleOperation(n, from, op) ==
    /\ Drop(n, from)
    /\ add_pending(n, op)
    /\ UNCHANGED <<shell_non_msg_vars, pv_non_pending_vars, mp_vars, aux_vars>>

HandleGetOperations(n, from, ohs) == {} \* TODO

HandleMessage == \E m, n \in Nodes :
    /\ m /= n
    /\ messages[n][m] /= <<>>
    /\ LET msg == Head(messages[n][m])
           t   == msg.type
       IN
       CASE t = "Head"          -> HandleHead(n, m, msg.contents)
         [] t = "GetHead"       -> HandleGetHead(n, m)
         [] t = "Operation"     -> HandleOperation(n, m, msg.contents)
         [] t = "GetOperations" -> HandleGetOperations(n, m, msg.contents)

\* TODO
\* ChangePredecessor

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

\* all pending operations are preapplied
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
    /\ UNCHANGED <<shell_vars, known_valid, aux_vars>>

ApplyMempool == \E n \in Nodes :
    /\ mp_pending /= {}
    /\ mp_pending'  = [ mp_pending  EXCEPT ![n] = {} ]
    /\ known_valid' = [ known_valid EXCEPT ![n] = @ \cup ToSeq(mp_pending[n]) ]
    /\ UNCHANGED <<shell_vars, pv_vars, aux_vars>>

\* a new operation is introduced into a node's pending collection
NewOperation == \E n \in Nodes :
    \E op \in Operations :
        /\ op.hash = all_operations.next
        /\ add_op(op)
        /\ add_pending(n, op)
        /\ UNCHANGED <<shell_vars, pv_non_pending_vars, mp_vars>>

----

(* Specification *)

EmptySet == [ n \in Nodes |-> {} ]

Init ==
    /\ peers           = INIT_PEERS
    /\ connections     = INIT_CONNECTIONS
    /\ greylist        = EmptySet
    /\ messages        = [ n \in Nodes |-> [ m \in connections[n] |-> <<>> ] ]
    /\ predecessor     = INIT_PREDECESSORS
    /\ branch_delayed  = EmptySet
    /\ branch_refused  = EmptySet
    /\ refused         = EmptySet
    /\ pending         = EmptySet
    /\ advertisement   = EmptySet
    /\ known_valid     = [ n \in Nodes |-> <<>> ]
    /\ mp_pending      = EmptySet
    /\ all_operations  = [ next |-> 0, ops |-> {} ]
    
Next == {}

\* all operations must have unique hashes
OperationHashUniqueness ==
    { ops \in all_operations.ops \X all_operations.ops :
        ops[1].hash = ops[2].hash /\ ops[1] /= ops[2] } = {}

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

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ []OperationHashUniqueness
    /\ []ProtocolConsistency

----

(* Properties *)

TypeOK ==
    /\ peers           \in [ Nodes -> SUBSET Nodes ]
    /\ connections     \in [ Nodes -> SUBSET Nodes ]
    /\ greylist        \in [ Nodes -> SUBSET Nodes ]
    /\ messages        \in [ Nodes -> [ SUBSET Nodes -> Seq(Messages) ] ]
    /\ predecessor     \in [ Nodes -> BlockHashes ]
    /\ branch_delayed  \in [ Nodes -> SUBSET Operations ]
    /\ branch_refused  \in [ Nodes -> SUBSET Operations ]
    /\ refused         \in [ Nodes -> SUBSET Operations ]
    /\ pending         \in [ Nodes -> SUBSET Operations ]
    /\ advertisement   \in [ Nodes -> SUBSET Operations ]
    /\ known_valid     \in [ Nodes -> Seq(Operations) ]
    /\ mp_pending      \in [ Nodes -> SUBSET Operations ]
    /\ all_operations  \in { r \in [ next : OpHashes, ops : SUBSET Operations ] : r.next = Cardinality(r.ops) }

===============================
