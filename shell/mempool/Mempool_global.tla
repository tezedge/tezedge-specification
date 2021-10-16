---- MODULE Mempool_global ----

EXTENDS FiniteSets, Integers, Sequences, Utils

CONSTANTS
    INIT_PEERS,
    INIT_CONNECTIONS,
    INIT_PREDECESSOR,
    INIT_LIVE_BLOCKS,
    INIT_LIVE_OPERATIONS,
    INIT_PREDECESSORS,
    MIN_OPS_PER_BLOCK,
    MAX_OPS_PER_BLOCK,
    MAX_HOPS,
    NONE

\* shell peers and messages
VARIABLES
    peers,              \* set of each node's peers
    connections,        \* set of each node's connections
    greylist,           \* set of each node's greylisted peers
    messages            \* queue of messages for each peer

shell_vars == <<peers, connections, greylist, messages>>

\* prevalidators
VARIABLES
    predecessor,        \* the current head on which a dummy block is baked
    branch_delayed,     \* set of operations which have this classification
    branch_refused,     \* set of operations which have this classification
    refused,            \* set of operations which have this classification
    pending,            \* set of operations TODO
    advertisement       \* set of operations to advertise

pv_vars == <<predecessor, branch_delayed, branch_refused, refused, pending, advertisement>>

pv_non_pending_vars == <<predecessor, branch_delayed, branch_refused, refused, advertisement>>

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

NODES == STRING
Nodes == DOMAIN INIT_CONNECTIONS

BlockHashes == Int

\* MAX_HOPS constrains the network topology
INSTANCE Topology WITH connections <- INIT_CONNECTIONS

INSTANCE Operations

Mempool == [ known_valid : Seq(Operations), pending : SUBSET Operations ]

INSTANCE Messages

live_operations(n) == branch_delayed[n] \cup branch_refused[n] \cup refused[n] \cup known_valid[n] \cup mp_pending[n]

mempool(kv, p) == [ known_valid |-> kv, pending |-> p ]

advertise_msg(n) ==
    [ type |-> "Advertise",
      from |-> n,
      contents |-> mempool(known_valid[n], advertisement[n] \cup mp_pending[n]) ]

request_msg(n) == [ type |-> "Request", from |-> n ]

operation_msg(n, op) ==
    [ type |-> "Operation",
      from |-> n,
      contents |-> op ]
----

(* Assumptions *)

\* the longest minimal path from any node to another is <= MAX_HOPS
ASSUME Max_path_len(Nodes) <= MAX_HOPS

----

(* Actions *)

Send(msg, rcvr) ==
    LET sndr == msg.from IN
    messages' = [ messages EXCEPT ![rcvr][sndr] = Append(@, msg) ]

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

\* what to do with advertisement?
Advertise == \E n \in Nodes :
    /\ advertisement[n] /= {}
    /\ Broadcast(advertise_msg(n))
    /\ UNCHANGED <<>> \* TODO

\* TODO
\* ChangePredecessor

\* TODO
\* PreapplyPending

add_op(op) ==
    all_operations' = [ all_operations EXCEPT !.next = @ + 1, !.ops = @ \cup {op} ]

add_pending(n, op) ==
    pending' = [ pending EXCEPT ![n] = @ \cup {op}]

add_bd(n, op) ==
    branch_delayed' = [ branch_delayed EXCEPT ![n] = @ \cup {op} ]

add_br(n, op) ==
    branch_refused' = [ branch_refused EXCEPT ![n] = @ \cup {op} ]

add_refused(n, op) ==
    refused' = [ refused EXCEPT ![n] = @ \cup {op} ]

Applied(n, op) ==
    /\ op.hash \notin live_operations(n)
    \* add to pending?
    \* add to known_valid
    /\ {}
    /\ UNCHANGED <<>> \* TODO

Branch_delayed(n, op) ==
    /\ op.hash \notin live_operations(n)
    \* add to pending?
    \* add to mp_pending?
    /\ branch_delayed' = [ branch_delayed EXCEPT ![n] = @ \cup {op} ]
    /\ UNCHANGED <<>> \* TODO

Branch_refused(n, op) ==
    /\ op.hash \notin live_operations(n)
    \* add to pending?
    /\ branch_refused' = [ branch_refused EXCEPT ![n] = @ \cup {op} ]
    /\ UNCHANGED <<>> \* TODO

Refused(n, op) ==
    /\ refused' = [ refused EXCEPT ![n] = @ \cup {op} ]
    /\ UNCHANGED <<>> \* TODO

Outdated(n, op) ==
    /\ UNCHANGED <<>> \* TODO

HandleAdvertise(n, from, mp) == {} \* TODO
    \* tail(messages)
    \* incorporate into pending or mempool?

HandleOperation(n, from, op) == {} \* TODO
    \* tail(messages)
    /\ \/ Applied(n, op)
       \/ Branch_delayed(n, op)
       \/ Branch_refused(n, op)
       \/ Refused(n, op)
       \/ Outdated(n, op)

HandleRequest(n, from) ==
    LET msg == advertise_msg(n) IN
    /\ Send(msg, from)
    /\ UNCHANGED <<>> \* TODO

HandleMessage == \E m, n \in Nodes :
    /\ m /= n
    /\ messages[n][m] /= <<>>
    /\ LET msg == Head(messages[n][m])
           t   == msg.type
       IN
       CASE t = "Advertise" -> HandleAdvertise(n, m, msg.contents)
         [] t = "Operation" -> HandleOperation(n, m, msg.contents)
         [] t = "Request"   -> HandleRequest(n, m)

\* a new operation is introduced
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
    /\ peers = INIT_PEERS
    /\ connections = INIT_CONNECTIONS
    /\ greylist = EmptySet
    /\ messages = [ n \in Nodes |-> [ m \in connections[n] |-> <<>> ] ]

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

\* TODO
\* on top of the same predecessor, the protocol makes consistent decisions
ProtocolConsistency == TRUE

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
