---- MODULE Mempool ----

EXTENDS FiniteSets, Integers, Sequences

CONSTANTS
    INIT_PEERS,
    INIT_CONNECTIONS,
    INIT_PREDECESSOR,
    INIT_LIVE_BLOCKS,
    INIT_LIVE_OPERATIONS

\* shell peers and messages
VARIABLES
    peers,              \* set of all known peers
    connections,        \* set of peer with which the node exchanges messages
    greylist,           \* set of greylisted peers
    outgoing,           \* queue of outgoing messages for each peer
    incoming,           \* queue of incoming messages for each peer
    all_operations      \* set of all operations which have been generated

\* prevalidator
VARIABLES
    predecessor,        \* the current head on which a dummy block is baked
    live_blocks,        \* set of hashes of all blocks in current branch
    live_operations,    \* set of hashes of all operations in [live_blocks]
    branch_delayed,     \* set of operations which have this classification
    branch_refused,     \* set of operations which have this classification
    refused,            \* set of operations which have this classification
    fetching,           \* set of operations which are actively being fetched from the db
    pending,            \* set of operations TODO
    in_mempool,         \* set of operations which have been pre-applied and added to the mempool
    banned,             \* set of banned operation hashes
    advertisement,      \* set of operations to advertise
    applied

\* mempool
VARIABLES
    known_valid,        \* list of operations which have been successfully pre-applied
    mp_pending          \* set of pending operations in mempool

vars == <<>>

Nodes == STRING

----

ToSet(seq) == { seq[i] : i \in DOMAIN seq }

----

Seen_ops == fetching \cup pending \cup banned \cup branch_delayed \cup branch_refused \cup refused \cup known_valid \cup mp_pending

(*
The mempool manages a *validation state* based upon the current head chosen by the validation subsystem
- each time the mempool receives an operation
  - it tries to classify it on top of the current validation state
    - if the operation is applied successfully
      - the validation state is updated
      - the operation is classified as `Applied`
      - the operation is propagated to peers
    - else, the handling of the operation depends on its *classification* which is detailed below
      - given an operation, its classification may change if the head changes
      - when the validation subsystem switches its head
        - it notifies the mempool with the new `live_blocks` and `live_operations`, and
        - triggers a `flush` of the mempool
          - every classified operation which is *anchored* on a *live* block and which is not in the
            `live_operations` is set as `pending`, meaning they are waiting to be classified again
          - an exception is made for operations classified as `Branch_refused`
            - those operations are reclassified only if the old head is not the predecessor of the new head
*)

(* Operations *)

OpHashes == Int
OpTypes == { "Endorsement", "Other" }
Operations == [ type : OpTypes, hash : OpHashes ]

\* seed_nonce_revelation level nonce
\* endorsement_with_slot [endorsement shell protocol_data] slot
\* double_endorsement_evidence [endorsement shell protocol_data] [endorsement shell protocol_data] slot
\* double_baking_evidence block_header block_header
\* activate_account id activation_code
\* endorsement level
\* proposals source period (proposals : Protocol_hash list)
\* ballot source period (proposal : Protocol_hash) (ballot : Vote_repr.ballot)
\* failing_noop string

\* Manager operations
\* reveal pub_key
\* transaction amount ?parameters (entrypoint : string) (dest : Contract_repr.contract)
\* origination delegate ?script credit (preorigination : Contract_repr.t option)
\* delegation (pkh : Public_key_hash.t option)

----

(* Assumptions *)

\* TODO

----

(* Messages *)

\* Operation
\* Advertisement request
\* any others?

MsgTypes == { "Advertise", "Operation" }
AdvContents == {} \* TODO
OpContents == {} \* TODO
Messages ==
    [ type : {"Advertise"}, contents : AdvContents ] \cup
    [ type : {"Operation"}, contents : OpContents ]

\* TODO classify operation on top of current validation state
\* do not want to advertise [refused] operations

\* TODO status
\* - fetching: hash known, operation not received
\* - pending: hash and operation known, not classified on top of [predecessor]
\* - classified: hash and operation known, classification has been given
\* - banned: removed from all other fields and ignored when received in any form

(* TODO actions

Handle an operation
 - try to classify
   - if applied, 

Predecessor changes
 - how to repressent blocks?

Advertise [advertisement]
 - endorsements are propagated if Applied or Branch_delayed

Flush hash

Fetch operation timeout

What else?
*)

ReceiveOperation == \E peer \in connections, op \in Operations :
    /\ all_operations' = all_operations \cup {op}
    /\ incoming' = [ incoming EXCEPT ![peer] = Append(@, op) ]
    /\ UNCHANGED <<>> \* TODO

Applied(peer, op) ==
    /\ op.hash \notin live_operations
    \* add to applied
    \* add to live_operations or fetching/pending?
    \* add to known_valid or mp_pending?
    /\ {}
    /\ UNCHANGED <<>> \* TODO

Branch_delayed(peer, op) ==
    /\ op.hash \notin live_operations
    \* add to branch_delayed
    \* add to live_operations or fetching/pending?
    \* add to known_valid or mp_pending?
    /\ {}
    /\ UNCHANGED <<>> \* TODO

Branch_refused(peer, op) ==
    /\ op.hash \notin live_operations
    \* add to branch_refused
    \* add to live_operations or fetching/pending?
    \* add to known_valid or mp_pending?
    /\ {}
    /\ UNCHANGED <<>> \* TODO

Refused(peer, op) ==
    /\ op.hash \notin live_operations
    \* add to refused
    \* add to banned?
    /\ {}
    /\ UNCHANGED <<>> \* TODO

Outdated(peer, op) ==
    /\ op.hash \in live_operations
    /\ incoming' = [ incoming EXCEPT ![peer] = Tail(@) ]
    /\ UNCHANGED <<>> \* TODO

Ban(peer, op) ==
    \* Why are some operations banned?
    \* Affect peer score?
    /\ banned' = banned \cup {op}
    /\ UNCHANGED <<>> \* TODO

HandleOperation == \E peer \in DOMAIN incoming :
    /\ incoming[peer] /= <<>>
    /\ LET op == Head(incoming[peer]) IN
       \/ Applied(peer, op)
       \/ Branch_delayed(peer, op)
       \/ Branch_refused(peer, op)
       \/ Refused(peer, op)
       \/ Outdated(peer, op)
       \/ Ban(peer, op)

----

Init ==
    /\ peers           = INIT_PEERS
    /\ connections     = INIT_CONNECTIONS
    /\ greylist        = {}
    /\ outgoing        = [ x \in connections |-> <<>> ]
    /\ incoming        = [ x \in connections |-> <<>> ]
    /\ all_operations  = {}

    /\ predecessor     = INIT_PREDECESSOR
    /\ live_blocks     = INIT_LIVE_BLOCKS
    /\ live_operations = INIT_LIVE_OPERATIONS
    /\ applied         = {}
    /\ branch_delayed  = {}
    /\ branch_refused  = {}
    /\ refused         = {}
    /\ fetching        = {}
    /\ pending         = {}
    /\ in_mempool      = {}
    /\ banned          = {}
    /\ advertisement   = {}

    /\ known_valid     = <<>>
    /\ mp_pending      = {}

Next == {}

\* operation hashes are unique
OperationHashUniqueness ==
    []( { ops \in all_operations \X all_operations :
            ops[1].hash = ops[2].hash /\ ops[1] /= ops[2] } = {} )

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ OperationHashUniqueness

----

(* Properties *)

TypeOK ==
    /\ peers \in SUBSET Nodes
    /\ connections \subseteq peers
    /\ greylist \in (peers \ connections)
    /\ outgoing \in [ connections -> Seq(Messages) ]
    \* TODO

PrevalidatorInvariant ==
    \* unclassified
    /\ fetching \cap pending \cap applied \cap banned = {}
    \* classified
    /\ applied \cap branch_delayed \cap branch_refused \cap refused = {}
    /\ advertisement \cap refused = {}
    \* mempool/prevalidator consistency
    /\ mp_pending \cup ToSet(known_valid) = in_mempool

AdvertisingEndorsements ==
    LET inter == advertisement \cap branch_delayed IN
    { op \in inter : op.type /= "Endorsement" } = {}

========================
