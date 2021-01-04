--------------------------- MODULE DistributedDB ---------------------------

EXTENDS FiniteSets, Integers, Naturals, Sequences

CONSTANTS NumNodes,     \* number of nodes
          MaxQueueSize, \* bound on size of message queues
          NumChainIds,  \* initial number of chain ids
          N             \* bound on seq lengths

VARIABLES in_messages,  \* Nodes -> Seq(Messages) - queue of incoming messages for the given node
          active,       \* Chains -> SUBSET Nodes - set of nodes which are active for the given chain
          active_chains \* Nodes -> SUBSET Chains - set of chains for which the given node is active

(* Associate a response to a request so we can determine if response is expected *)

(* Bootstrap pipeline with header/operation timeouts (notify_new_block) *)

\*ASSUME

vars == <<active, active_chains, in_messages>>

Nodes == 1..NumNodes

Chains == 1..NumChainIds

----------------------------------------------------------------------------

(* Helper functions *)
Pick(_s) == CHOOSE _x \in _s : TRUE

RECURSIVE _update_msgs(_, _, _)
_update_msgs(_msgs, _msg, _to_update) ==
    CASE _to_update = {} -> _msgs
      [] OTHER ->
           LET p == Pick(_to_update)
               new == [ _msgs EXCEPT ![p] = Append(@, _msg) ]
           IN  _update_msgs(new, _msg, _to_update \ {p})

update_msgs(_msgs, _chain, _msg) ==
    LET _from == _msg.from
        _active == active[_chain] \ {_from}
        _receivers == { _node \in _active : Len(in_messages[_node]) < 2 }
    IN  _update_msgs(_msgs, _msg, _receivers)

checkQueueSize[_id \in Nodes] == Len(in_messages[_id]) < MaxQueueSize

ToSet(_seq) == { _seq[i] : i \in DOMAIN _seq }

NESeq(_set) == Seq(_set) \ {<<>>}

SeqOfLen(_elems, _size) ==
    CASE _size < 0 -> {}
      [] OTHER -> [ 1.._size -> _elems ]

(* Enumerable set of bounded sequences *)
RECURSIVE _Seq_n(_, _, _, _)
_Seq_n(_elems, _size, _curr, _acc) ==
    CASE _curr > _size -> _acc
      [] OTHER -> _Seq_n(_elems, _size, _curr + 1, _acc \cup SeqOfLen(_elems, _curr))

Seq_n(_elems, _size) ==
    CASE _size < 0 -> {}
      [] OTHER -> _Seq_n(_elems, _size, 0, {})

NESeq_n(_set, _size) == { _s \in Seq_n(_set, _size) : _s # <<>> }

NE(_set) == SUBSET _set \ {{}}

Pairs(_set1, _set2) == { <<_x1, _x2>> : _x1 \in _set1, _x2 \in _set2 }

----------------------------------------------------------------------------

(* Messages *)

(* Advertise messages *)
(*
 - Current_branch of Chain_id.t * Block_locator.t
 - Current_head of Chain_id.t * Block_header.t * Mempool.t
 - Block_header of Block_header.t
 - Operation of Operation.t
 - Protocol of Protocol.t
 - Operations_for_block of
      Block_hash.t * int * Operation.t list * Operation_list_list_hash.path
 - Checkpoint of Chain_id.t * Block_header.t
 - Protocol_branch of
      Chain_id.t * int (* proto_level: uint8 *) * Block_locator.t
 - Predecessor_header of Block_hash.t * int32 * Block_header.t
*)
Hashes == { "hash" }

Headers == { "header" }

Locators == { "locator" }

Mempools == { "mempool" }

Operations == { "operation" }

Protocols == { "protocol" }

AdParams == [ id : Chains,  locator : Locators ]
            \cup
            [ id : Chains, header : Headers, mempool : Mempools ]
            \cup
            [ header : Headers ]
            \cup
            [ operation : Operations ]
            \cup
            [ protocol : Protocols ]
            \cup
            [ block_hash : Hashes, (*branch?,*) operations : NESeq_n(Operations, N),
              operations_hash : NESeq_n(Hashes, N) ]
            \cup
            [ id : Chains, header : Headers ]
            \cup
            [ id : Chains, (*int?,*) locator : Locators ]
            \cup
            [ block_hash : Hashes, (*int32?,*) header : Headers ]

AdMsgTypes ==
    { "Current_branch", "Current_head", "Block_header", "Operation"
    , "Protocol", "Operations_for_block", "Checkpoint", "Protocol_branch"
    , "Predecessor_header" }

AdMsgs == [ from : Nodes, type : AdMsgTypes, params : AdParams ]

(* Request messages *)
(*
 - Get_current_branch of Chain_id.t
 - Get_current_head of Chain_id.t
 - Get_checkpoint of Chain_id.t
 - Get_protocol_branch of Chain_id.t * int
 - Get_block_headers of Block_hash.t list
 - Get_operations of Operation_hash.t list
 - Get_protocols of Protocol_hash.t list
 - Get_operations_for_blocks of (Block_hash.t * int) list
 - Get_predecessor_header of Block_hash.t * int32
*)
ReqParams == [ id : Chains ]                                \* current_branch, current_head, checkpoint
             \cup
             [ id : Chains, branch : 1..N ]                 \* branch?
             \cup
             [ hashes : NESeq_n(Hashes, N) ]                \* headers, operations, protocols
             \cup
             [ hash_num : NESeq_n(Pairs(Hashes, 1..N), N) ] \* num?
             \cup
             [ hash : Hashes, num : 1..N ]                  \* num?

ReqMsgTypes ==
    { "Get_current_branch", "Get_current_head", "Get_block_headers", "Get_operations"
    , "Get_protocols", "Get_operations_for_blocks", "Get_checkpoint", "Get_protocol_branch"
    , "Get_predecessor_header" }

ReqMsgs == [ from : Nodes, type : ReqMsgTypes, params : ReqParams ]

\*(* Activate *)
\*ActivateMsg == [ type : {"Activate"}, id : Chains ]
\*
\*(* Deactivate *)
\*DeactivateMsg == [ type : {"Deactivate"}, id : Chains ]

Messages == AdMsgs \cup ReqMsgs \* \cup DeactivateMsg

PossibleQueueStates == Seq_n(Messages, MaxQueueSize)

Msg1(_from, _type, _chain) ==
    [ from |-> _from, type |-> _type, params |-> [ id |-> _chain ] ]

----------------------------------------------------------------------------

(* An inactive node becomes active on given chain *)
Activate(_node, _chain) ==
    /\ active' = [ active EXCEPT ![_chain] = @ \cup {_node} ]
    /\ active_chains' = [ active_chains EXCEPT ![_node] = @ \cup {_chain} ]
    /\ UNCHANGED <<in_messages>>

(* An active node becomes inactive on given chain *)
Deactivate(_node, _chain) ==
    /\ active' = [ active EXCEPT ![_chain] = @ \ {_node} ]
    /\ active_chains' = [ active_chains EXCEPT ![_node] = @ \ {_chain} ]
    /\ UNCHANGED <<in_messages>>

(* Request actions *)

(* Request the current branch from one active peer *)
Get_current_branch_1(_from, _chain, _to) ==
    /\ in_messages' =
         [ in_messages EXCEPT ![_to] =
             IF checkQueueSize[_to]
             THEN Append(@, Msg1(_from, "Get_current_branch", _chain))
             ELSE @ ]
    /\ UNCHANGED <<active, active_chains>>

(* Request the current branch from all active peers *)
Get_current_branch_n(_from, _chain) ==
    /\ in_messages' =
         update_msgs(in_messages, _chain, Msg1(_from, "Get_current_branch", _chain))
    /\ UNCHANGED <<active, active_chains>>

(* Request the current head from one active peer *)
Get_current_head_1(_from, _chain, _to) ==
    /\ in_messages' =
         [ in_messages EXCEPT ![_to] =
             IF checkQueueSize[_to]
             THEN Append(@, Msg1(_from, "Get_current_branch", _chain))
             ELSE @ ]
    /\ UNCHANGED <<active, active_chains>>

(* Request the current head from all active peers *)
Get_current_head_n(_from, _chain) ==
    /\ in_messages' =
         update_msgs(in_messages, _chain, Msg1(_from, "Get_current_head", _chain))
    /\ UNCHANGED <<active, active_chains>>

----------------------------------------------------------------------------

\* TODO
(* A node that is inactive on a chain becomes active *)
Activation ==
    \E _chain \in Chains :
        \E _node \in Nodes \ active[_chain] : Activate(_node, _chain)

(* A node that is active on a chain become inactive *)
Deactivation ==
    \E _chain \in Chains :
        \E _node \in active[_chain] : Deactivate(_node, _chain)

(* Request current branch from an active peer *)
Get_current_branch_one ==
    \E _from \in Nodes, _chain \in Chains :
        \E _to \in active[_chain] \ {_from} : Get_current_branch_1(_from, _chain, _to)

(* Request current branch from all active peers *)
Get_current_branch_all ==
    \E _from \in Nodes, _chain \in Chains : Get_current_branch_n(_from, _chain)

(* Request current head from an active peer *)
Get_current_head_one ==
    \E _from \in Nodes :
        \E _chain \in active_chains[_from] :
            \E _to \in active[_chain] \ {_from} :
                Get_current_head_1(_from, _chain, _to)

(* Request current head from all active peers *)
Get_current_head_all ==
    \E _from \in Nodes :
        \E _chain \in active_chains[_from] : Get_current_head_n(_from, _chain)

----------------------------------------------------------------------------

(* Type invariant *)
TypeOK ==
    /\ active \in [ Chains -> SUBSET Nodes ]
    /\ active_chains \in [ Nodes -> SUBSET Chains ]
    /\ in_messages \in [ Nodes -> PossibleQueueStates ]
    /\ \A _node \in Nodes, _chain \in Chains :
         _node \in active[_chain] <=> _chain \in active_chains[_node]

----------------------------------------------------------------------------

Init ==
    /\ active = [ _x \in Chains |-> {} ]
    /\ active_chains = [ _x \in Nodes |-> {} ]
    /\ in_messages = [ _x \in Nodes |-> <<>> ]

Next ==
    \/ Activation
    \/ Deactivation
    \/ Get_current_branch_one
    \/ Get_current_branch_all
    \/ Get_current_head_one
    \/ Get_current_head_all

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

(* Invariants *)

=============================================================================
