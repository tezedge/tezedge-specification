---------------------------- MODULE DB_Messages -----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES network_info, node_info

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE Utils

-----------------------------------------------------------------------------

\* There 2 types of messages:
\* - Full (advertise/request)
\* - Synchronization (acknowledge/error)

-----------------------------------------------------------------------------

(***************************************)
(* Full messages (2 kinds):            *)
(* - Advertise messages                *)
(* - Request messages                  *)
(***************************************)

(* Advertise messages *)
(* Used to respond to specific requests and to broadcast messages to all active nodes on a chain *)

\* Advertise message parameters
AdParams ==
    [ branch : Branches \cup {-1} ] \* Current_branch
    \cup
    [ branch : Branches, height : Heights \cup {-1} ] \* Current_head
    \cup
    [ branch : Branches, height : Heights, header : Headers ] \* Block_header
    \cup
    [ branch : Branches, height : Heights, ops : Operations ] \* Operations

\* Advertise message types
AdMsgTypes == { "Block_header", "Current_branch", "Current_head", "Operations" }

\* Advertise messages
AdMsgs == [ from : SysNodes, to : SysNodes, type : AdMsgTypes, params : AdParams ]

isValidAdMsg(msg) ==
    /\ msg \in AdMsgs
    /\ msg.from /= msg.to
    /\ \/ /\ DOMAIN msg.params = { "branch" }
          /\ msg.type = "Current_branch"
       \/ /\ DOMAIN msg.params = { "branch", "height" }
          /\ msg.type = "Current_head"
       \/ /\ DOMAIN msg.params = { "branch", "height", "header" }
          /\ msg.type = "Block_header"
       \/ /\ DOMAIN msg.params = { "branch", "height", "ops" }
          /\ msg.type = "Operations"

(* Request messages *)
(* Used to request specific info either from a single node or from all active nodes on a chain *)

\* Request message parameters
ReqParams ==
    [ chain : Chains ] \* Get_current_branch
    \cup
    [ branch : Branches ] \* Get_current_head
    \cup
    [ branch : Branches, height : Heights ] \* Get_block_header & Get_operations

\* Request message types
ReqMsgTypes == { "Get_block_header", "Get_current_branch", "Get_current_head", "Get_operations" }

\* Request messages
ReqMsgs == [ from : Nodes, to : SysNodes, type : ReqMsgTypes, params : ReqParams ]

isValidReqMsg(msg) ==
    /\ msg \in ReqMsgs
    /\ msg.from /= msg.to
    /\ \/ /\ DOMAIN msg.params = { "chain" }
          /\ msg.type = "Get_current_branch"
       \/ /\ DOMAIN msg.params = { "branch" }
          /\ msg.type = "Get_current_head"
       \/ /\ DOMAIN msg.params = { "branch", "height" }
          /\ \/ msg.type = "Get_block_header"
             \/ msg.type = "Get_operations"

\* A full message is either an advertise or request message
FullMsgs == AdMsgs \cup ReqMsgs

isValidFullMsg(msg) ==
    \/ isValidAdMsg(msg)
    \/ isValidReqMsg(msg)

-----------------------------------------------------------------------------

(***************************************)
(* Synchronization messages (2 kinds): *)
(* - Acknowledgment                    *)
(* - Error                             *)
(***************************************)

(* Acknowledgment messages *)

\* Acknowledgment message types
AckMsgTypes == { "Ack_block_header", "Ack_current_branch", "Ack_current_head", "Ack_operations" }

\* Acknowledgment/error messages
AckMsgs == [ from : Nodes, to : SysNodes, type : AckMsgTypes ]

isValidAckMsg(msg) ==
    /\ msg \in AckMsgs
    /\ msg.from /= msg.to

(* Error messages *)

\* Error message params
ErrParams == [ branch : Branches, height : Heights ]

\* Error message types
ErrMsgTypes == { "Err_block_header", "Err_operations" }

\* Error messages
ErrMsgs == [ from : Nodes, to : Nodes, type : ErrMsgTypes, error : ErrParams ]

isValidErrMsg(msg) ==
    /\ msg \in ErrMsgs
    /\ msg.from /= msg.to

\* A sync message is an ack, expect, or error message
SyncMsgs == AckMsgs \cup ErrMsgs

-----------------------------------------------------------------------------

(****************)
(* All messages *)
(****************)

Messages == FullMsgs \cup SyncMsgs

-----------------------------------------------------------------------------

\* full message predicate
isFullMsg(msg) == msg \in FullMsgs

\* advertise message predicate
isAdMsg(msg) == msg \in AdMsgs

\* request message predicate
isReqMsg(msg) == msg \in ReqMsgs

\* ack message predicate
isAckMsg(msg) == msg \in AckMsgs

\* error message predicate
isErrMsg(msg) == msg \in ErrMsgs

\* [msg] is a non-expect message
isValidMsg(msg) ==
    \/ isValidAdMsg(msg)
    \/ isValidReqMsg(msg)
    \/ isValidAckMsg(msg)
    \/ isValidErrMsg(msg)

\* Message "constructors"
\* validates [type] matches [params] and creates the message
\* invalid type/param pairs will return a TLC error

\* Full message "constructor"
Msg(from, to, type, params) ==
    LET msg == [ from |-> from, to |-> to, type |-> type, params |-> params ]
    IN CASE isValidFullMsg(msg) -> msg
         [] OTHER -> PrintT(msg)

\* Synchronization message "constructors"
AckMsg(from, to, type) ==
    LET msg == [ from |-> from, to |-> to, type |-> type ]
    IN CASE isValidAckMsg(msg) -> msg 

ErrMsg(from, to, type, error) ==
    LET msg == [ from |-> from, to |-> to, type |-> type, error |-> error ]
    IN CASE isValidErrMsg(msg) -> msg

-----------------------------------------------------------------------------

(**************************)
(* Managing sent messages *)
(**************************)

\* convert advertise msg type to corresponding ack type
ack_type[ type \in AdMsgTypes ] ==
    CASE type = "Current_branch" -> "Ack_current_branch"
      [] type = "Current_head"   -> "Ack_current_head"
      [] type = "Block_header"   -> "Ack_block_header"
      [] type = "Operations"     -> "Ack_operations"

\* TODO

-----------------------------------------------------------------------------

(********************************)
(* Message-based action helpers *)
(********************************)

\* Send [msg] to a node on [chain]
\* sent \in SUBSET Messages
Send(sent, msg) == checkAdd(sent, msg)

\* Register an expectation
\*Expect(expect, from, msg) == checkUnion(expect, {msg})

\* send [msg] to all active nodes and [sys] on [chain] except [from]
\* sent_chain \in [ SysNodes -> SUBSET Messages ]
\* DOMAIN msg = { "from", "type", "params" }
checkAddToActive(sent_chain, from, chain, msg) ==
    [ to \in SysNodes |->
        CASE to \in network_info.active[chain] \ {from} ->
               LET m == Msg(from, to, msg.type, msg.params)
               IN checkAdd(sent_chain[to], m)
          [] OTHER -> sent_chain[to] ]

\* send [msg] to all active nodes and [sys] on [chain]
\* sent : SysNodes -> SUBSET Messages
Broadcast(sent, from, chain, msg) ==
    CASE DOMAIN msg = { "params", "type" } -> checkAddToActive(sent, from, chain, msg)

\* send [msg] to all active nodes on [chain] except [from]
\* sent_chain : SysNodes -> SUBSET Messages
checkAddToActiveNodes(sent_chain, from, chain, msg) ==
    [ to \in SysNodes |->
        CASE to \in activeNodes[chain] \ {from} ->
               LET m == Msg(from, to, msg.type, msg.params)
               IN checkAdd(sent_chain[to], m)
          [] OTHER -> sent_chain[to] ]

\* Sends [msg] to all active nodes on [chain]
\* sent \in [ SysNodes -> SUBSET Messages ]
\* UNCHANGED network_info.sent[chain][sys] 
BroadcastNodes(sent, from, chain, msg) ==
    CASE DOMAIN msg = { "params", "type" } -> checkAddToActiveNodes(sent, from, chain, msg)

\* TODO manage sent messages

=============================================================================
