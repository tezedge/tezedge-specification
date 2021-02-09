---------------------------- MODULE DB_Messages -----------------------------

CONSTANTS numChains, numNodes, sizeBound

VARIABLES node_active, node_blocks, node_branches, node_headers, node_height, node_incoming, node_sent,
          active, blocks, branch, chains, mailbox, height, sysmsgs

LOCAL INSTANCE DB_Defs
LOCAL INSTANCE Utils

-----------------------------------------------------------------------------

\* There 3 types of messages:
\* - Full (advertise/request)
\* - Partial (broadcasts)
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
AdvParams ==
    [ branch : Branches \cup {-1} ] \* Current_branch
    \cup
    [ branch : Branches, height : Heights \cup {-1} ] \* Current_head
    \cup
    [ branch : Branches, height : Heights, header : Headers ] \* Block_header
    \cup
    [ branch : Branches, height : Heights, ops : Operations ] \* Operations

\* Advertise message types
AdvMsgTypes == { "Block_header", "Current_branch", "Current_head", "Operations" }

\* Advertise messages
AdvMsgs == [ from : SysNodes, to : SysNodes, type : AdvMsgTypes, params : AdvParams ]

\* Advertise message predicates
isAdMsg(msg) == msg \in AdvMsgs

isValidAdvMsg(msg) ==
    /\ msg \in AdvMsgs
    /\ msg.from /= msg.to
    /\ \/ /\ DOMAIN msg.params = { "branch" }
          /\ msg.type = "Current_branch"
       \/ /\ DOMAIN msg.params = { "branch", "height" }
          /\ msg.type = "Current_head"
       \/ /\ DOMAIN msg.params = { "branch", "height", "header" }
          /\ msg.type = "Block_header"
          /\ isHeader(msg.params.header)
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

\* Request message predicates
isReqMsg(msg) == msg \in ReqMsgs

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

(* Full messages *)

\* A full message is either an advertise or request message
FullMsgs == AdvMsgs \cup ReqMsgs

\* Full message predicates
isFullMsg(msg) == msg \in FullMsgs

isValidFullMsg(msg) ==
    \/ isValidAdvMsg(msg)
    \/ isValidReqMsg(msg)

\* Full message "constructor"
Msg(from, to, type, params) ==
    LET msg == [ from |-> from, to |-> to, type |-> type, params |-> params ]
    IN CASE isValidFullMsg(msg) -> msg

-----------------------------------------------------------------------------

(****************************)
(* Partial request messages *)
(****************************)

\* Partial messages
PartialMsgs == [ type : ReqMsgTypes, params : ReqParams ]

\* Partial message predicate
isValidPartialMsg(msg) ==
    /\ msg \in PartialMsgs
    /\ \/ /\ DOMAIN msg.params = { "chain" }
          /\ msg.type = "Get_current_branch"
       \/ /\ DOMAIN msg.params = { "branch" }
          /\ msg.type = "Get_current_head"
       \/ /\ DOMAIN msg.params = { "branch", "height" }
          /\ \/ msg.type = "Get_block_header"
             \/ msg.type = "Get_operations"

\* Partial message "constructor"
PartialMsg(type, params) == [ type |-> type, params |-> params ]

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

\* Ack message predicates
isAckMsg(msg) == msg \in AckMsgs

isValidAckMsg(msg) ==
    /\ msg \in AckMsgs
    /\ msg.from /= msg.to

\* Ack message "constructor"
AckMsg(from, to, type) ==
    LET msg == [ from |-> from, to |-> to, type |-> type ]
    IN CASE isValidAckMsg(msg) -> msg

(* Error messages *)

\* Error message params
ErrParams == [ branch : Branches, height : Heights ]

\* Error message types
ErrMsgTypes == { "Err_block_header", "Err_operations" }

\* Error messages
ErrMsgs == [ from : Nodes, to : Nodes, type : ErrMsgTypes, error : ErrParams ]

\* Error message predicates
isErrMsg(msg) == msg \in ErrMsgs

isValidErrMsg(msg) ==
    /\ msg \in ErrMsgs
    /\ msg.from /= msg.to

\* Error message "constructor"
ErrMsg(from, to, type, error) ==
    LET msg == [ from |-> from, to |-> to, type |-> type, error |-> error ]
    IN CASE isValidErrMsg(msg) -> msg

(* Synchronization messages *)

\* A sync message is an ack, expect, or error message
SyncMsgs == AckMsgs \cup ErrMsgs

-----------------------------------------------------------------------------

(****************)
(* All messages *)
(****************)

Messages == FullMsgs \cup SyncMsgs

\* valid message predicate
isValidMsg(msg) ==
    \/ isValidAdvMsg(msg)
    \/ isValidReqMsg(msg)
    \/ isValidAckMsg(msg)
    \/ isValidErrMsg(msg)

-----------------------------------------------------------------------------

(**************************)
(* Managing sent messages *)
(**************************)

\* convert adv msg type to corresponding ack type
ack_type[ type \in AdvMsgTypes ] ==
    CASE type = "Current_branch" -> "Ack_current_branch"
      [] type = "Current_head"   -> "Ack_current_head"
      [] type = "Block_header"   -> "Ack_block_header"
      [] type = "Operations"     -> "Ack_operations"

\* convert ack msg type to corresponding adv type
adv_type[ type \in AckMsgTypes ] ==
    CASE type = "Ack_current_branch" -> "Current_branch"
      [] type = "Ack_current_head"   -> "Current_head"
      [] type = "Ack_block_header"   -> "Block_header"
      [] type = "Ack_operations"     -> "Operations"

\* convert adv and err msg types to corresponding req type
req_type[ type \in AdvMsgTypes \cup ErrMsgTypes ] ==
    CASE type = "Current_branch"   -> "Get_current_branch"
      [] type = "Current_head"     -> "Get_current_head"
      [] type = "Block_header"     -> "Get_block_header"
      [] type = "Operations"       -> "Get_operations"
      [] type = "Err_block_header" -> "Get_block_header"
      [] type = "Err_operations"   -> "Get_operations"

\* delete the corrsponding sent message when an adv, ack, or err message is handled
delete_msg(msg, sent) ==
    LET from == msg.from
        to   == msg.to
        type == msg.type
    IN CASE type \in AckMsgTypes ->
              LET pred(m) == ~(m.from = from /\ m.to = to /\ m.type = adv_type[type])
              IN Filter(sent, pred)
         [] type \in AdvMsgTypes \cup ErrMsgTypes ->
              LET pred(m) == ~(m.from = from /\ m.to = to /\ m.type = req_type[type])
              IN Filter(sent, pred)

-----------------------------------------------------------------------------

(*************************)
(* Message-based actions *)
(*************************)

\* Send [msg] to a node on [chain]
\* sent \in SUBSET Messages
Send(node, chain, msg) ==
    LET to == msg.to
    IN IF node = sys
       THEN mailbox' = [ mailbox EXCEPT ![chain][to] = checkAppend(@, msg) ]
       ELSE /\ node_sent' = [ node_sent EXCEPT ![node][chain] = checkCons(msg, @) ]
            /\ mailbox' = [ mailbox EXCEPT ![chain][to] = checkAppend(@, msg) ]

SendNoRecord(node, chain, msg) ==
    mailbox' = [ mailbox EXCEPT ![chain][msg.to] = checkAppend(@, msg) ]

\* Manage sent messages
ManageSent(node, chain, msg) ==
    node_sent' = [ node_sent EXCEPT ![node][chain] = delete_msg(msg, @) ]

\* [node] consumes an incoming message
Consume(node, chain) ==
    IF node = sys
    THEN sysmsgs' = [ sysmsgs EXCEPT ![chain] = Tail(@) ]
    ELSE node_incoming' = [ node_incoming EXCEPT ![node][chain] = Tail(@) ]

\* send [msg] to all active nodes and [sys] on [chain] except [from]
\* mailbox_chain : SysNodes -> SUBSET Messages
\* DOMAIN msg_tp = { "type", "params" }
checkAppToActive(mailbox_chain, from, chain, pmsg) ==
    [ to \in SysNodes |->
        CASE to \in active[chain] \ {from} ->
               LET msg == Msg(from, to, pmsg.type, pmsg.params)
               IN checkAppend(mailbox_chain[to], msg)
          [] OTHER -> mailbox_chain[to] ]

\* send [msg] to all active nodes and [sys] on [chain]
\* mailbox_chain : SysNodes -> SUBSET Messages
Broadcast(mailbox_chain, from, chain, pmsg) ==
    CASE DOMAIN pmsg = { "params", "type" } -> checkAppToActive(mailbox_chain, from, chain, pmsg)

\* send [msg] to all active nodes on [chain] except [from]
\* mailbox_chain : SysNodes -> SUBSET Messages
\* DOMAIN msg_tp = { "type", "params" }
checkAppToActiveNodes(mailbox_chain, from, chain, pmsg) ==
    [ to \in SysNodes |->
        CASE to \in activeNodes[chain] \ {from} ->
               LET msg == Msg(from, to, pmsg.type, pmsg.params)
               IN checkAppend(mailbox_chain[to], msg)
          [] OTHER -> mailbox_chain[to] ]

\* Sends [msg] to all active nodes on [chain]
\* mailbox_chain : SysNodes -> SUBSET Messages
\* UNCHANGED mailbox[chain][sys]
BroadcastNodes(mailbox_chain, from, chain, pmsg) ==
    CASE DOMAIN pmsg = { "params", "type" } -> checkAppToActiveNodes(mailbox_chain, from, chain, pmsg)

=============================================================================
