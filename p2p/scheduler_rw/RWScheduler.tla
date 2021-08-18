---------------------------- MODULE RWScheduler ----------------------------

EXTENDS Utils

CONSTANTS
    \* set of abstract messages
    \* @type: Set(MSG);
    Messages,

    \* how fast quota is updated
    \* @type: Int;
    Max_speed,
    
    \* maximum number of connections for scheduler to handle
    \* @type: Int;
    Max_conn,

    \* maximum counter value
    \* @type: Int;
    Max_count,

    \* maximum size of msg
    \* @type: Int;
    Max_msg,

    \* maximum quota value
    \* @type: Int;
    Max_quota,

    \* high/low queue size bound
    \* @type: Int;
    HL_queue,

    \* in_param queue size bound
    \* @type: Int;
    In_queue,

    \* null value
    \* @type: Int;
    None

VARIABLES
    \* record of connection counters, quotas
    \* @type: [ counter : Int, quota : Int ];
    state,

    \* scheduler counter
    \* @type: Int;
    counter,

    \* high & low priority queues
    \* @type: [ high : Seq(<<MSG, Int>>), low : Seq(<<MSG, Int>>) ];
    queue,

    \* scheduler quota
    \* @type: Int;
    quota,

    \* ids of active connections handled by the scheduler
    \* @type: Set(Int);
    connections,

    \* TRUE if waiting for data, FALSE otherwise
    \* @type: Bool;
    waiting,

    \* record to enforce relationship between Pop and Handle
    \* @type: [ prio : Bool, msg : Seq(MSG) ];
    handle,

    \* incoming messages
    \* @type: Seq(<<MSG, Int>>);
    in_param

vars == <<state, counter, queue, quota, connections, waiting, handle, in_param>>

ASSUME Cardinality(Messages) >= 1
ASSUME Max_speed \in Nat
ASSUME Max_conn \in Nat
ASSUME Max_count \in Nat
ASSUME Max_msg \in Nat
ASSUME Max_quota \in Nat
ASSUME HL_queue \in Nat
ASSUME In_queue \in Nat
ASSUME Max_speed <= Max_quota

----------------------------------------------------------------------------

\* Module-specific definitions

Connections == 0..Max_conn

MsgSize == 0..Max_msg

queuesEmpty ==
    /\ queue.high = <<>>
    /\ queue.low = <<>>

\* @type: (Seq(<<MSG, Int>>)) => Set(Int);
ids(s) == { s[i][2] : i \in DOMAIN s }

\* check if quota is positive
\* @type: <<Int, MSG>> => Bool;
PosQuota(msg) ==
    LET id == msg[2] IN
    /\ id \in connections
    /\ state.quota[id] > 0

\* check if quota is non-positive
NonPosQuota(msg) ==
    LET id == msg[2] IN
    /\ id \in connections
    /\ state.quota[id] <= 0

ValidMsgInQueue ==
    \/ /\ queue.high /= <<>>
       /\ Head(queue.high)[2] /= None
       /\ Head(queue.high)[3] /= None
    \/ /\ queue.low /= <<>>
       /\ Head(queue.low)[2] /= None
       /\ Head(queue.low)[3] /= None

\* <<id, msg, size>>
FullMsg == Connections \times Messages \times MsgSize

\* <<msg, size>>
PartialMsg == Messages \times MsgSize

----------------------------------------------------------------------------

(***********)
(* Actions *)
(***********)

\* New connections can be created
Create_connection(id) ==
    /\ id \notin connections
    /\ state' = [ state EXCEPT !.counter[id] = 0, !.quota[id] = 0 ]
    /\ connections' = connections \cup {id}
    /\ UNCHANGED <<counter, queue, quota, waiting, handle, in_param>>

\* Connections can be closed as long as we are not handling a message from this connection
Close_connection(id) ==
    /\ id \notin ids(handle.msg)
    /\ state' = [ state EXCEPT !.counter[id] = None, !.quota[id] = None ]
    /\ connections' = connections \ {id}
    /\ UNCHANGED <<counter, queue, quota, waiting, handle, in_param>>

\* When there are messages to handle, we adjust all the counters and quotas, enables Waiter
\* message = <<id, msg, size>>
Handle ==
    /\ handle.prio
    /\ handle.msg /= <<>>
    /\ LET hd  == Head(handle.msg)
           b   == hd[1]  \* if b then high prio else low prio
           id  == hd[2]
           msg == hd[3]
           len == hd[4]
       IN /\ id \in connections
          /\ counter <= Max_count - len
          /\ state.counter[id] <= Max_count - len
          /\ counter' = counter + len
          /\ quota' = quota - len
          /\ state' = [ state EXCEPT
                        !.counter[id] = @ + len,
                        !.quota[id]   = IF b THEN @ - len ELSE @ ]
    /\ waiting' = TRUE
    /\ handle' = [ handle EXCEPT
                    !.prio = Len(handle.msg) /= 1, \* are there more messages to handle?
                    !.msg  = Tail(@) ]             \* remove the handled message
    /\ UNCHANGED <<queue, connections, in_param>>

\* Incoming message on in_param
\* check that in_param is not full already
Message(id, msg, len) ==
    /\ Len(in_param[id]) < In_queue
    /\ handle' = [ handle EXCEPT !.prio = TRUE ]
    /\ in_param' = [ in_param EXCEPT ![id] = Append(@, <<msg, len>>) ]
    /\ UNCHANGED <<state, counter, queue, quota, connections, waiting>>

\* Pop a message from one of the queues, enables Handle
Pop(id) ==
    /\ handle.prio
    /\ ValidMsgInQueue
    /\ IF queue.high /= <<>>
       THEN \* take msg from queue.high
         LET msg == Head(queue.high)
         IN /\ handle' = [ handle EXCEPT !.msg = Append(@, <<TRUE>> \o msg) ]
            /\ queue' = [ queue EXCEPT !.high = Tail(@) ]
       ELSE \* take msg from queue.low
         LET msg == Head(queue.low)
         IN /\ handle' = [ handle EXCEPT !.msg = Append(@, <<FALSE>> \o msg) ]
            /\ queue' = [ queue EXCEPT !.low = Tail(@) ]
    /\ UNCHANGED <<state, counter, quota, waiting, connections, in_param>>

\* When we are not handling data or already waiting for data, we can enable Waiter
Wait_data ==
    /\ ~handle.prio
    /\ ~waiting
    /\ queuesEmpty
    /\ waiting' = TRUE
    /\ UNCHANGED <<state, counter, queue, quota, connections, handle, in_param>>

\* When waiting for data, once we get a msg from in_param, we place it in the appropriate queue
Waiter(id) ==
    /\ waiting
    /\ in_param[id] /= <<>>
    /\ IF queuesEmpty
       THEN waiting' = FALSE
       ELSE UNCHANGED waiting
    /\ LET hd == Head(in_param[id])
           msg == <<id, hd[1], hd[2]>>
       IN IF state.quota[id] > 0
          THEN queue' = [ queue EXCEPT !.high = Append(@, msg) ]
          ELSE queue' = [ queue EXCEPT !.low  = Append(@, msg) ]
    /\ in_param' = [ in_param EXCEPT ![id] = Tail(@) ]
    /\ UNCHANGED <<state, counter, quota, connections, handle>>

\* When the scheduler quota < 0, we can update the quota and rearrange the queues
Update_quota ==
    /\ quota < 0
    /\ quota' = min[quota, 0] + Max_speed
    /\ IF queue.low /= <<>>
       THEN queue' = [ queue EXCEPT
                        !.high = SelectSeq(@, PosQuota),
                        !.low  = SelectSeq(@, NonPosQuota) ]
       ELSE UNCHANGED queue
    /\ UNCHANGED <<connections, counter, handle, in_param, state, waiting>>

-----------------------------------------------------------------------------

(*********************)
(* Initial predicate *)
(*********************)

Init ==
    /\ state \in [ counter : [ Connections -> 0..Max_count \cup {None} ]
                 , quota   : [ Connections -> (-Max_quota)..Max_quota \cup {None} ] ]
    /\ counter \in 0..Max_count
    /\ queue \in [ high : Seq_n(FullMsg, HL_queue), low : Seq_n(FullMsg, HL_queue) ]
    /\ quota \in (-Max_quota)..Max_quota
    /\ connections \in SUBSET Connections
    /\ waiting \in BOOLEAN
    /\ handle \in [ prio : BOOLEAN
                  , msg  : Seq_n(BOOLEAN \times Connections \times Messages \times MsgSize, HL_queue) ]
    /\ in_param \in [ Connections -> Seq_n(PartialMsg, In_queue) ]

(****************)
(* Next actions *)
(****************)

Create_conn == \E id \in Connections: Create_connection(id)

Close_conn == \E id \in connections: Close_connection(id)

Popping == \E id \in connections: Pop(id)

Waiting == \E id \in connections: Waiter(id)

Incoming_msg ==
    \E id \in connections, msg \in Messages, len \in 1..Max_msg : Message(id, msg, len)

Next ==
    \/ Create_conn
    \/ Close_conn
    \/ Popping
    \/ Handle
    \/ Wait_data
    \/ Waiting
    \/ Update_quota
    \/ Incoming_msg

-----------------------------------------------------------------------------

(************)
(* Fairness *)
(************)

Fairness ==
    /\ SF_vars(Create_conn)
    /\ SF_vars(Popping)
    /\ SF_vars(Handle)
    /\ SF_vars(Update_quota)
    /\ SF_vars(Incoming_msg)
    /\ WF_vars(Wait_data)
    /\ WF_vars(Close_conn)
    /\ WF_vars(Waiting)

-----------------------------------------------------------------------------

(*****************)
(* Specification *)
(*****************)

Spec == Init /\ [][Next]_vars \* /\ Fairness

----------------------------------------------------------------------------

(**************)
(* Invariants *)
(**************)

ConnOK == connections \subseteq Connections

CounterOK == counter \in 0..Max_count

HandleOK ==
    /\ DOMAIN handle = { "prio", "msg" }
    /\ handle.prio \in BOOLEAN
    /\ Len(handle.msg) <= HL_queue
    /\ \A i \in DOMAIN handle.msg : handle.msg[i] \in BOOLEAN \times FullMsg

InParamOK ==
    /\ DOMAIN in_param = Connections
    /\ \A id \in DOMAIN in_param :
        /\ Len(in_param[id]) <= In_queue
        /\ \A n \in DOMAIN in_param[id] : in_param[id][n] \in PartialMsg

QueueOK ==
    /\ DOMAIN queue = { "high", "low" }
    /\ \A i \in DOMAIN queue.high : queue.high[i] \in FullMsg
    /\ Len(queue.high) <= HL_queue
    /\ \A i \in DOMAIN queue.low : queue.low[i] \in FullMsg
    /\ Len(queue.low) <= HL_queue

QuotaOK == quota \in (-Max_quota)..Max_quota

StateOK ==
    /\ DOMAIN state = { "counter", "quota" }
    /\ DOMAIN state.counter = Connections
    /\ DOMAIN state.quota = Connections
    /\ \A id \in Connections : state.counter[id] \in 0..Max_count \cup {None}
    /\ \A id \in Connections : state.quota[id] \in (-Max_quota)..Max_quota \cup {None}

WaitingOK == waiting \in BOOLEAN

Consistency ==
    /\ StateOK
    /\ QueueOK
    /\ ConnOK
    /\ QuotaOK
    /\ CounterOK
    /\ WaitingOK
    /\ InParamOK

-----------------------------------------------------------------------------

(**************)
(* Properties *)
(**************)



=============================================================================
