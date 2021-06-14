---------------------------- MODULE RWScheduler ----------------------------

EXTENDS FiniteSets, Integers, Naturals, Sequences

CONSTANTS Messages,     \* abstract message type
          Max_speed,    \* how fast quota is updated
          M,            \* maximum number of connections for scheduler to handle
          N,            \* maximum counter value
          S,            \* maximum size of msg
          Q,            \* maximum quota value
          HL,           \* high_q/low_q queue size bound
          I,            \* in_param queue size bound
          None          \* null value

VARIABLES state,        \* record of connection counters, quotas
          counter,      \* scheduler counter
          high_q,       \* high priority queue
          low_q,        \* low priority queue
          quota,        \* scheduler quota
          connections,  \* ids of active connections handled by the scheduler
          waiting,      \* TRUE if waiting for data, FALSE otherwise
          handle,       \* record of b, id, msg to enforce relationship between Pop and Handle
          in_param      \* incoming messages

vars == <<state
        , counter
        , high_q
        , low_q
        , quota
        , connections
        , waiting
        , handle
        , in_param>>

ASSUME Max_speed <= Q

----------------------------------------------------------------------------

min(n, m) == IF n > m THEN m ELSE n

queuesEmpty == high_q = <<>> /\ low_q = <<>>

ids(s) == { s[i][2] : i \in DOMAIN s }

PosQuota(msg) ==
    LET id == msg[1]
    IN  /\ id \in connections
        /\ state.quota[id] > 0

NonPosQuota(msg) ==
    LET id == msg[1]
    IN  /\ id \in connections
        /\ state.quota[id] <= 0

ValidMsgInQueue ==
    \/ /\ high_q # <<>>
       /\ Head(high_q)[2] # None
       /\ Head(high_q)[3] # None
    \/ /\ low_q # <<>>
       /\ Head(low_q)[2] # None
       /\ Head(low_q)[3] # None

FullMsg == (0..M) \times Messages \times 0..S

PartialMsg == Messages \times 0..S

----------------------------------------------------------------------------

\*TypeOK ==
\*    /\ state \in [ counter : [ 0..M -> 0..N \cup {None} ]
\*                 , quota   : [ 0..M -> 0..Q \cup {None} ] ]
\*    /\ high_q \in Seq(FullMsg)
\*    /\ Len(high_q) <= HL
\*    /\ low_q \in Seq(FullMsg)
\*    /\ Len(low_q) <= HL
\*    /\ connections \subseteq 0..M
\*    /\ quota <= Q
\*    /\ counter \in 0..N
\*    /\ waiting \in BOOLEAN
\*    /\ in_param \in [ 0..M -> Seq(PartialMsg) ]
\*    /\ \A id \in DOMAIN in_param: Len(in_param[id]) <= I

Init ==
    /\ state = [ counter |-> [ x \in 0..M |-> None ]
               , quota   |-> [ x \in 0..M |-> None ] ]
    /\ counter = 0
    /\ high_q = <<>>
    /\ low_q = <<>>
    /\ quota = Max_speed
    /\ connections = {}
    /\ waiting = FALSE
    /\ handle = [ b |-> FALSE, msg |-> <<>> ]
    /\ in_param = [ x \in 0..M |-> <<>> ]

----------------------------------------------------------------------------

(* New connections can be created *)
Create_connection(id) ==
    /\ id \notin connections
    /\ state' = [ state EXCEPT !.counter[id] = 0, !.quota[id] = 0 ]
    /\ connections' = connections \cup {id}
    /\ UNCHANGED <<counter, high_q, low_q, quota, waiting, handle, in_param>>

(* Connections can be closed as long as we are not handling a message from this connection *)
Close_connection(id) ==
    /\ id \notin ids(handle.msg)
    /\ state' = [ state EXCEPT !.counter[id] = None, !.quota[id] = None ]
    /\ connections' = connections \ {id}
    /\ UNCHANGED <<counter, high_q, low_q, quota, waiting, handle, in_param>>

(* When there are messages to handle, we adjust all the counters and quotas, enables Waiter *)
(* message = <<id, msg, size>> *)
Handle ==
    /\ handle.b
    /\ handle.msg # <<>>
    /\ LET hd  == Head(handle.msg)
           b   == hd[1]  \* if b then high prio else low prio
           id  == hd[2]
           msg == hd[3]
           len == hd[4]
       IN
       /\ id \in connections
       /\ counter' = counter + len
       /\ quota' = quota - len
       /\ state' = [ state EXCEPT
                       !.counter[id] = @ + len,
                       !.quota[id]   = IF b THEN @ - len ELSE @ ]
    /\ waiting' = TRUE
    /\ handle' = [ handle EXCEPT
                     !.b = Len(handle.msg) # 1, \* are there more messages to handle?
                     !.msg = Tail(@) ]          \* remove the handled message
    /\ UNCHANGED <<high_q, low_q, connections, in_param>>

(* Incoming message on in_param *)
(* check that in_param is not full already *)
Message(id, msg, len) ==
    /\ Len(in_param[id]) < I
    /\ handle' = [ handle EXCEPT !.b = TRUE ]
    /\ in_param' = [ in_param EXCEPT ![id] = Append(@, <<msg, len>>) ]
    /\ UNCHANGED <<state, counter, high_q, low_q, quota, connections, waiting>>

(* Pop a message from one of the queues, enables Handle *)
Pop(id) ==
    /\ handle.b
    /\ ValidMsgInQueue
    /\ IF high_q # <<>>
       THEN \* take msg from high_q
         LET msg == Head(high_q)
         IN /\ handle' = [ handle EXCEPT !.msg = Append(@, <<TRUE>> \o msg) ]
            /\ high_q' = Tail(high_q)
            /\ UNCHANGED low_q
       ELSE \* take msg from low_q
         LET msg == Head(low_q)
         IN /\ handle' = [ handle EXCEPT !.msg = Append(@, <<FALSE>> \o msg) ]
            /\ low_q' = Tail(low_q)
            /\ UNCHANGED high_q
    /\ UNCHANGED <<state, counter, quota, waiting, connections, in_param>>

(* When we are not handling data or already waiting for data, we can enable Waiter *)
Wait_data ==
    /\ ~handle.b
    /\ ~waiting
    /\ queuesEmpty
    /\ waiting' = TRUE
    /\ UNCHANGED <<state, counter, high_q, low_q, quota, connections, handle, in_param>>

(* When waiting for data, once we get a msg from in_param, we place it in the appropriate queue *)
Waiter(id) ==
    /\ waiting
    /\ in_param[id] # <<>>
    /\ IF queuesEmpty
       THEN waiting' = FALSE
       ELSE UNCHANGED waiting
    /\ LET hd == Head(in_param[id])
           msg == <<id, hd[1], hd[2]>>
       IN IF state.quota[id] > 0
          THEN /\ high_q' = Append(high_q, msg)
               /\ UNCHANGED low_q
          ELSE /\ low_q' = Append(low_q, msg)
               /\ UNCHANGED high_q
    /\ in_param' = [ in_param EXCEPT ![id] = Tail(@) ]
    /\ UNCHANGED <<state, counter, quota, connections, handle>>

(* When the scheduler quota < 0, we can update the quota and rearrange the queues *)
Update_quota ==
    /\ quota < 0
    /\ quota' = min(quota, 0) + Max_speed
    /\ IF low_q # <<>>
       THEN /\ high_q' = SelectSeq(low_q, PosQuota)
            /\ low_q'  = SelectSeq(low_q, NonPosQuota)
       ELSE UNCHANGED <<low_q, high_q>>
    /\ UNCHANGED <<counter, waiting, connections, handle, in_param>>

-----------------------------------------------------------------------------

(* Actions *)
Create_conn == \E id \in 0..M: Create_connection(id)

Close_conn == \E id \in connections: Close_connection(id)

Popping == \E id \in connections: Pop(id)

Waiting == \E id \in connections: Waiter(id)

Incoming_msg ==
    \E id \in connections, msg \in Messages, len \in 1..S: Message(id, msg, len)

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

(* Specification *)
Spec == Init /\ [][Next]_vars

=============================================================================
