----------------------------- MODULE Scheduler -----------------------------

EXTENDS FiniteSets, Naturals, Integers, Sequences

CONSTANTS Max_read,     \* read constant
          Max_write,    \* write constant
          Messages,     \* set of possible messages
          M,            \* maximum number of connections for scheduler to handle
          N,            \* maximum counter value
          S,            \* maximum size of msg
          Q,            \* maximum quota value
          HL,           \* high_q/low_q queue size bound
          IO,           \* in_param queue size bound
          None          \* null value

VARIABLES \* read variables
          in_state, in_counter, in_high_q, in_low_q,
          in_quota, in_waiting, in_handle, in_param,
          \* write variables
          out_state, out_counter, out_high_q, out_low_q,
          out_quota, out_waiting, out_handle, out_param,
          \* shared variable
          connections

vars ==
    <<in_state, in_counter, in_high_q, in_low_q,
      in_quota, in_waiting, in_handle, in_param,
      out_state, out_counter, out_high_q, out_low_q,
      out_quota, out_waiting, out_handle, out_param,
      connections>>

-----------------------------------------------------------------------------

\* basic helper functions

min(n, m) == IF n > m THEN m ELSE n

some(f) == { i \in DOMAIN f : f[i] # None }

(* Sum of optional-valued function values *)
RECURSIVE sum(_)
sum(f) ==
    IF Cardinality(some(f)) = 0
    THEN 0
    ELSE
      LET x == CHOOSE _x \in some(f) : TRUE
          g == [ y \in (some(f) \ {x}) |-> f[y] ]
      IN f[x] + sum(g)

RECURSIVE _divide(_, _, _)
_divide(dividend, divisor, count) ==
    IF dividend < divisor
    THEN IF divisor <= 2 * dividend
         THEN count + 1
         ELSE count
    ELSE _divide(dividend - divisor, divisor, count + 1)

divide(a, b) == _divide(a, b, 0)

(* Approximate average of optional-valued function *)
avg(f) ==
    LET tot == sum(f)
        num == Cardinality(some(f))
    IN  divide(tot, num)

(* All-in-one-step update of state quotas *)
(* update of r1 = result[1], update of r2 = result[2] *)
RECURSIVE update(_, _, _, _, _)
update(s, r1, r2, x1, x2) ==
    IF s = {}
    THEN <<r1, r2>>
    ELSE
      LET id == CHOOSE x \in s : TRUE
          new1 == [ r1 EXCEPT !.quota[id] = min(@, 0) + x1 ]
          new2 == [ r2 EXCEPT !.quota[id] = min(@, 0) + x2 ]
      IN
        update(s \ {id}, new1, new2, x1, x2)

-----------------------------------------------------------------------------

(* Read/Write scheduler instances *)
ReadScheduler ==
    INSTANCE RWScheduler
    WITH state <- in_state, counter <- in_counter, high_q <- in_high_q,
         low_q <- in_low_q, quota <- in_quota, waiting <- in_waiting,
         handle <- in_handle, Max_speed <- Max_read, I <- IO

WriteScheduler ==
    INSTANCE RWScheduler
    WITH state <- out_state, counter <- out_counter, high_q <- out_high_q,
         low_q <- out_low_q, quota <- out_quota, waiting <- out_waiting,
         handle <- out_handle, in_param <- out_param, Max_speed <- Max_write, I <- IO

(* Initial state *)
Init ==
    /\ ReadScheduler!Init
    /\ WriteScheduler!Init

-----------------------------------------------------------------------------

(* Register a connection *)
(* ONLY the following variables can change:
 - connections
 - in_state
 - out_state *)
Connect(id) ==
    /\ id \notin connections
    /\ ReadScheduler!Create_connection(id)
    /\ WriteScheduler!Create_connection(id)
    /\ UNCHANGED
        <<in_counter, in_high_q, in_low_q, in_quota,
          in_waiting, in_handle, in_param,
          out_counter, out_high_q, out_low_q, out_quota,
          out_waiting, out_handle, out_param>>

(* Close an established connection *)
(* ONLY the following variables can change:
 - connections
 - in_state
 - out_state *)
Close(id) ==
    /\ ReadScheduler!Close_connection(id)
    /\ WriteScheduler!Close_connection(id)
    /\ UNCHANGED
        <<in_counter, in_high_q, in_low_q, in_quota,
          in_waiting, in_handle, in_param,
          out_counter, out_high_q, out_low_q, out_quota,
          out_waiting, out_handle, out_param>>

(* Reset quotas when < 0 *)
(* ONLY the following variables can change:
 - in_state
 - in_quota
 - in_high_q
 - in_low_q
 - out_state
 - out_quota
 - out_high_q
 - out_low_q *)
Reset_quota ==
    /\ LET inflow  == in_counter
           outflow == out_counter
           nb_conn == Cardinality(connections)
       IN
         IF nb_conn = 0
         THEN /\ \/ /\ ReadScheduler!Update_quota
                    /\ UNCHANGED <<out_high_q, out_low_q, out_quota>>
                 \/ /\ WriteScheduler!Update_quota
                    /\ UNCHANGED <<in_high_q, in_low_q, in_quota>>
                 \/ /\ ReadScheduler!Update_quota
                    /\ WriteScheduler!Update_quota
              /\ UNCHANGED <<in_state, out_state>>
         ELSE
           LET fair_r == divide(inflow, nb_conn)
               fair_w == divide(outflow, nb_conn)
               news == update(connections, in_state, out_state, fair_r, fair_w)
               s1 == news[1]
               s2 == news[2]
           IN
             /\ in_state' = s1
             /\ out_state' = s2
             /\ \/ /\ ReadScheduler!Update_quota
                   /\ UNCHANGED <<out_high_q, out_low_q, out_quota>>
                \/ /\ WriteScheduler!Update_quota
                   /\ UNCHANGED <<in_high_q, in_low_q, in_quota>>
                \/ /\ ReadScheduler!Update_quota
                   /\ WriteScheduler!Update_quota
    /\ UNCHANGED
        <<in_counter, in_waiting, in_handle, in_param, connections,
          out_counter, out_waiting, out_handle, out_param>>

-----------------------------------------------------------------------------

(* Incoming/reading *)

(*  *)
(* ONLY the following variables can change:
 - in_handle
 - in_param *)
In_message(id, msg, len) ==
    /\ ReadScheduler!Message(id, msg, len)
    /\ UNCHANGED
        <<in_state, in_counter, in_high_q, in_low_q,
          in_quota, in_waiting, connections,
          out_state, out_counter, out_high_q, out_low_q,
          out_quota, out_waiting, out_handle, out_param>>

(* Read a message from in_high_q or in_low_q, enables In_handle *)
(* ONLY the following variables can change:
 - in_handle
 - one of {in_high_q, in_low_q} *)
Read(id) ==
    /\ ReadScheduler!Pop(id)
    /\ UNCHANGED
        <<in_state, in_counter, in_quota,
          in_waiting, in_param, connections,
          out_state, out_counter, out_high_q, out_low_q,
          out_quota, out_waiting, out_handle, out_param>>

(*  *)
(* ONLY the following variables can change:
 - in_state
 - in_counter
 - in_waiting
 - in_quota
 - in_handle *)
In_handle ==
    /\ ReadScheduler!Handle
    /\ UNCHANGED
        <<in_high_q, in_low_q, in_param, connections,
          out_state, out_counter, out_high_q, out_low_q,
          out_quota, out_waiting, out_handle, out_param>>

(*  *)
(* ONLY the following variables can change:
 - in_waiting *)
In_wait_data ==
    /\ ReadScheduler!Wait_data
    /\ UNCHANGED
        <<in_state, in_counter, in_high_q, in_low_q, 
          in_quota, in_handle, in_param, connections,
          out_state, out_counter, out_high_q, out_low_q,
          out_quota, out_waiting, out_handle, out_param>>

(*  *)
(* ONLY the following variables can change:
 - in_param
 - in_waiting
 - in_high_q
 - in_low_q *)
In_waiter(id) ==
    /\ ReadScheduler!Waiter(id)
    /\ UNCHANGED
        <<in_state, in_counter, in_quota, in_handle, connections,
          out_state, out_counter, out_high_q, out_low_q,
          out_quota, out_waiting, out_handle, out_param>>

-----------------------------------------------------------------------------

(* Outgoing/writing *)

(*  *)
(* ONLY the following variables can change:
 - out_handle
 - out_param *)
Out_message(id, msg, len) ==
    /\ WriteScheduler!Message(id, msg, len)
    /\ UNCHANGED
        <<out_state, out_counter, out_high_q, out_low_q,
          out_quota, out_waiting, connections,
          in_state, in_counter, in_high_q, in_low_q,
          in_quota, in_waiting, in_handle, in_param>>

(* Write a message from out_high_q or out_low_q, enables Out_handle *)
(* ONLY the following variables can change:
 - out_handle
 - one of {out_high_q, out_low_q} *)
Write(id) ==
    /\ WriteScheduler!Pop(id)
    /\ UNCHANGED
        <<out_state, out_counter, out_quota,
          out_waiting, out_param, connections,
          in_state, in_counter, in_high_q, in_low_q,
          in_quota, in_waiting, in_handle, in_param>>

(*  *)
(* ONLY the following variables can change:
 - out_state
 - out_counter
 - out_waiting
 - out_quota
 - out_handle *)
Out_handle ==
    /\ WriteScheduler!Handle
    /\ UNCHANGED
        <<out_high_q, out_low_q, out_param, connections,
          in_state, in_counter, in_high_q, in_low_q,
          in_quota, in_waiting, in_handle, in_param>>

(*  *)
(* ONLY the following variables can change:
 - out_waiting *)
Out_wait_data ==
    /\ WriteScheduler!Wait_data
    /\ UNCHANGED
        <<out_state, out_counter, out_high_q, out_low_q, 
          out_quota, out_handle, out_param, connections,
          in_state, in_counter, in_high_q, in_low_q,
          in_quota, in_waiting, in_handle, in_param>>

(*  *)
(* ONLY the following variables can change:
 - out_param
 - out_waiting
 - out_high_q
 - out_low_q *)
Out_waiter(id) ==
    /\ WriteScheduler!Waiter(id)
    /\ UNCHANGED
        <<out_state, out_counter, out_quota, out_handle, connections,
          in_state, in_counter, in_high_q, in_low_q,
          in_quota, in_waiting, in_handle, in_param>>

\* Work_loop

-----------------------------------------------------------------------------

(* Actions *)

\* Maintanence
\* Parameterized
Register == \E id \in 0..M : Connect(id)

Close_conn == \E id \in connections : Close(id)

\* Unparameterized: Reset_quota


\* Read
\* Parameterized
Incoming_message ==
    \E id \in connections, msg \in Messages, len \in 0..S : In_message(id, msg, len)

Read_one == \E id \in connections : Read(id)

Incoming_waiter == \E id \in connections : In_waiter(id)

\* Unparameterized: In_handle, In_wait_data


\* Write
\* Parameterized
Outgoing_message ==
    \E id \in connections, msg \in Messages, len \in 0..S : Out_message(id, msg, len)

Write_one == \E id \in connections : Write(id)

Outgoing_waiter == \E id \in connections : Out_waiter(id)

\* Unparameterized: Out_handle, Out_wait_data


(* Possible next steps *)
Next ==
       \* Maintanence
    \/ Close_conn
    \/ Register
    \/ Reset_quota
       \* Read actions
    \/ In_handle
    \/ In_wait_data
    \/ Incoming_message
    \/ Read_one
    \/ Incoming_waiter
       \* Write actions
    \/ Out_handle
    \/ Out_wait_data
    \/ Outgoing_message
    \/ Write_one
    \/ Outgoing_waiter

-----------------------------------------------------------------------------

(* Specification *)
Spec == Init /\ [][Next]_vars

=============================================================================
