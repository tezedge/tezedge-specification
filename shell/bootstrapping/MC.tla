---- MODULE MC ----

EXTENDS ActionTraceChecker

Nodes == {"a", "b"}
Min_peers == 0
Max_peers == 10
Max_ops == 10
Max_score == 100
Incr_score == 10
Decr_score == 10
Init_chain == <<genesis>>
Init_head == gen_header
Init_connections == {}

===================
