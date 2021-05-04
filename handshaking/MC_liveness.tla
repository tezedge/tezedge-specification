---- MODULE MC_liveness ----

EXTENDS Handshaking, TLC

Nodes == 0..2

Good_nodes == 1..2

Max == 2

Min == 1

Conn_attempt == 1

Timeouts == 1

============================
