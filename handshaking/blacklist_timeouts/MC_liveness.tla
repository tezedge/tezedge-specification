---- MODULE MC_liveness ----

EXTENDS Handshaking, TLC

Bad_nodes == 0..0

Good_nodes == 1..2

Max == 2

Min == 1

============================
