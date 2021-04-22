---- MODULE MC_safety ----

EXTENDS Handshaking_nack_peers, TLC

\* @type: Set(Int);
Bad_nodes == 0..0

\* @type: Set(Int);
Good_nodes == 1..2

\* @type: Int;
Max == 2

\* @type: Int;
Min == 1

\* @type: Int;
Min_peers == 2

==========================
