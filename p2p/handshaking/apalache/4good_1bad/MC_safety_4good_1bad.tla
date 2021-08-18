---- MODULE MC_safety_4good_1bad ----

EXTENDS Handshaking, TLC

\* @type: Set(Int);
Bad_nodes == 0..0

\* @type: Set(Int);
Good_nodes == 1..4

\* @type: Int;
Max == 3

\* @type: Int;
Min == 1

\* @type: Int;
Min_peers == 2

=====================================
