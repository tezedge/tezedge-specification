---- MODULE MC_safety_2good_8bad ----

EXTENDS Handshaking, TLC

\* @type: Set(Int);
Bad_nodes == 0..7

\* @type: Set(Int);
Good_nodes == 8..9

\* @type: Int;
Max == 5

\* @type: Int;
Min == 1

\* @type: Int;
Min_peers == 3

=====================================
