---- MODULE MC_safety_2good_3bad ----

EXTENDS Handshaking, TLC

\* @type: Set(Int);
Bad_nodes == 0..2

\* @type: Set(Int);
Good_nodes == 3..4

\* @type: Int;
Max == 1

\* @type: Int;
Min == 1

=====================================
