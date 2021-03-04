---- MODULE MC ----

EXTENDS HighLevel, TLC

peer_threshold == 2

connection_threshold == 1

num_nodes == 2

num_joins == 2

size_bound == 1

Inv == TypeOK!TypeOK

Prop1 == Properties!AllNodesHaveJoined

Prop2 == Properties!AllNodesHaveSameState

\* For Apalache
UNROLL_TIMES_isSubSeq == 2 * size_bound
UNROLL_DEFAULT_isSubSeq == <<>>

UNROLL_TIMES_TypeOK_isSubSeq == 2 * size_bound
UNROLL_DEFAULT_TypeOK_isSubSeq == <<>>

UNROLL_TIMES_Properties_isSubSeq == 2 * size_bound
UNROLL_DEFAULT_Properties_isSubSeq == <<>>

UNROLL_TIMES_Properties_Act_isSubSeq == 2 * size_bound
UNROLL_DEFAULT_Properties_Act_isSubSeq == <<>>

===================
