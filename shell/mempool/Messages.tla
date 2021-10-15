---- MODULE Messages ----

CONSTANT Nodes, Mempool

INSTANCE Operations

\* Operation
\* Advertisement request
\* any others?

MsgTypes == { "Advertise", "Operation" }
AdvContents == Mempool
OpContents == Operations
Messages ==
    [ type : {"Advertise"}, from : Nodes, contents : AdvContents ] \cup
    [ type : {"Operation"}, from : Nodes, contents : OpContents ]

=========================
