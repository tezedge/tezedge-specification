---- MODULE Messages ----

CONSTANT Nodes, Mempool

INSTANCE Operations

\* Operation
\* Advertisement request/response
\* any others?

MsgTypes == { "Advertise", "Request", "Operation" }
AdvContents == Mempool
OpContents == Operations
Messages ==
    [ type : {"Advertise"}, from : Nodes, contents : AdvContents ] \cup
    [ type : {"Operation"}, from : Nodes, contents : OpContents ] \cup
    [ type : {"Request"},   from : Nodes ]

=========================
