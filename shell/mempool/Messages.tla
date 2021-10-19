---- MODULE Messages ----

EXTENDS Sequences

CONSTANT Nodes, Mempool, Blocks

INSTANCE Operations

\* Operation
\* Advertisement request/response
\* any others?

MsgTypes == { "Head", "GetHead", "Operation" }
AdvContents == Mempool
OpContents == Operations
Messages ==
    [ type : {"Head"},      from : Nodes, contents : Blocks \X AdvContents ] \cup
    [ type : {"GetHead"},   from : Nodes ] \cup
    [ type : {"Operation"}, from : Nodes, contents : OpContents ]

=========================
