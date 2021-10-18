---- MODULE Messages ----

EXTENDS Sequences

CONSTANT Nodes, Mempool, BlockHashes

INSTANCE Operations

\* Operation
\* Advertisement request/response
\* any others?

MsgTypes == { "Head", "GetHead", "Operation", "GetOperations" }
AdvContents == Mempool
OpContents == Operations
Messages ==
    [ type : {"Head"},          from : Nodes, contents : BlockHashes \X AdvContents ] \cup
    [ type : {"GetHead"},       from : Nodes ] \cup
    [ type : {"Operation"},     from : Nodes, contents : OpContents ] \cup
    [ type : {"GetOperations"}, from : Nodes, contents : Seq(OpHashes) ]

=========================
