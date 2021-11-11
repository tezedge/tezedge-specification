---- MODULE Blocks ----

EXTENDS Integers, Sequences

CONSTANT OpHashes

BlockHashes == Int
Blocks == [ hash : BlockHashes, ops : Seq(OpHashes) ]

block(h, ops) == [ hash |-> h, ops |-> ops ]

=======================
