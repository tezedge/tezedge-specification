---- MODULE Parser ----

EXTENDS Naturals, Sequences

Data == STRING \X STRING \X Seq(Nat)

parse(path) == CHOOSE x \in Seq(Data) : TRUE

parseActionTrace(path) == parse(path)

=======================
