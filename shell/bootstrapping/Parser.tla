---- MODULE Parser ----

EXTENDS Naturals, Sequences

Data == STRING \X Seq(STRING \cup Nat)

parse(path) == CHOOSE x \in Seq(Data) : TRUE

=======================
