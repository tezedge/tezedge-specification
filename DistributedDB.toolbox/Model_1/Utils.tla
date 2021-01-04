------------------------------- MODULE Utils -------------------------------

EXTENDS FiniteSets, Integers, Naturals, Sequences, TLC

----------------------------------------------------------------------------

(* Sequences *)

SeqOfLen(S, n) ==
    CASE n < 0 -> {}
      [] OTHER -> [ 1..n -> S ]

(* Enumerable set of sequences up to a given length *)
RECURSIVE _Seq_n(_, _, _, _)
_Seq_n(_elems, _size, _curr, _acc) ==
    CASE _curr > _size -> _acc
      [] OTHER -> _Seq_n(_elems, _size, _curr + 1, _acc \cup SeqOfLen(_elems, _curr))

\* Sequences of elements from set S, up to length n
Seq_n(S, n) ==
    CASE n < 0 -> {}
      [] OTHER -> _Seq_n(S, n, 0, {})

NESeq_n(S, n) == { f \in Seq_n(S, n) : f # <<>> }

Pairs(X1, X2) == { <<x1, x2>> : x1 \in X1, x2 \in X2 }

NESeq(S) == Seq(S) \ {<<>>}

----------------------------------------------------------------------------

(* Sets *)

Pick(S) == CHOOSE x \in S : TRUE

ToSet(f) == { f[i] : i \in DOMAIN f }

NE(S) == SUBSET S \ {{}}

----------------------------------------------------------------------------



=============================================================================
