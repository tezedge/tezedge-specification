------------------------------- MODULE Utils -------------------------------

EXTENDS FiniteSets, Integers, Naturals, Sequences, TLC

----------------------------------------------------------------------------

(* Functions/Sequences *)

\* Enumerable set of sequences of elements from S with length = n
SeqOfLen(S, n) ==
    CASE n < 0 -> {}
      [] OTHER -> [ 1..n -> S ]

\* Enumerable set of sequences of elements from S with length <= n
Seq_n(S, n) == UNION { SeqOfLen(S, l) : l \in 0..n }

\* Enumerable set of nonempty sequences of length <= n
NESeq_n(S, n) == { f \in Seq_n(S, n) : f # <<>> }

\* Enumerable set of pairs of elements from sets S1 and S2
Pairs(S1, S2) == { <<x1, x2>> : x1 \in S1, x2 \in S2 }

\* Nonempty sequences of elements from set S
NESeq(S) == Seq(S) \ {<<>>}

----------------------------------------------------------------------------

(* Sets *)

\* Pick an "arbitrary" element from set S
Pick(S) == CHOOSE x \in S : TRUE

\* Turn a function/sequence into a set
ToSet(f) == { f[i] : i \in DOMAIN f }

\* Nonempty subsets of S
NESubsets(S) == SUBSET S \ {{}}

=============================================================================
