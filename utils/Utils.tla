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

----------------------------------------------------------------------------

(* Common functions *)

\* minimum
min(m, n) == IF m > n THEN n ELSE m

\* maximum
max(m, n) == IF m > n THEN m ELSE n

\* integer division
RECURSIVE _divide(_, _, _)
_divide(n, m, p) ==
    IF n < m
    THEN IF m <= 2 * n
         THEN p + 1
         ELSE p
    ELSE _divide(n - m, m, p + 1)

divide(a, b) == _divide(a, b, 0)

=============================================================================
