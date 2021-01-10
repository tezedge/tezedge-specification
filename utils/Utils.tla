------------------------------- MODULE Utils -------------------------------

EXTENDS FiniteSets, Integers, Naturals, Sequences, TLC

----------------------------------------------------------------------------

(* Sets *)

\* Pick an "arbitrary" element from set S
Pick(S) == CHOOSE x \in S : TRUE

\* Turn a function/sequence into a set
ToSet(f) == { f[i] : i \in DOMAIN f }

\* Nonempty subsets of S
NESubsets(S) == SUBSET S \ {{}}

\* Subsets of size <= n
Subsets_n(S, n) == { s \in SUBSET S : Cardinality(s) <= n }

----------------------------------------------------------------------------

(* Common functions/operators *)

\* minimum
min[m, n \in Int] == IF m > n THEN n ELSE m

\* maximum
max[m, n \in Int] == IF m > n THEN m ELSE n

\* integer division
divide[a, b \in Nat] ==
    LET _divide[n, m \in Nat, p \in Nat] ==
        IF n < m
        THEN IF m <= 2 * n
             THEN p + 1
             ELSE p
        ELSE _divide[n - m, m, p + 1]
    IN
      _divide[a, b, 0]

\* maximum element of a nonempty finite set
RECURSIVE _max_set(_, _)
_max_set(S, curr) ==
    CASE S = {} -> curr
      [] OTHER -> LET x == Pick(S) IN _max_set(S \ {x}, max[x, curr])

max_set(S) == CASE S # {} -> LET x == Pick(S) IN _max_set(S \ {x}, x)

\* minimum element of a nonempty finite set
RECURSIVE _min_set(_, _)
_min_set(S, curr) ==
    CASE S = {} -> curr
      [] OTHER -> LET x == Pick(S) IN _min_set(S \ {x}, min[x, curr])

min_set(S) == CASE S # {} -> LET x == Pick(S) IN _min_set(S \ {x}, x)

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

\* remove (all occurrences of) an element from a sequence
RECURSIVE _remove(_, _, _)
_remove(s, e, acc) ==
    CASE s = <<>> -> acc
      [] e # Head(s) -> _remove(Tail(s), e, Append(acc, Head(s)))
      [] OTHER -> _remove(Tail(s), e, acc)

Remove(s, e) == _remove(s, e, <<>>)

\* (finite) subsequence predicate
RECURSIVE isSubSeq(_, _)
isSubSeq(s1, s2) ==
    \/ s1 = <<>>
    \/ CASE { j \in DOMAIN s2 : s2[j] = Head(s1) } = {} -> FALSE
         [] OTHER ->
            LET n == max_set(DOMAIN s2)
                i == min_set({ j \in DOMAIN s2 : s2[j] = Head(s1) })
                s == [ j \in (i + 1)..n |-> s2[j] ]
            IN
              isSubSeq(Tail(s1), s)

=============================================================================
