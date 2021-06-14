------------------------------- MODULE Utils -------------------------------

EXTENDS FiniteSets, Integers, Naturals, Sequences, TLC

----------------------------------------------------------------------------

(* Sets *)

\* Pick an "arbitrary" element from set S
Pick(S) == CHOOSE x \in S : TRUE

\* Turn a function/sequence into a set
\* @type: (Seq(T)) => Set(T);
ToSet(f) == { f[i] : i \in DOMAIN f }

disjoint(S, T) == S \cap T = {}

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

\* maximum element of a nonempty finite set of naturals
max_set(set) ==
    LET RECURSIVE _max_set(_, _)
        _max_set(S, curr) ==
            CASE S = {} -> curr
              [] OTHER -> LET x == Pick(S) IN _max_set(S \ {x}, max[x, curr])
    IN CASE set /= {} -> LET x == Pick(set) IN _max_set(set \ {x}, x)
         [] OTHER -> -1

\* minimum element of a nonempty finite set of naturals
min_set(set) ==
    LET RECURSIVE _min_set(_, _)
        _min_set(S, curr) ==
            CASE S = {} -> curr
              [] OTHER -> LET x == Pick(S) IN _min_set(S \ {x}, min[x, curr])
    IN CASE set /= {} -> LET x == Pick(set) IN _min_set(set\ {x}, x)
         [] OTHER -> -1

----------------------------------------------------------------------------

(* Functions/Sequences *)

\* Enumerable set of sequences of elements from S with length = n
SeqOfLen(S, n) ==
    CASE n < 0 -> {}
      [] OTHER -> [ 1..n -> S ]

\* Enumerable set of sequences of elements from S with length <= n
Seq_n(S, n) == UNION { SeqOfLen(S, l) : l \in 0..n }

\* Enumerable set of nonempty sequences of length <= n
NESeq_n(S, n) == { f \in Seq_n(S, n) : f /= <<>> }

\* Enumerable set of pairs of elements from sets S1 and S2
\* @type: (Set(A), Set(B)) => Set(<<A, B>>);
Pairs(S1, S2) == { <<x1, x2>> : x1 \in S1, x2 \in S2 }

\* Nonempty sequences of elements from set S
NESeq(S) == Seq(S) \ {<<>>}

\* remove (all occurrences of) an element from a sequence
Remove(seq, elem) ==
    LET RECURSIVE _remove(_, _, _)
        _remove(s, e, acc) ==
            CASE s = <<>> -> acc
              [] e /= Head(s) -> _remove(Tail(s), e, Append(acc, Head(s)))
              [] OTHER -> _remove(Tail(s), e, acc)
    IN _remove(seq, elem, <<>>)

\* (finite) subsequence predicate
RECURSIVE isSubSeq(_, _)
isSubSeq(s1, s2) ==
    \/ s1 = <<>>
    \/ CASE { j \in DOMAIN s2 : s2[j] = Head(s1) } = {} -> FALSE
         [] OTHER ->
            LET n == max_set(DOMAIN s2)
                i == min_set({ j \in DOMAIN s2 : s2[j] = Head(s1) })
                s == [ j \in (i + 1)..n |-> s2[j] ]
            IN isSubSeq(Tail(s1), s)

\* Selects the first element that satisfies the predicate
\* if no element satisfies the predicate, then return <<>>
Select(seq, test(_)) ==
    LET RECURSIVE select(_)
        select(s) ==
            CASE s = <<>> -> <<>>
              [] test(Head(s)) -> Head(s)
              [] OTHER -> select(Tail(s))
    IN select(seq)

\* returns TRUE if all elements of [seq] satisfy [test], FALSE otherwise
Forall(seq, test(_)) ==
    LET RECURSIVE forall(_, _)
        forall(s, acc) ==
          IF s = <<>>
          THEN acc
          ELSE /\ acc
               /\ forall(Tail(s), acc /\ test(Head(s)))
    IN forall(seq, TRUE)

\* returns TRUE if any elements of [seq] satisfy [test], FALSE otherwise
Exists(seq, test(_)) ==
    LET RECURSIVE exists(_, _)
        exists(s, acc) ==
          IF s = <<>>
          THEN acc
          ELSE \/ acc
               \/ exists(Tail(s), acc \/ test(Head(s)))
    IN exists(seq, FALSE)

Cons(elem, seq) == <<elem>> \o seq

Filter(seq, pred(_)) == SelectSeq(seq, pred)

=============================================================================
