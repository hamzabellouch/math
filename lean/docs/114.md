# Approximate counting of common integer polymatroid bases

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Approximate counting of common bases of two matroids](../../preprints/Approximate-counting-of-common-bases-of-two-matroids-September-23-2026/main.pdf)

## Scope

The formalized result gives a fully polynomial randomized approximation scheme for the number of common bases of two equal-rank matroids on an enumerated finite ground set, using independence oracles. For rational $0<\varepsilon,\delta<1$, the nonnegative rational output has relative error at most $\varepsilon$ with probability at least $1-\delta$. A zero count produces zero on every execution. Oracle calls and bit operations have polynomial bounds on every random tape in the input size, $\varepsilon^{-1}$, and $\log(\delta^{-1})$.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| FPRAS for common matroid bases | [CommonBasesFPRAS.lean](../ComparatorChallenges/CommonBasesFPRAS.lean) |
