# A counterexample to Kaplansky’s zero-divisor conjecture

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [A Torsion-Free Group Algebra with Zero Divisors](../../preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf)

## Scope

Kaplansky's zero-divisor conjecture asserts that the group algebra of a torsion-free group over a field has no zero divisors. The formalized result constructs a finitely presented torsion-free group $G$ and nonzero elements $\alpha,\beta\in\mathbb F_2[G]$ with $\alpha\beta=0$, giving a counterexample.

The same group admits a finite two-dimensional classifying space $K(G,1)$.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Torsion-free group-algebra counterexample | [TorsionFreeZeroDivisors.lean](../ComparatorChallenges/TorsionFreeZeroDivisors.lean) |
