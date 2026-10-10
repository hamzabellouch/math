# Boolean functions violate the square-root degree bound by arbitrary factors

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Unbounded Violations of the Square-Root Degree Bound](../../preprints/Unbounded-Violations-of-the-Square-Root-Degree-Bound-September-26-2026/Unbounded-Violations-of-the-Square-Root-Degree-Bound-September-26-2026.pdf)

## Scope

The formalization disproves the Gopalan–Servedio square-root degree conjecture by an unbounded factor. For every $C>0$, it gives a nonconstant Boolean function on a finite sign cube for which the sum of its linear Fourier coefficients exceeds $C\sqrt{\deg f}$, where $\deg f$ is its real multilinear degree.

It also proves that the ratio of the sum of the absolute values of those coefficients to $\sqrt{\deg f}$ is unbounded among positive-degree Boolean functions.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Unbounded violations of the square-root Fourier-degree bound | [SquareRootDegree.lean](../ComparatorChallenges/SquareRootDegree.lean) |
