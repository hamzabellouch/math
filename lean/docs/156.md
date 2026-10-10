# Borsuk's conjecture fails in dimension nine

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [A nine-dimensional counterexample to Borsuk's covering assertion](../../preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf)

## Scope

Borsuk's conjecture predicts that every bounded subset of $\mathbb R^d$ can be covered by $d+1$ sets of strictly smaller diameter. The formalized counterexample is the compact set of rank-one orthogonal projectors onto lines in $\mathbb R^4$, with the Frobenius metric. It lies in the nine-dimensional affine space of trace-one symmetric matrices, has diameter $\sqrt2$, and cannot be covered by ten arbitrary sets of smaller diameter.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Nine-dimensional Borsuk counterexample | [BorsukNine.lean](../ComparatorChallenges/BorsukNine.lean) |
