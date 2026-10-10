# A uniformly discrete counterexample to bounded approximation in Lipschitz-free spaces

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [A uniformly discrete counterexample to bounded approximation in Lipschitz-free spaces](../../preprints/Failure-of-Bounded-Approximation-in-a-Lipschitz-Free-Space-over-a-Uniformly-Discrete-Metric-Space-September-26-2026/main.pdf)

## Scope

Kalton's question asks whether uniform discreteness of a metric space forces its Lipschitz-free space to have the bounded approximation property. The formalization constructs a countable metric space with all distinct points at distance at least one whose real Lipschitz-free space has the approximation property but fails every bounded approximation bound. The metric space is unbounded and not proper.

The earlier quantitative renorming result for real $\ell_1$ is retained: for each integer $p\ge1$, an equivalent complete norm has the $2B_p$-bounded approximation property but fails the $p$-bounded approximation property, where $B_p=300p^2+150p+5$.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Quantitative renorming of real $\ell_1$ | [RealL1Renorming.lean](../ComparatorChallenges/RealL1Renorming.lean) |
| Uniformly discrete Lipschitz-free space with AP but no BAP | [DiscreteLipschitzFree.lean](../ComparatorChallenges/DiscreteLipschitzFree.lean) |
