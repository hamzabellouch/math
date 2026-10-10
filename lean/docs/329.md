# A counterexample to metric-entropy duality

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Counterexamples to the duality conjecture for metric entropy](../../preprints/Counterexamples-to-the-duality-conjecture-for-metric-entropy-September-24-2026/main.pdf)

## Scope

Metric-entropy duality predicts a universal comparison between covering numbers of convex bodies and their polars. The formalized result disproves such a comparison: for every $a,b\ge1$, there is an origin-symmetric convex body $K$ in a positive finite dimension with $\log N(K,B_\infty)>b\log N(B_\infty^\circ,a^{-1}K^\circ)$, where $N$ is the least number of translates in a finite cover. A further construction makes the dual-to-primal logarithmic entropy ratio tend to zero as the dimension grows.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Counterexample to metric-entropy duality | [MetricEntropyDuality.lean](../ComparatorChallenges/MetricEntropyDuality.lean) |
