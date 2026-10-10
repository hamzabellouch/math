# The Benjamini–Schramm nonuniqueness conjecture

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Nonuniqueness of percolation on nonamenable quasi-transitive graphs](../../preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf)

## Scope

The formalization proves the nonuniqueness phase conjecture for Bernoulli bond percolation on infinite connected locally finite nonamenable quasi-transitive graphs. It establishes $p_c<p_{2\to2}\le p_u$ and a common nonempty coupled interval with infinitely many infinite clusters almost surely. For Cayley graphs, the result holds for every finite symmetric generating set of a nonamenable finitely generated group and every $p\in(p_c,p_u)$.

The selected critical estimates include a finite triangle diagram, susceptibility of order $(p_c-p)^{-1}$, percolation probability of order $p-p_c$, cluster-volume tail of order $n^{-1/2}$, and intrinsic and extrinsic radius tails of order $n^{-1}$. Connection probabilities decay exponentially below $p_{2\to2}$.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Nonuniqueness phase and critical laws on quasi-transitive graphs | [BenjaminiSchramm.lean](../ComparatorChallenges/BenjaminiSchramm.lean) |
| Nonuniqueness for every nonamenable Cayley graph | [CayleyPercolation.lean](../ComparatorChallenges/CayleyPercolation.lean) |
