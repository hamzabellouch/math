# The Unique Games Conjecture and optimal approximation thresholds

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [The Unique Games Theorem](../../preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf)
- [A Direct Proof of Optimal Max-Cut Hardness](../../preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf)
- [The Factor-Two Hardness Threshold for Vertex Cover](../../preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf)
- [Constant-factor hardness of Min-UnCut](../../preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf)
- [Constant-factor hardness of directed feedback vertex set](../../preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf)

## Scope

The Unique Games conjecture asks for hardness of distinguishing nearly satisfiable unique games from games of very small value. The formalized result gives, for every fixed $0<\varepsilon,\delta<1/2$, a deterministic polynomial-time reduction from binary 3SAT to nonempty unweighted simple bipartite unique games. Satisfiable inputs have value at least $1-\varepsilon$ and unsatisfiable inputs have value at most $\delta$. The alphabet is a fixed $\mathbb F_2^s$ depending only on the errors, and every constraint is a translation.

The formalized result establishes hardness of approximating Max-Cut beyond the Goemans–Williamson constant $\alpha_{\mathrm{GW}}$. For every fixed $\alpha_{\mathrm{GW}}<\alpha\le1$, it gives a deterministic polynomial-time reduction from binary 3SAT to a strictly separated Max-Cut gap on finite simple unweighted graphs. The reduction includes the explicit positive integer scaling used in the gap statement.

The formalized result gives the factor-two hardness threshold for Vertex Cover. For each integer $m\ge4$, a polynomial-time reduction from binary 3SAT produces simple unweighted graphs with cover density below $1/2+1/m$ on satisfiable inputs and above $1-1/m$ on unsatisfiable inputs. Consequently, any polynomial-time approximation with a fixed factor $1\le\alpha<2$ would give a polynomial-time decision algorithm for 3SAT. No assumption that $P\ne NP$ is built into the statement.

Min-UnCut minimizes the number of edges left uncut by a bipartition. The formalization constructs a deterministic reduction from encoded $3$-SAT formulas to finite simple unweighted Min-UnCut instances with arbitrarily large fixed multiplicative gaps. For every integer $K\ge2$, satisfiable formulas give optimum at most the output threshold, while unsatisfiable formulas give optimum strictly greater than $K$ times that threshold. Runtime and output length are polynomial for each fixed $K$, establishing hardness for every fixed approximation factor greater than one.

A directed feedback vertex set meets every directed cycle. The formalization proves hardness of approximating the minimum such set within any fixed constant factor. For every real factor $A\ge1$ and every language in NP, it constructs a polynomial-time gap reduction to unweighted directed graphs with the stated completeness and soundness separation. Thus a fixed-factor polynomial-time approximation would imply a polynomial-time algorithm for every NP language.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Unique Games gap reduction | [UniqueGamesTheorem.lean](../ComparatorChallenges/UniqueGamesTheorem.lean) |
| Optimal Max-Cut hardness gap | [OptimalMaxCut.lean](../ComparatorChallenges/OptimalMaxCut.lean) |
| Vertex Cover gap and factor-two hardness | [VertexCover.lean](../ComparatorChallenges/VertexCover.lean) |
| Arbitrary constant-factor hardness of Min-UnCut | [MinUncut.lean](../ComparatorChallenges/MinUncut.lean) |
| Constant-factor hardness of directed feedback vertex set | [DirectedFeedback.lean](../ComparatorChallenges/DirectedFeedback.lean) |
