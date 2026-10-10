# The sharp terminal leave in random triangle removal

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [The sharp terminal leave in random triangle removal](../../preprints/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026.pdf)

## Scope

Start with the complete graph on $n$ vertices and repeatedly delete the three edges of a uniformly chosen remaining triangle. The formalization proves that the number of edges at termination, divided by $n^{3/2}$, converges in $L^2$ to $1/(2\sqrt2)$. It also states convergence in probability and convergence of the normalized expectation to the same constant. This is the triangle case of the sharp terminal-leave conjecture of Joos and Kühn.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Sharp terminal edge count in random triangle removal | [TriangleRemoval.lean](../ComparatorChallenges/TriangleRemoval.lean) |
