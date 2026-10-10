# The Erdős–Gallai cycle-decomposition conjecture

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [A linear cycle-and-edge decomposition of every graph](../../preprints/A-linear-cycle-and-edge-decomposition-of-every-graph-September-24-2026/main.pdf)

## Scope

The Erdős–Gallai cycle-decomposition conjecture asks for a linear bound on the number of cycles and single edges needed to partition a graph's edges. The formalized result gives one absolute constant $C>0$ such that every finite simple graph on $n$ vertices has an edge-disjoint decomposition into at most $Cn$ cycles or singleton edges. Edgeless and small graphs are included. The optimal value of $C$ is not determined.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Linear cycle-and-edge decomposition | [CycleDecomposition.lean](../ComparatorChallenges/CycleDecomposition.lean) |
