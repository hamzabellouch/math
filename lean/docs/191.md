# A power improvement in the Heilbronn triangle lower bound

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [A power improvement in the Heilbronn triangle lower bound](../../preprints/A-power-improvement-in-the-Heilbronn-triangle-lower-bound-September-25-2026/main.pdf)

## Scope

Heilbronn's triangle problem asks how large the smallest triangle determined by $n$ points in the unit square can be. The formalization constructs an unbounded sequence of sizes $n$ and point sets for which every triangle has area at least $n^{-2+\eta}$, for one fixed $\eta>0$. It consequently refutes the proposed upper bound of order $n^{-2+\varepsilon}$ for every $\varepsilon>0$. The linked construction is for an unbounded sequence of sizes; the paper's statement for every sufficiently large $n$ is broader.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Power improvement for the smallest Heilbronn triangle | [HeilbronnTriangle.lean](../ComparatorChallenges/HeilbronnTriangle.lean) |
