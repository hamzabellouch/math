# The Lane–Emden and Hénon–Lane–Emden conjectures

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [The Subcritical Hénon–Lane–Emden Conjecture](../../preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/paper.pdf)

## Scope

The formalized result proves nonexistence of positive entire solutions to the subcritical Hénon–Lane–Emden system. For $n\ge2$, $p,q>0$, and real $A,B$ with $(n+A)/(p+1)+(n+B)/(q+1)>n-2$, there are no positive functions, continuous everywhere and $C^2$ off the origin, satisfying $-\Delta u=|x|^A v^p$ and $-\Delta v=|x|^B u^q$ away from the origin. It includes the globally $C^2$ unweighted case for $n\ge3$. The critical equality case is not included.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Subcritical Hénon–Lane–Emden nonexistence | [HenonEmden.lean](../ComparatorChallenges/HenonEmden.lean) |
