# Nagata’s conjecture and maximal Seshadri constants

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Nagata's conjecture for plane curves](../../preprints/Nagatas-Conjecture-for-Plane-Curves-September-23-2026/main.pdf)
- [Maximal Seshadri constants on arbitrary polarized surfaces](../../preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf)

## Scope

Nagata's conjecture asserts that a nonzero effective plane curve of degree $d$, with multiplicities at least $m_i$ at $r\ge10$ very general points, satisfies $\sum_i m_i<d\sqrt r$.

The formalization establishes this inequality simultaneously for all curves and multiplicity vectors outside one countable union of proper Zariski-closed exceptional sets with nonempty complement. Reducible curves, repeated components, and unequal multiplicities are included, in both effective-curve and homogeneous-polynomial formulations. The formalization also includes the passage from homogeneous effective cycles to equations.

The maximality question asks whether the multipoint Seshadri constant reaches the upper bound $\sqrt{L^2/r}$ at very general points once $r$ is sufficiently large. The formalized result establishes this for every smooth integral complex projective surface $S$ and ample line bundle $L$.

For every $r$ above a threshold depending on $(S,L)$, it gives a countable union of proper closed exceptional sets with nonempty complement. Outside it, the constant is $\sqrt{L^2/r}$ and the boundary class defining this Seshadri constant on the point blowup is nef. The threshold is not explicit or uniform over all surfaces.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Nagata's conjecture | [Nagata.lean](../ComparatorChallenges/Nagata.lean) |
| Eventual maximal Seshadri constants | [MaximalSeshadriConstants.lean](../ComparatorChallenges/MaximalSeshadriConstants.lean) |
