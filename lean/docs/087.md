# The Mahler conjectures, functional inequalities and polar-product symplectic width

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [The symmetric Mahler conjecture and its equality cases](../../preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf)
- [The Mahler Conjecture for General Convex Bodies](../../preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/paper.pdf)
- [Symplectic Balls in Symmetric Polar Products](../../preprints/Symplectic-Balls-in-Symmetric-Polar-Products-September-22-2026/paper.pdf)

## Scope

The symmetric Mahler conjecture predicts $|K||K^\circ|\ge4^n/n!$ for every origin-symmetric convex body $K\subset\mathbb R^n$. The formalization establishes this for every $n\ge1$ and characterizes equality exactly by invertible linear images of Hanner bodies, built from intervals using Cartesian products and convex-hull joins.

The nonsymmetric Mahler conjecture and the functional inequalities are not included.

The general Mahler conjecture gives a sharp lower bound for the volume product of a convex body and its polar. For every $n\ge1$ and compact convex body $K\subset\mathbb R^n$ with nonempty interior, the formalization proves
$\inf_{z\in\mathrm{int}\,K}|K|\,|(K-z)^\circ|\ge (n+1)^{n+1}/(n!)^2$.
Equality holds exactly when $K$ is a simplex. The paper's functional inequality is outside this selected statement.

For an origin-symmetric convex body $K\subset\mathbb R^n$, $n\ge2$, the formalized result determines the symplectic ball capacity of $\mathrm{int}\,K\times\mathrm{int}\,K^\circ$: its Gromov width is $4$, and every ball of capacity $0<c<4$ embeds symplectically into it. The normalization assigns capacity $\pi r^2$ to a ball of radius $r$.

No boundary smoothness or strict convexity is assumed. An embedding at capacity exactly $4$ is not asserted.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Symmetric Mahler inequality | [MahlerConjecture.lean](../ComparatorChallenges/MahlerConjecture.lean) |
| Symmetric Mahler equality characterization | [SymmetricMahlerEquality.lean](../ComparatorChallenges/SymmetricMahlerEquality.lean) |
| General Mahler inequality and simplex equality cases | [GeneralMahler.lean](../ComparatorChallenges/GeneralMahler.lean) |
| Gromov width of symmetric polar products | [SymmetricPolar.lean](../ComparatorChallenges/SymmetricPolar.lean) |
