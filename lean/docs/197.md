# A torsion-free group algebra that is not directly finite

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two](../../preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf)
- [A Counterexample to the Group-Ring Determinant Conjecture](../../preprints/A-Counterexample-to-the-Group-Ring-Determinant-Conjecture-September-23-2026/paper.pdf)
- [A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Odd Characteristic](../../preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Odd-Characteristic-September-26-2026/paper.pdf)

## Scope

Kaplansky's direct-finiteness conjecture asserts that $ab=1$ implies $ba=1$ for $a,b\in K[G]$, for every field $K$ and group $G$. The formalized results construct a finite field of characteristic two and a group algebra violating this implication. One statement records the counterexample for a finitely generated group; the more detailed construction gives a finitely presented group with an element of odd prime order.

The detailed construction also gives a precise recipe for choosing the data and proves that the required search terminates. The further conclusion that the group is nonsofic is outside these statements.

A nonsingular integer matrix has absolute determinant at least $1$. The group-ring Determinant Conjecture extends this bound to matrices over $\mathbb Z[G]$ for every discrete group $G$. If $T_A$ is the operator induced by such a matrix $A$ on finite direct sums of $\ell^2(G)$, and $\mu_A$ is the spectral measure of $T_A^*T_A$ with respect to the group trace, the conjecture asserts

$\displaystyle \int_{(0,\infty)}\log t\,d\mu_A(t)\ge0,$

with the zero spectral atom omitted. For an invertible square matrix, this is equivalent to its Fuglede–Kadison determinant being at least $1$.

The formalized result contradicts that bound. It gives a finitely generated group $G$ and an $n\times n$ matrix over $\mathbb Z[G]$, with $n\ge1$, that is invertible over $\mathbb Q[G]$. Its bounded left-regular operator is invertible and has determinant strictly between $0$ and $1$.

The formalization uses the trace of $\log(T^*T)$ to define the determinant for the invertible operator $T$. The paper's additional spectral-measure integral conclusion is not included.

Kaplansky's direct-finiteness conjecture asserts that $ab=1$ implies $ba=1$ in every group algebra over a field. Let $p$ be the smallest prime divisor of $\bigl(\binom{1200}{600}!\bigr)^2+1$; this prime is odd. The formalized result constructs a field $K$ of order $p^4$, a finitely generated group $G$ with torsion, and elements $a,b$ violating this implication. The associated cellular automaton on all configurations $K^G$ is injective but not surjective.

The formalization also contains fixed-field transfer results, separate from the statement linked below.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Finitely presented characteristic-two counterexample | [KaplanskyFinitelyPresented.lean](../ComparatorChallenges/KaplanskyFinitelyPresented.lean) |
| Characteristic-two direct-finiteness counterexample | [KaplanskyDirectFiniteness.lean](../ComparatorChallenges/KaplanskyDirectFiniteness.lean) |
| Group-ring determinant counterexample | [GroupRingDeterminant.lean](../ComparatorChallenges/GroupRingDeterminant.lean) |
| Prescribed odd-characteristic counterexample | [OddKaplansky.lean](../ComparatorChallenges/OddKaplansky.lean) |
