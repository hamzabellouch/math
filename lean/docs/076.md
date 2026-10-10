# Real ultraflat Littlewood polynomials and unbounded binary merit factors

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Asymptotically minimal maxima of real Littlewood polynomials](../../preprints/Asymptotically-minimal-maxima-of-real-Littlewood-polynomials-September-23-2026/paper.pdf)

## Scope

The formalization gives real Littlewood polynomials of every sufficiently large length whose maximum modulus on the unit circle is at most $(1+\eta)\sqrt N$ for any fixed $\eta>0$. Thus the smallest possible maximum is asymptotically minimal through all integer lengths.

A further statement chooses one family of real sign polynomials for all lengths such that, for every fixed finite $p>0$, the $L^p$ mean of $\bigl||P_N(z)|/\sqrt N-1\bigr|$ on the unit circle tends to zero. The results are existential and do not give an effective convergence rate or a signing algorithm.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Asymptotically minimal Littlewood maximum | [AsymptoticallyMinimalLittlewood.lean](../ComparatorChallenges/AsymptoticallyMinimalLittlewood.lean) |
| Finite-exponent flatness of one all-length Littlewood family | [LittlewoodFiniteFlatness.lean](../ComparatorChallenges/LittlewoodFiniteFlatness.lean) |
