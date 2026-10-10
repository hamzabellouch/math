# Planar first-passage geometry and the absence of bigeodesics

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Strict convexity and differentiability of the planar exponential first-passage limit shape](../../preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf)

## Scope

The formalization proves differentiability of the planar first-passage time-constant norm for independent Gamma edge weights of every positive shape and rate. The norm is differentiable away from the origin, and its unit sphere has a $C^1$ boundary. This includes the exponential model, for which the linked statement also gives a unique supporting line at every boundary point.

The paper also claims strict convexity for the exponential limit shape. Strict convexity is outside these selected differentiability statements.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Differentiability of the exponential first-passage limit shape | [PlanarFirstPassage.lean](../ComparatorChallenges/PlanarFirstPassage.lean) |
| Differentiability for every positive Gamma edge-weight law | [GammaPassage.lean](../ComparatorChallenges/GammaPassage.lean) |
