# Weak MTW curvature gives convexity and regular optimal transport

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Global Support and Convex Injectivity Domains under Weak MTW](../../preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf)
- [Uniform Bi-Hölder Transport from Weak MTW](../../preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf)

## Scope

On a compact connected smooth Riemannian manifold of dimension at least two, the formalized result proves that weak MTW curvature implies convexity of every open tangent injectivity domain. Prior convexity or nonfocality is not assumed. Additional formalized results give global support at ordinary subgradients, compact convex lifted gap sections with the stated diameter bound, and scale and local-injectivity estimates for finite target families. The latter finite-family result does not cover the paper's arbitrary-potential local-injectivity assertion.

The formalized result gives uniform bi-Hölder optimal transport for squared-distance cost on each fixed compact connected smooth Riemannian manifold of dimension at least two satisfying weak MTW. For probability densities between fixed positive lower and finite upper bounds, one exponent and constant work for every pair of densities. The optimal map is a homeomorphism, is unique almost everywhere, and both it and its inverse satisfy the global Hölder bound. The constants are uniform over the density class on the fixed manifold, not over varying metrics.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Convex injectivity domains under weak MTW | [WeakMTWGlobalSupport.lean](../ComparatorChallenges/WeakMTWGlobalSupport.lean) |
| Uniform bi-Hölder optimal transport | [BiholderTransport.lean](../ComparatorChallenges/BiholderTransport.lean) |
