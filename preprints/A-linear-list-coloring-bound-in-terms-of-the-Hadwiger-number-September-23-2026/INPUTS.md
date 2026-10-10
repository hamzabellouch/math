# Mathematical input interfaces

The complete locally authored proof is in `main.tex` and `sections/01-introduction.tex` through `sections/08-recursion.tex`. The ordinary halving scaffold is integrated in Section 3; there is no dependency on an internal ordinary-coloring manuscript. Empty auxiliary graphs have `h = ell = chi = f = 0`.

Three nontrivial graph-theoretic statements are invoked without proof:

1. Reed–Seymour's fractional minor theorem: `f(P) <= 4 h(P)`, a weakened form of their statement (1.3), which gives factor 2. Used to initialize thinning and obtain private clique models. Finite simple graph hypotheses hold in both uses.
2. Ordinary-chromatic connectivity extraction: for integer `k >= 1`, `chi(P) >= 7k` gives a `k`-connected subgraph `J` with `chi(J) >= chi(P) - 6k`. The exact form is Delcourt–Postle arXiv:2108.01633v5, Theorem 5.1, credited there to Girão–Narayanan. Used on auxiliary clique blow-ups; no minor-exclusion hypothesis is imposed on those blow-ups.
3. Terminal grouping: there is an absolute integer `gamma` such that `gamma*m` connectivity realizes every partition of `m` distinct terminals into disjoint connected sets. This is Delcourt–Postle v5, Definition 5.7 and Theorem 5.8, second knitting parameter one, based on Bollobás–Thomason. All uses count distinct representatives or proxies and verify their connectivity budget.

Finite linear-programming duality is a standard additional input, cited to Gale–Kuhn–Tucker, for the fractional-coloring primal/dual equality. The paper verifies finite feasibility and boundedness; it does not claim to prove LP duality. This corrects an inherited input inventory that described a local convex-hull proof absent from the canonical source.

Stable-set sampling, the bounded-differences estimate, integral vertex path packing, list connectivity extraction, color reservation, coarse density and incidence bounds, the small-district construction, unpaired path minimization, path-history accounting, separability, and the complete three-district recursion are proved locally. Attribution to predecessors remains attached to those arguments.

The clean build is a document build, not a mathematical certificate. Author and component review records live in the coordination directory; fresh final whole-proof reviews must be bound to the final article sources and PDF.
