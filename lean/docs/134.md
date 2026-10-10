# Generalized star height at most three

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Finite Monoid Computations and a Uniform Generalized Star-Height Bound](../../preprints/Finite-Monoid-Computations-and-a-Uniform-Generalized-Star-Height-Bound-September-25-2026/Finite-Monoid-Computations-and-a-Uniform-Generalized-Star-Height-Bound-September-25-2026.pdf)
- [Generalized Star Height at Most Four](../../preprints/Generalized-Star-Height-at-Most-Four-September-25-2026/Generalized-Star-Height-at-Most-Four-September-25-2026.pdf)
- [Generalized Star Height at Most Three](../../preprints/Generalized-Star-Height-at-Most-Three-September-25-2026/article.pdf)

## Scope

Generalized star height measures the nesting of Kleene stars in regular expressions that also allow Boolean operations. The formalization proves that every regular language over a finite alphabet has a generalized expression over the same alphabet of star height at most three. This is stronger than the bound of thirteen in the accompanying finite-monoid paper. The selected statement asserts the uniform expression bound, without separately encoding every construction step of that paper.

The formalization proves that every regular language over a finite alphabet has a generalized regular expression over that same alphabet with star height at most three. Generalized expressions allow Boolean operations as well as concatenation and Kleene star. The bound of three implies the accompanying paper's bound of four; the selected statement concerns the expression bound itself.

Generalized star height measures the nesting of Kleene stars in regular expressions that also allow Boolean operations. The formalization proves that every regular language over a finite alphabet has a generalized regular expression over that same alphabet of star height at most three. Complements are taken in the same free monoid. This is the paper's uniform bound.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Uniform generalized star-height bound of three | [GeneralizedStarHeight.lean](../ComparatorChallenges/GeneralizedStarHeight.lean) |
| Generalized star height at most three | [GeneralizedStarHeight.lean](../ComparatorChallenges/GeneralizedStarHeight.lean) |
