# Ostmann’s inverse Goldbach conjecture

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [The additive indecomposability of the primes](../../preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf)

## Scope

The formalization proves Ostmann's inverse Goldbach conjecture. For any two sets $A,B$ of nonnegative integers, each containing at least two elements, the symmetric difference between their sumset $A+B$ and the set of primes is infinite. Thus no set differing from the primes by only finitely many elements can be decomposed as such a sumset. The linked statements include the full result and its two-infinite-summands case.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Ostmann's inverse Goldbach theorem and the infinite-summands case | [OstmannComplete.lean](../ComparatorChallenges/OstmannComplete.lean) |
| Additive indecomposability of the primes up to finite changes | [OstmannPrimes.lean](../ComparatorChallenges/OstmannPrimes.lean) |
