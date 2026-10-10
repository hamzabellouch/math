# Erdős’s reciprocal-sum conjecture and quasipolynomial Szemerédi bounds

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Quasipolynomial Bounds for Arithmetic Progressions](../../preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf)

## Scope

Erdős's reciprocal-sum conjecture asks whether every set of positive integers with divergent reciprocal sum contains arithmetic progressions of every finite length. The formalization proves this statement: for every requested length, such a set contains a progression with positive common difference.

The selected theorem is the reciprocal-sum consequence. The paper's quantitative upper bound for the largest progression-free subset of $\{1,\ldots,N\}$ is outside this statement.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Erdős's reciprocal-sum arithmetic-progression conjecture | [ErdosReciprocal.lean](../ComparatorChallenges/ErdosReciprocal.lean) |
