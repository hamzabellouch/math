# Short Egyptian fractions

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Short Egyptian fractions](../../preprints/Short-Egyptian-fractions-September-25-2026/Short-Egyptian-fractions-September-25-2026.pdf)

## Scope

An Egyptian-fraction expansion writes a rational number as a sum of distinct unit fractions. The formalization proves that every $a/b$ with $1\le a<b$ has such an expansion and that the largest minimum length at denominator $b$ is $\Theta(\log\log b)$. If $F(k)$ counts exact $k$-term expansions of $1$, it also proves $\log\log F(k)=\Theta(k)$ and bounds every denominator in such an expansion.

Every integer $m\ge2$ occurs as a denominator in an expansion of $1$, with length eventually at most $(257/\log2+\varepsilon)\log\log m$ for every $\varepsilon>0$; padding can preserve that denominator. If $v(k)$ is the least integer at least $2$ absent from all exact $k$-term expansions of $1$, then eventually $e^{e^{k/600}}\le v(k)\le1+k^{2^{k-1}}$, and $\liminf_{k\to\infty}\log\log v(k)/k\ge\log2/257$.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Short expansions, counting, and prescribed denominators | [EgyptianFractions.lean](../ComparatorChallenges/EgyptianFractions.lean) |
| Optimal order of the shortest Egyptian-fraction expansions | [ShortEgyptianFractions.lean](../ComparatorChallenges/ShortEgyptianFractions.lean) |
