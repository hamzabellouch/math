# Independent largest prime factors of consecutive integers

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [The joint Dickman law for consecutive integers](../../preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf)

## Scope

Let $P^+(n)$ be the largest prime factor of $n$. The formalization proves the joint Dickman law in ordinary natural density: for every $0<a,b<1$, the density of integers satisfying $P^+(n)\le n^a$ and $P^+(n+1)\le n^b$ tends to $\rho(1/a)\rho(1/b)$, where $\rho$ is the Dickman function.

It also proves that each of the orderings $P^+(n)<P^+(n+1)$ and $P^+(n+1)<P^+(n)$ has natural density $1/2$.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Joint Dickman law and equal ordering densities for consecutive integers | [JointDickman.lean](../ComparatorChallenges/JointDickman.lean) |
