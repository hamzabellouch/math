# Squarefree quartics and power-free polynomial values

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Squarefree values of quartics and power-free values of polynomials](../../preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/manuscript.pdf)

## Scope

The formalized result proves positive-density power-free values for every integer polynomial $f$ irreducible over $\mathbb Q$ of degree $d\ge4$. Put $k=d-2$ and assume no prime $k$th power divides every value of $f$. Then the number of positive integers $n\le X$ for which $f(n)$ is $k$-free is $c_fX+o_f(X)$, where $c_f>0$ is the convergent product of local factors. Negative values are allowed and zero is excluded. No monicity, primitivity, or coefficient-height restriction is imposed.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Positive density of power-free polynomial values | [PowerFreeValues.lean](../ComparatorChallenges/PowerFreeValues.lean) |
