# Endpoint Sobolev regularity of centered disk averages

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [An Endpoint Gradient Bound for the Centered Disk Maximal Operator](../../preprints/An-Endpoint-Gradient-Bound-for-the-Centered-Disk-Maximal-Operator-September-26-2026/article.pdf)

## Scope

The centered disk maximal operator takes the supremum of averages of $|f|$ over disks centered at each point. The formalization proves that every real $f\in W^{1,1}(\mathbb R^2)$ has a maximal function that is finite almost everywhere, belongs to $W^{1,1}_{\mathrm{loc}}$, and has a globally integrable weak gradient satisfying $\|\nabla Mf\|_1\le C\|\nabla f\|_1$ for one absolute constant $C$.

The earlier signed finite-band estimate for smooth compactly supported functions is also retained. The general endpoint statement covers the Sobolev setting of the paper; a BV extension is outside these statements.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Signed finite-band disk-maximal gradient bound | [SignedFiniteBand.lean](../ComparatorChallenges/SignedFiniteBand.lean) |
| Endpoint gradient bound for the centered disk maximal operator | [DiskMaximal.lean](../ComparatorChallenges/DiskMaximal.lean) |
