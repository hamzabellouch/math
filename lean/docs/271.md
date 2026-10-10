# Bloch's law, its lattice correction, and the spherical magnetization law

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Spontaneous magnetization in the quantum Heisenberg ferromagnet](../../preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf)

## Scope

The formalization proves spontaneous magnetization for the nearest-neighbor isotropic quantum Heisenberg ferromagnet on $\mathbb Z^d$ for every $d\ge3$ and every spin $S\in\{\tfrac12,1,\tfrac32,\ldots\}$. At every sufficiently low positive temperature, it constructs a translation-invariant equilibrium state satisfying the KMS condition for the zero-field dynamics and having magnetization at least $S/4$.

It also proves convergence of the finite-volume dynamics to the infinite-volume dynamics used in the KMS statement.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Low-temperature spontaneous magnetization for every positive spin | [Heisenberg.lean](../ComparatorChallenges/Heisenberg.lean) |
