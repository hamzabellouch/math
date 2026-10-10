# The $`L\log L`$ Fourier-convergence conjecture

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Almost-everywhere Fourier convergence in L log L](../../preprints/Almost-everywhere-Fourier-convergence-in-L-log-L-September-23-2026/paper.pdf)

## Scope

The $L\log L$ Fourier-convergence conjecture asks whether ordinary symmetric Fourier partial sums converge almost everywhere at this integrability scale. The formalization proves this for every measurable complex-valued function on $\mathbb T=\mathbb R/(2\pi\mathbb Z)$ satisfying $\int_{\mathbb T}|f|\log(2+|f|)<\infty$. Outside one measurable null set,
$\sum_{k=-N}^{N}\widehat f(k)e^{ikx}\to f(x)$ along the full sequence $N\to\infty$.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Almost-everywhere convergence of full symmetric Fourier partial sums | [FourierLLogL.lean](../ComparatorChallenges/FourierLLogL.lean) |
