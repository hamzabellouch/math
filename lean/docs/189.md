# Cycle–clique Ramsey numbers

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Cycle–clique Ramsey numbers](../../preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf)

## Scope

The cycle–clique Ramsey conjecture predicts the exact number of vertices forcing either a cycle $C_m$ or a clique $K_n$ in complementary colors. The formalization proves $R(C_m,K_n)=(m-1)(n-1)+1$ for all integers $m\ge n\ge3$ except $(m,n)=(3,3)$, where it proves $R(C_3,K_3)=6$. This is the complete parameter range of the paper's main theorem.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Exact cycle–clique Ramsey numbers | [CycleCliqueRamsey.lean](../ComparatorChallenges/CycleCliqueRamsey.lean) |
