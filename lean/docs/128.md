# A factor-two approximation for shortest common superstring

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [A Polynomial-Time 2-Approximation for Shortest Common Superstring](../../preprints/A-Polynomial-Time-2-Approximation-for-Shortest-Common-Superstring-September-24-2026/paper.pdf)

## Scope

The shortest common superstring problem asks for the shortest string containing each input string as a contiguous substring. The formalized result gives one deterministic polynomial-time algorithm whose output is a common superstring of length at most twice the unrestricted optimum. It applies to every finite list of explicitly encoded strings, with running time measured in input bits and the approximation ratio measured in symbol length.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Polynomial-time 2-approximation for shortest common superstring | [Superstring.lean](../ComparatorChallenges/Superstring.lean) |
