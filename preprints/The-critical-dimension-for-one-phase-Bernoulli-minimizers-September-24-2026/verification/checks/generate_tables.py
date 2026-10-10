#!/usr/bin/env python3
"""Render the complete coefficient appendix from the pinned source, without transcription.

Default: compare the existing appendix with the deterministic rendering.
Use --write to regenerate it after an intentional formatting change here.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from pathlib import Path
import re
import sys

SOURCE_SHA256 = "3b1e67b40af1740a1faab1ee8bbe85aa7c90dcb289fb5df2c8880de6956a8ffc"
EXTRACT_SHA256 = {
    "I": "1624eef4a8bfdb7152f17928b66d258e80974d7aa8ce99c2b72bb1fada01f07a",
    "II": "81fa8219837a8eaa43bc01ef193fc03746172cac63d7c10a231071ff2212605c",
}
CHECKS = Path(__file__).resolve().parent

INTRO = r"""\section{Complete coefficient tables}\label{app:tables}

The following two tables specify the polynomials used in
Section~\ref{cert:table-I} and the comparison forms in
Section~\ref{cert:gram}. Every coefficient printed below is an integer
numerator with denominator
\[
Q=250000.
\]
Leading zeroes in monomial codes are significant. All rows and all block
headers are included.

\subsection{Decoding and block conventions}\label{app:decoding}
For nonnegative rank, read a monomial code in consecutive triples.
Its first triple $h\,b\,j$ contributes
$g^h(\tr A^3)^b w^{[j=1]}z^{[j=2]}$.
Each subsequent triple $u\,v\,k$ is an unoriented edge carrying $A^k$,
with $A^0=\Id$. Endpoints $0,\ldots,r-1$ denote the free slots in order,
$5$ denotes a copy of $p$, and $6$ a copy of $\ell$;
three occurrences of $7$ are contracted with one $X$,
and three occurrences of $8$ with a second copy.
Multiply all factors and contract all nonfree slots.
There are no additional multiplicity factors; see
Section~\ref{cert:decode}.

In Table~I the first field specifies the polynomial, the second its monomial,
and the third its coefficient numerator. The free-slot orders are
$U_{jk}$, $K_{lijk}$, $M_l$, and $P_l$, while $f$ has rank zero.
The numbers of rows for $(f,U,M,P,K)$ are $(34,57,74,32,34)$,
for a total of $231$.

Each line of Table~II beginning with \texttt{@} starts a separate block
and gives its rank, projection label, and multiplier mode.
For each coefficient column, sum the monomials with the coefficients
in that column divided by $Q$ to obtain a tensor $J_c$.
For nonnegative rank the block contributes
$\rho\sum_c\langle J_c,\Pi J_c\rangle$ to $\Gamma$,
where the modes \texttt{I} and \texttt{B} mean
$\rho=1$ and $\rho=\chi=1-|p|^2-g^2$, respectively.
The labels \texttt{none}, \texttt{anti}, \texttt{sym}, and \texttt{hook}
specify exactly the operators of Section~\ref{cert:projections};
they do not instruct any further normalization of the coefficients.
Identical headers in different positions still define distinct blocks.

For rank $-1$, the four code digits instead give the four individual
exponents of $x_1,x_2,x_3,x_4$. The block contributes to $\Lambda$
the average over all $24$ permutations of
$\rho\sum_c J_c^2$.
Here \texttt{I} means $\rho=1$, while \texttt{H} means
$\rho=\sum_i x_i=-\lambda$.
The averaging and boundary normalization
$R=\sum_i x_i^2+(\sum_i x_i)^2=1$ are those of
Section~\ref{cert:gram}.
Table~II contains $21$ blocks: $19$ interior blocks with $529$ rows and
two boundary blocks with $14$ rows each, hence $557$ coefficient rows
in total. Each block retains its own number of coefficient columns.

\subsection{Table I: the multiplier coefficients}\label{app:table-I}
The columns below read from top to bottom, first on the left and then
on the right.
\begin{multicols}{2}
\begin{Verbatim}[fontsize=\footnotesize]
"""

BETWEEN = r"""\end{Verbatim}
\end{multicols}

\subsection{Table II: the comparison coefficients}\label{app:table-II}
\noindent The block headers are part of the data.
\begingroup\clubpenalty=10000\widowpenalty=10000
\begin{Verbatim}[fontsize=\footnotesize]
"""

OUTRO = r"""\end{Verbatim}
\endgroup

\subsection{Reproduction of the finite arithmetic}\label{app:reproduction}
In the complete source directory accompanying this article, run
\texttt{make -C build check}; dependencies and the preserved calculation records are in
\texttt{verification/checks/README.md}.  The entry point enables assertions, fixes
$a=29/50$, and checks source pins, literal table transcription, and fresh
exact outputs from two interior expansions and the
boundary, projection, and graph calculations.  The interior implementations
agree on every key, signed coefficient, magnitude assignment, rounded bound,
and aggregate. The retained provenance records describe the second
implementation as separately authored from the mathematical specification
and frozen before comparison with the first engine's output. That
specification already contained the claimed aggregate totals. These checks
verify finite arithmetic; correspondence
between formulas and code, and the analytic argument, require mathematical
review.
"""

def extract_tables(original: Path) -> tuple[bytes, bytes]:
    source = (original / "certificate-inputs.txt").read_bytes()
    if hashlib.sha256(source).hexdigest() != SOURCE_SHA256:
        raise ValueError("the source SHA-256 does not match the pinned input")
    blocks = re.findall(rb"(?ms)^~~~\n(.*?)^~~~(?:\n|$)", source)
    if len(blocks) != 3:
        raise ValueError("expected exactly two coefficient tables and one Python block")
    for name, block in zip(("I", "II"), blocks[:2]):
        if hashlib.sha256(block).hexdigest() != EXTRACT_SHA256[name]:
            raise ValueError(f"source Table {name} has an unexpected digest")
        if block != (original / "checks" / f"exact-table-{name}.txt").read_bytes():
            raise ValueError(f"source Table {name} differs from the preserved extraction")
    table_i, table_ii = blocks[:2]
    rows = table_i.decode("ascii").splitlines()
    if Counter(row.split()[0] for row in rows) != {
        "f": 34, "U": 57, "M": 74, "P": 32, "K": 34
    }:
        raise ValueError("Table I row counts differ")
    rows = table_ii.decode("ascii").splitlines()
    if sum(row.startswith("@") for row in rows) != 21 or len(rows) != 578:
        raise ValueError("Table II row or block counts differ")
    return table_i, table_ii

def render(original: Path) -> bytes:
    table_i, table_ii = extract_tables(original)
    blocks = table_ii.decode("ascii").split("\n@")
    separated = ("\n\\end{Verbatim}\n\\begin{Verbatim}[fontsize=\\footnotesize]\n@").join(blocks).encode("ascii")
    return INTRO.encode("ascii") + table_i + BETWEEN.encode("ascii") + separated + OUTRO.encode("ascii")

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write the generated appendix")
    args = parser.parse_args()
    target = CHECKS.parent.parent / "build" / "appendices" / "tables.tex"
    expected = render(CHECKS / "original")
    if args.write:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(expected)
        print(f"Wrote {target}")
    elif target.read_bytes() != expected:
        raise ValueError("appendix differs from deterministic rendering; check changes before --write")
    else:
        print("PASS complete appendix: 231 Table I rows, 557 Table II rows, 21 block headers")
    return 0

if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        sys.exit(1)
