# [Triangular minimality for planar Coulomb renormalized energy](paper.pdf)

OpenAI  
September 23, 2026

## Citation

```bibtex
@misc{OAI:Triangular-minimality-for-planar-Coulomb-renormalized-energy-September-23-2026,
  author = {{OpenAI}},
  title = {{Triangular minimality for planar Coulomb renormalized energy}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Triangular-minimality-for-planar-Coulomb-renormalized-energy-September-23-2026/paper.pdf}{OAI:Triangular-minimality-for-planar-Coulomb-renormalized-energy-September-23-2026}},
  year = {2026}
}
```

## Verification

The finite interval certificate requires Python 3, g++ with C++17 and OpenMP,
and Boost.Multiprecision headers. Run it with a fresh output directory:

```sh
paper_verify=$(mktemp -d)
python3 -I -B verification/run-certificate.py --output-dir "$paper_verify"
```

The command compiles and runs the certificate, then records logs and a receipt
in the selected directory. See [verification/README.md](verification/README.md)
for the acceptance conditions, source-bound verification record, and the
limits of the finite computation.
