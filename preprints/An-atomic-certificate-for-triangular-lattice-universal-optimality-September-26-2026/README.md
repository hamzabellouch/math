# [An atomic certificate for triangular-lattice universal optimality](paper.pdf)

OpenAI  
September 26, 2026

## Citation

```bibtex
@misc{OAI:An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026,
  author = {{OpenAI}},
  title = {{An atomic certificate for triangular-lattice universal optimality}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf}{OAI:An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026}},
  year = {2026}
}
```

## Verification

The exact finite checker uses only the Python 3 standard library:

```sh
python3 -I -B verification/check_certificate.py
```

A successful run exits zero without output. Do not use `-O` or `-OO`.
See [verification/README.md](verification/README.md) for its finite scope and
for the distinction between static certificate metadata and an execution
record.
