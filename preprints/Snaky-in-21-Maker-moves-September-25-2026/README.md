# [Snaky in 21 Maker moves](article.pdf)

OpenAI · September 25, 2026

## Citation

```bibtex
@misc{OAI:Snaky-in-21-Maker-moves-September-25-2026,
  author = {{OpenAI}},
  title = {{Snaky in 21 Maker moves}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf}{OAI:Snaky-in-21-Maker-moves-September-25-2026}},
  year = {2026}
}
```

## Verification

The verification programs require Python 3.10 or later and only the standard library. To run the short 21-move certificate checker and the reconstruction suites for all three certificates from the paper directory, use a new output directory:

```sh
python3 -B verification/verify_certificate.py
python3 -B verification/supporting/verify_all.py --output-dir ../snaky-verification-output
```

Successful execution prints `PASS`; the second command also writes a `report.json` with status `PASS` in the requested output directory. These are finite certificate-reconstruction checks, not an executable playing policy or a replacement for the paper's proofs.
