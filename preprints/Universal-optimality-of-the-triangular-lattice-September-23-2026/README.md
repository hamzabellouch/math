# [Universal optimality of the triangular lattice](paper.pdf)

OpenAI  
September 23, 2026

## Citation

```bibtex
@misc{OAI:Universal-optimality-of-the-triangular-lattice-September-23-2026,
  author = {{OpenAI}},
  title = {{Universal optimality of the triangular lattice}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Universal-optimality-of-the-triangular-lattice-September-23-2026/paper.pdf}{OAI:Universal-optimality-of-the-triangular-lattice-September-23-2026}},
  year = {2026}
}
```

## Verification

The two finite checkers require Python 3 and `python-flint==0.9.0`:

```sh
paper_verify=$(mktemp -d)
python3 -m venv "$paper_verify/venv"
"$paper_verify/venv/bin/python" -m pip install -r verification/requirements.txt
"$paper_verify/venv/bin/python" -B verification/numeric_balls.py --output-dir "$paper_verify/results"
"$paper_verify/venv/bin/python" -B verification/arithmetic_bounds.py --output-dir "$paper_verify/results"
```

Run without `-O` or `-OO`. The manifest binds the finalized manuscript inputs
in `build/` and the checker sources. A zero exit status and complete success
JSON are required for each run. See [verification/README.md](verification/README.md)
for the exact scope, source-version caveats, and output interpretation.
