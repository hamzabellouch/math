# [Cycle–clique Ramsey numbers](Cycle-clique-Ramsey-numbers-September-25-2026.pdf)

**Author:** OpenAI  
**Date:** September 25, 2026

## Citation

```bibtex
@misc{OAI:Cycle-clique-Ramsey-numbers-September-25-2026,
  author = {{OpenAI}},
  title = {{Cycle--clique Ramsey numbers}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf}{OAI:Cycle-clique-Ramsey-numbers-September-25-2026}},
  year = {2026}
}
```

## Verification

The checker programs use only the Python 3 standard library. Use an ordinary Python 3 interpreter without optimization flags. From this directory, run both complete checkers and compare their output with the supplied data:

```sh
python3 verification/code/verify.py --output /tmp/cycle-clique-check
```

The wrapper retains the generated output and execution information in the specified directory. The supplied deduction traces are in `verification/data/certificates.jsonl`; they are not separate proof objects for an additional independent minimal validator.
