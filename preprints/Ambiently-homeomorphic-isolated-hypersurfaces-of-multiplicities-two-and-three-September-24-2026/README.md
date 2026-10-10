# [Ambiently homeomorphic isolated hypersurfaces of multiplicities two and three](paper.pdf)

**Author:** OpenAI  
**Date:** September 24, 2026

## Citation

```bibtex
@misc{OAI:Ambiently-homeomorphic-isolated-hypersurfaces-of-multiplicities-two-and-three-September-24-2026,
  author = {{OpenAI}},
  title = {{Ambiently homeomorphic isolated hypersurfaces of multiplicities two and three}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Ambiently-homeomorphic-isolated-hypersurfaces-of-multiplicities-two-and-three-September-24-2026/paper.pdf}{OAI:Ambiently-homeomorphic-isolated-hypersurfaces-of-multiplicities-two-and-three-September-24-2026}},
  year = {2026}
}
```

## Run the verification code

Both checks use only the Python standard library. From this paper directory, run:

```sh
env -u PYTHONOPTIMIZE python3 verification/support/supplied_finite_rank.py
verification_tmp=$(mktemp -d)
python3 verification/validation/explicit_relation.py verification/support/explicit-relation.json "$verification_tmp/explicit-relation-verification.json"
```

Run the first command with assertions enabled, without Python's `-O` option; it exits silently when the cutoff counts and rank certificate pass. The second command verifies the explicit integer relation and the construction's variable counts, and writes a JSON report. These checks cover the finite arithmetic, not the lattice-theoretic or topological arguments.
