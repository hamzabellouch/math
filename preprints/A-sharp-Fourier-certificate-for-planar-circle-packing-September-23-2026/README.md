# [A sharp Fourier certificate for planar circle packing](paper.pdf)

OpenAI  
September 23, 2026

## Citation

```bibtex
@misc{OAI:A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026,
  author = {{OpenAI}},
  title = {{A sharp Fourier certificate for planar circle packing}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf}{OAI:A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026}},
  year = {2026}
}
```

## Verification

The numerical certificate requires Python 3 and `python-flint==0.9.0`.
The following runs it in a temporary copy so generated results stay separate
from the supplied sources:

```sh
paper_root=$(pwd -P)
paper_verify=$(mktemp -d)
cp -R "$paper_root/build" "$paper_root/verification" "$paper_verify/"
python3 -m venv "$paper_verify/venv"
"$paper_verify/venv/bin/python" -m pip install -r "$paper_verify/verification/requirements.txt"
"$paper_verify/venv/bin/python" -B "$paper_verify/verification/verify_all.py"
```

The optional exact-rational six-by-six check uses only the Python standard
library:

```sh
"$paper_verify/venv/bin/python" -B "$paper_verify/verification/check_sjj_rational.py"
```

Run without `-O` or `-OO`. See [verification/README.md](verification/README.md)
for the precise coverage, output interpretation, and limitations.
