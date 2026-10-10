# Finite certificate verification

Requires Python 3 and only its standard library. Run with assertions enabled; do not add `-O` or `-OO`.

From the article directory:

```sh
python3 -I verification/check_certificate.py
```

Success is a zero exit with no output. A failed assertion or arithmetic error exits nonzero. The checker embeds its finite inputs and writes no result files.

`CERTIFICATE.json` identifies the checker and documented command; it is static metadata, not an execution receipt. The checker verifies the finite blocks, parameter-polytope bounds, envelope comparisons, and Bernstein tables, not the article's analytic propagation and energy-transfer arguments.
