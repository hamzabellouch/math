# Support coverage

The manuscript contains the full argument for Theorem 1.1 and Corollary 1.2, including the integral coefficient conventions, the completed-theory application, the geometric comparison, Witt transfer, and ordinary finite-amplitude descent. The mathematical references in the paper supply the explicitly cited external inputs. The files below support only the stated portions of that argument.

## Exact-arithmetic Chevalley--Eilenberg calculation

`support/r-ce/ce_certificate.py` constructs the trivial-coefficient Chevalley--Eilenberg matrices \(d_0,\ldots,d_3\) for \(\mathfrak{sl}_2\) and \(\mathfrak{sl}_3\) from matrix commutators. It uses exact integers and rational `Fraction` arithmetic. Its complete generated arrays and transcript are `support/r-ce/ce_certificate.json` and `support/r-ce/ce_certificate.txt`.

The checked identities are the characteristic-zero arithmetic used in Appendix A.1: the matrix shapes, rational ranks \((0,3,0,0)\) and \((0,8,20,35)\), the displayed nonzero minors, the adjacent products \(d_1d_0=0\), \(d_2d_1=0\), and \(d_3d_2=0\), closure of the trace cocycle, and its value \(2\) on the specified \(\mathfrak{sl}_2\) triple. The program does not calculate an augmented-image rank for the trace. Appendix A.1 proves non-boundary separately by restricting to the rank-two block.

This support does not check characteristic-\(p\) ranks, the building proof in Appendix A.2, the continuous group/Lie comparison, the geometric and Witt arguments, ordinary descent, or the main theorem. It supplies no computation for another paper in this family. `BUILDING.md` gives the guarded replay command and the required Python assertion setting.

The active guarded trio is in `support/r-ce/`. The separate directory `support/historical/r-ce/` preserves the earlier CE script, data, and transcript byte for byte, with the bounded arithmetic scope stated above.

Exact artifact and source-locator identities are listed in [SUPPORT-COVERAGE.json](SUPPORT-COVERAGE.json).

No Lean source or Lean verification is supplied for this article. The arithmetic support is not an independent review of the final manuscript.
