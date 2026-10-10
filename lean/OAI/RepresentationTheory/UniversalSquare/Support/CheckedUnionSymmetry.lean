import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.SymmetricRegions
import OAI.RepresentationTheory.UniversalSquare.Support.UnionRowChecker

namespace OAI

/-! Checked Union Symmetry. -/

section

namespace UniversalTensorSquare

lemma checkedUnion_symmetric {n M r H W : ℕ} {qs : List (List ℕ)} {t : RowTree}
    {regions allRegions : List PrefixRegion}
    (check : ∀ h ≤ H, checkRegionPrefixes (quickResidual M r qs t) h n W regions [] = true)
    (height : ∀ R ∈ regions, firstBound n R.1 ≤ H)
    (width : ∀ R ∈ regions, firstBound n R.2 ≤ W)
    (cover : ∀ R ∈ allRegions, R ∈ regions ∨ (R.2,R.1) ∈ regions) :
    ∀ R ∈ allRegions, ∀ μ : YoungDiagram, μ.card = n →
      RowBounds μ.transpose R.1 → RowBounds μ R.2 → TreeResidual M r qs t μ.rowLens := by
  intro R hR μ hμ hA hB
  rcases cover R hR with h | h
  · exact checkedRegion_diagram check μ hμ h hA hB (height R h) (width R h)
  · apply treeResidual_transpose
    apply checkedRegion_diagram check μ.transpose ((Saxl.transpose_card μ).trans hμ) h
    · simpa only [YoungDiagram.transpose_transpose] using hB
    · exact hA
    · exact height _ h
    · exact width _ h

end UniversalTensorSquare
end

end OAI
