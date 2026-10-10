import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.ThreeRowLocal

namespace OAI

/-! Three Row Projected. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.ThreeRow
open FlagColumns Columns Balance

lemma columns_height (m s : ℕ) : (columnShape (columns m s)).colLen 0 ≤ 3 := by
  apply columnShape_height
  intro x hx
  simp only [columns,List.mem_append,List.mem_singleton,twos,ones,List.mem_replicate] at hx
  rcases hx with (⟨_,rfl⟩ | ⟨_,rfl⟩) | rfl <;> omega

theorem projected_support (m s : ℕ)
    (a b : Tableau (columns m s).sum (columnShape (columns m s)))
    {ν η μ : YoungDiagram}
    (tν : Tableau (twos m).sum ν) (tη : Tableau (twos m ++ ones s).sum η)
    (tμ : Tableau (columns m s).sum μ)
    (hev : ∀ i, Even (ν.rowLen i)) (hν : ν.colLen 0 ≤ 3) (hμ : μ.colLen 0 ≤ 3)
    (hs : HorizontalStrip ν η) (ht : HorizontalStrip η μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep tμ)
      (projectedSpechtTensor a b (inOutputs (Set.Icc 1 3))
        (inOutputs_invariant (Set.Icc 1 3))).toRepresentation, Function.Injective F := by
  classical
  let rs := columns m s
  obtain ⟨e,hr,hc⟩ := columnShape_placement rs
  let t := (enumerate rs).trans e
  let f := Fin.castLE (columns_height m s)
  have hblocks : letterLift f (polytabloid t) = blocks rs (standard 3) :=
    (standard_placed e hr hc (columns_height m s)).symm
  let P := inOutputs (n := rs.sum) (d := (columnShape rs).colLen 0)
    (e := (columnShape rs).colLen 0) (Set.Icc 1 3)
  let hP := inOutputs_invariant (n := rs.sum) (d := (columnShape rs).colLen 0)
    (e := (columnShape rs).colLen 0) (Set.Icc 1 3)
  let Q := inOutputs (n := rs.sum) (d := 3) (e := 3) (Set.Icc 1 3)
  have hPQ (w : Fin rs.sum → Fin ((columnShape rs).colLen 0 * (columnShape rs).colLen 0)) :
      Q (pairLetterMap f f ∘ w) ↔ P w := by
    change (∀ i, output (pairLetterMap f f (w i)) ∈ Set.Icc 1 3) ↔ _
    simp only [output_pairLetterMap f (fun _ => rfl)]
    rfl
  let W := projectedSpechtTensor a b P hP
  have hma : polytabloid t ∈ spechtSub a := by
    rw [← spechtSub_tableau_independent t a]
    exact mem_cyclic _ _
  have hmb : polytabloid t ∈ spechtSub b := by
    rw [← spechtSub_tableau_independent t b]
    exact mem_cyclic _ _
  let z : W.toSubmodule := projectedTensorQuotient a b P hP
    (⟨polytabloid t,hma⟩ ⊗ₜ[ℂ] ⟨polytabloid t,hmb⟩)
  let D : Representation.IntertwiningMap W.toRepresentation (wordRep rs.sum 6) :=
    (restrictLetters pairLetters).comp
      ((letterLift (pairLetterMap f f)).comp (subrepInclusion W))
  have hz : D z = -generator (pairPositions m) (shortSplit m s) (tripleSplit m s) := by
    change restrictLetters pairLetters (letterLift (pairLetterMap f f)
      (coordinateProjection P (spechtTensorMap a b
        (⟨polytabloid t,hma⟩ ⊗ₜ[ℂ] ⟨polytabloid t,hmb⟩)))) = _
    rw [spechtTensorMap]
    change restrictLetters pairLetters (letterLift (pairLetterMap f f)
      (coordinateProjection P (wordTensor rs.sum _ _ (polytabloid t ⊗ₜ[ℂ] polytabloid t)))) = _
    rw [← coordinateProjection_letterLift _ P Q hPQ,
      letterLift_wordTensor,hblocks]
    change restrictLetters pairLetters (invariantCoordinateProjection Q
      (inOutputs_invariant _) (wordTensor rs.sum 3 3 (blocks rs (standard 3) ⊗ₜ[ℂ]
        blocks rs (standard 3)))) = _
    rw [restrict_projected]
    exact sixSquare_columns m s
  have hsupp := generator_support (pairPositions m) (shortSplit m s) (tripleSplit m s)
    tν tη tμ hev hν hμ hs ht
  have hcy : cyclic (wordRep rs.sum 6) (D z) =
      cyclic (wordRep rs.sum 6) (generator (pairPositions m) (shortSplit m s) (tripleSplit m s)) := by
    rw [hz, ← neg_one_smul ℂ,cyclic_smul_eq _ _ _ (by norm_num)]
  rw [←hcy] at hsupp
  obtain ⟨F,hF⟩ := hsupp
  obtain ⟨G,hG⟩ := cyclic_projection_support D z F hF
  let H := (subrepInclusion (cyclic W.toRepresentation z)).comp G
  have hH : H ≠ 0 := by
    intro hz
    apply hG
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun J => J x) hz
  let := specht_irreducible tμ
  exact ⟨H,(Representation.IsIrreducible.injective_or_eq_zero H).resolve_right hH⟩

end Saxl.ThreeRow
end
end

end OAI
