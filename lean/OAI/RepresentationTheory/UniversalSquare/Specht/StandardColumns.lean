import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.SingletonPairs
import OAI.RepresentationTheory.UniversalSquare.Specht.FlagColumns
import OAI.RepresentationTheory.UniversalSquare.Specht.ZeroColumns

namespace OAI

/-! Standard Columns. -/

section

noncomputable section
namespace Saxl.FlagColumns
open Columns

def standard (d : ℕ) (i : ℕ) (a : Fin d) : ℂ := if i = a.val then 1 else 0

def appendPositions (rs ss : List ℕ) : Fin (rs ++ ss).sum ≃ Fin rs.sum ⊕ Fin ss.sum :=
  (finCongr (show (rs ++ ss).sum = rs.sum + ss.sum from List.sum_append)).trans finSumFinEquiv.symm

@[simp] lemma appendPositions_left_val (rs ss : List ℕ) (i : Fin rs.sum) :
    ((appendPositions rs ss).symm (Sum.inl i)).val = i.val := rfl

@[simp] lemma appendPositions_right_val (rs ss : List ℕ) (i : Fin ss.sum) :
    ((appendPositions rs ss).symm (Sum.inr i)).val = rs.sum+i.val := rfl

lemma blocks_append (rs ss : List ℕ) {d : ℕ} (N : ℕ → Fin d → ℂ) :
    blocks (rs ++ ss) N = positionProduct (appendPositions rs ss) (blocks rs N) (blocks ss N) := by
  induction rs with
  | nil =>
    rw [blocks_nil]
    funext w
    change blocks ss N w = 1 * blocks ss N (rightWord (appendPositions [] ss) w)
    rw [one_mul]
    congr 1
    funext i
    apply congrArg w
    apply Fin.ext
    change i.val = 0 + i.val
    omega
  | cons r rs ih =>
    change blocks (r :: (rs ++ ss)) N = _
    rw [blocks_cons,blocks_cons,ih]
    funext w
    have hll : leftWord finSumFinEquiv.symm w =
        leftWord finSumFinEquiv.symm (leftWord (appendPositions (r::rs) ss) w) := by
      funext i
      apply congrArg w
      apply Fin.ext
      rfl
    have hlr : leftWord (appendPositions rs ss) (rightWord finSumFinEquiv.symm w) =
        rightWord finSumFinEquiv.symm (leftWord (appendPositions (r::rs) ss) w) := by
      funext i
      apply congrArg w
      apply Fin.ext
      rfl
    have hrr : rightWord (appendPositions rs ss) (rightWord finSumFinEquiv.symm w) =
        rightWord (appendPositions (r::rs) ss) w := by
      funext i
      apply congrArg w
      apply Fin.ext
      change r + (rs.sum+i.val) = (r+rs.sum)+i.val
      omega
    change wedge r N _ * (blocks rs N _ * blocks ss N _) =
      (wedge r N _ * blocks rs N _) * blocks ss N _
    rw [hll,hlr,hrr,mul_assoc]
    rfl

lemma standard_placed {rs : List ℕ} {μ : YoungDiagram} {D : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (hD : μ.colLen 0 ≤ D) :
    blocks rs (standard D) = letterLift (Fin.castLE hD) (polytabloid ((enumerate rs).trans e)) := by
  rw [← mapped_placed e hr hc (standard D)]
  unfold letterLift
  congr 2
  funext i a
  unfold standard
  simp only [Fin.ext_iff, Fin.val_castLE]

lemma letterLift_id_apply {n d : ℕ} (x : WordSpace n d) :
    letterLift (id : Fin d → Fin d) x = x := by
  classical
  have hx : x = ∑ w, x w • Pi.single w (1 : ℂ) := by
    funext w
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [map_smul, letterLift_single, Function.id_comp]
  exact hx.symm

lemma standard_placed_self {rs : List ℕ} {μ : YoungDiagram}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c') :
    blocks rs (standard (μ.colLen 0)) = polytabloid ((enumerate rs).trans e) := by
  rw [standard_placed e hr hc le_rfl]
  exact letterLift_id_apply _

lemma standard_exists_tableau (rs : List ℕ) :
    ∃ t : Tableau rs.sum (columnShape rs),
      blocks rs (standard ((columnShape rs).colLen 0)) = polytabloid t := by
  obtain ⟨e,hr,hc⟩ := columnShape_placement rs
  exact ⟨(enumerate rs).trans e,standard_placed_self e hr hc⟩

lemma standard_lift (rs : List ℕ) {d D : ℕ} (hd : (columnShape rs).colLen 0 ≤ d)
    (hD : d ≤ D) :
    letterLift (Fin.castLE hD) (blocks rs (standard d)) = blocks rs (standard D) := by
  obtain ⟨e,hr,hc⟩ := columnShape_placement rs
  rw [standard_placed e hr hc hd,standard_placed e hr hc (hd.trans hD),letterLift_comp]
  rfl

end Saxl.FlagColumns
end
end

end OAI
