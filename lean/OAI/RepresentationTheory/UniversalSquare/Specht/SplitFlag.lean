import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.FlagColumns

namespace OAI

/-! Split Flag. -/

section

noncomputable section
namespace Saxl.FlagColumns

lemma pure_single {n d : ℕ} (a : Fin n → Fin d) :
    pure (fun i => Pi.single (a i) 1) = Pi.single a 1 := by
  classical
  funext w
  by_cases h : w = a
  · subst w
    simp [pure]
  · rw [Pi.single_eq_of_ne h]
    unfold pure
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Pi.single_eq_of_ne hi 1)

lemma wedge_base {n d : ℕ} (a : Fin n → Fin d) :
    ∃ N : ℕ → Fin d → ℂ, wedge n N = altWord ⊤ a := by
  classical
  refine ⟨fun i => if hi : i < n then Pi.single (a ⟨i,hi⟩) 1 else 0, ?_⟩
  rw [altWord_inverse_sum]
  let := Fintype.ofFinite (⊤ : Subgroup (Equiv.Perm (Fin n)))
  let e : (⊤ : Subgroup (Equiv.Perm (Fin n))) ≃ Equiv.Perm (Fin n) :=
    { toFun := Subtype.val
      invFun := fun π => ⟨π, Subgroup.mem_top π⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  symm
  unfold wedge
  apply Fintype.sum_equiv e
  intro π
  change signC π.val • Pi.single (a ∘ π.val) 1 =
    signC π.val • pure (fun i => if hi : (π.val i).val < n then
      Pi.single (a ⟨(π.val i).val,hi⟩) 1 else 0)
  simp only [dite_eq_left (π.val _).isLt]
  congr 1
  exact (pure_single (a ∘ π.val)).symm

lemma coordinateProjection_pair {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (x y : WordSpace n d) :
    dotProduct (coordinateProjection P x) y = dotProduct x (coordinateProjection P y) := by
  classical
  apply Finset.sum_congr rfl
  intro w hw
  simp only [coordinateProjection_apply]
  split_ifs <;> simp

lemma coordinateProjection_idempotent {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (x : WordSpace n d) :
    coordinateProjection P (coordinateProjection P x) = coordinateProjection P x := by
  classical
  ext w
  simp only [coordinateProjection_apply]
  split_ifs <;> rfl

lemma coordinateProjection_star {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (x : WordSpace n d) :
    star (coordinateProjection P x) = coordinateProjection P (star x) := by
  classical
  funext w
  simp only [Pi.star_apply, coordinateProjection_apply]
  split_ifs <;> simp

theorem split_column_nonzero {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w : Fin n → Fin d) (hw : Function.Injective w) (Q : Fin d → Prop)
    (hQ : ∀ i, Q (w i) ↔ (e i).isLeft = true) :
    ∃ N : ℕ → Fin d → ℂ,
      dotProduct (wedge n N) (positionProduct e (altWord ⊤ (leftWord e w))
        (altWord ⊤ (rightWord e w))) ≠ 0 := by
  classical
  let P := fun v : Fin n → Fin d => ∀ i, Q (v i) ↔ (e i).isLeft = true
  let y := altWord (⊤ : Subgroup (Equiv.Perm (Fin n))) w
  let z := coordinateProjection P y
  have hf {m : ℕ} : fiberGroup (fun _ : Fin m => ()) = ⊤ := by
    apply Subgroup.ext
    intro g
    simp [fiberGroup]
  have hz : z = positionProduct e (altWord ⊤ (leftWord e w))
      (altWord ⊤ (rightWord e w)) := by
    change coordinateProjection P (altWord ⊤ w) = _
    rw [altWord_sector ⊤ w Q _ hQ, ← hf (m := n),
      altWord_fiber_split e (fun _ => ()) w]
    simp only [hf]
  have hz0 : z ≠ 0 := by
    intro hn
    have hh := congrFun hn w
    have he : z w = 1 := by
      change coordinateProjection P y w = 1
      rw [coordinateProjection_apply, ite_eq_left (show P w from hQ)]
      exact altWord_injective_base ⊤ w hw
    exact one_ne_zero (he.symm.trans hh)
  have hzr : star z = z := by
    change star (coordinateProjection P y) = _
    rw [coordinateProjection_star, altWord_real]
  obtain ⟨N,hN⟩ := wedge_base w
  refine ⟨N, ?_⟩
  rw [hN, ← hz]
  intro hn
  have hh : dotProduct z (star z) = 0 := by
    rw [hzr]
    change dotProduct (coordinateProjection P y) (coordinateProjection P y) = 0
    rw [coordinateProjection_pair, coordinateProjection_idempotent]
    exact hn
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  exact hz0 (dotProduct_self_star_eq_zero.mp hh)

end Saxl.FlagColumns
end
end

end OAI
