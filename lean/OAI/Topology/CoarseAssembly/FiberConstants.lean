import OAI.Topology.CoarseAssembly.BlockOperators
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

/-! # The normalized constant subspace of a finite fiber

The fiber embedding sends `h` to the constant vector `|Q|⁻¹ᐟ² h`.
It is an actual linear isometry, including for singleton boundary fibers.
-/

noncomputable section

namespace CoarseAssembly

variable (Q : Type*) [Fintype Q]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def fiberNormalization : ℝ := (Real.sqrt (Fintype.card Q))⁻¹

theorem fiberNormalization_nonneg : 0 ≤ fiberNormalization Q := by
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem fiberNormalization_sq [Nonempty Q] :
    (Fintype.card Q : ℝ) * fiberNormalization Q ^ 2 = 1 := by
  have hn : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  unfold fiberNormalization
  rw [inv_pow, Real.sq_sqrt hn.le]
  exact mul_inv_cancel₀ (ne_of_gt hn)

def fiberConstant (h : H) : lp (fun _ : Q => H) 2 :=
  ⟨fun _ => (fiberNormalization Q : ℂ) • h, Memℓp.all _⟩

@[simp] theorem fiberConstant_apply (h : H) (q : Q) :
    fiberConstant Q h q = (fiberNormalization Q : ℂ) • h := rfl

theorem fiberConstant_norm [Nonempty Q] (h : H) : ‖fiberConstant Q h‖ = ‖h‖ := by
  have hs := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (fiberConstant Q h)
  have hs' : ‖fiberConstant Q h‖ ^ 2 =
      (Fintype.card Q : ℝ) * (fiberNormalization Q * ‖h‖) ^ 2 := by
    simpa [Real.rpow_two, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fiberNormalization_nonneg Q), tsum_fintype] using hs
  have hn := fiberNormalization_sq Q
  have heq : ‖fiberConstant Q h‖ ^ 2 = ‖h‖ ^ 2 := by
    rw [mul_pow, ← mul_assoc, hn, one_mul] at hs'
    exact hs'
  nlinarith [norm_nonneg (fiberConstant Q h), norm_nonneg h]

def fiberConstantIsometry [Nonempty Q] : H →ₗᵢ[ℂ] lp (fun _ : Q => H) 2 where
  toFun := fiberConstant Q
  map_add' x y := by
    apply lp.ext
    funext q
    exact smul_add (fiberNormalization Q : ℂ) x y
  map_smul' a x := by
    apply lp.ext
    funext q
    exact smul_comm (fiberNormalization Q : ℂ) a x
  norm_map' := fiberConstant_norm Q

/-- Singleton boundary fibers have normalization one. -/
@[simp] theorem fiberNormalization_of_unique [Unique Q] : fiberNormalization Q = 1 := by
  simp [fiberNormalization]

end CoarseAssembly

end

end OAI
