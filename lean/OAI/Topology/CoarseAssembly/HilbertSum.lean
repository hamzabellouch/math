import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.BlockOperators
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-! # Flattening the Hilbert sum of the finite fibers

The transfer is naturally constructed as a block operator. Flattening its
Hilbert sum identifies it isometrically with the ordinary Roe module on
the sigma type of vertices. Both directions and the norm identity are
constructed from summability of squared norms.
-/

noncomputable section

namespace CoarseAssembly

variable {ι : Type*} {Q : ι → Type*} {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem l2_norm_sq {J : Type*} {E : J → Type*} [∀ j, NormedAddCommGroup (E j)]
    (x : lp E 2) : ‖x‖ ^ 2 = ∑' j, ‖x j‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x

theorem l2_summable_sq {J : Type*} {E : J → Type*} [∀ j, NormedAddCommGroup (E j)]
    (x : lp E 2) : Summable (fun j => ‖x j‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)

omit [NormedSpace ℂ H] in
theorem flattenVector_norm (x : lp (fun i => lp (fun _ : Q i => H) 2) 2) :
    ‖flattenVector x‖ = ‖x‖ := by
  have hsq : ‖flattenVector x‖ ^ 2 = ‖x‖ ^ 2 := by
    calc
      _ = ∑' q, ‖flattenVector x q‖ ^ 2 := l2_norm_sq _
      _ = ∑' i, ∑' q : Q i, ‖flattenVector x ⟨i, q⟩‖ ^ 2 :=
        Summable.tsum_sigma' (fun i => l2_summable_sq (x i))
          (l2_summable_sq (flattenVector x))
      _ = ∑' i, ‖x i‖ ^ 2 := tsum_congr (fun i => (l2_norm_sq (x i)).symm)
      _ = ‖x‖ ^ 2 := (l2_norm_sq x).symm
  nlinarith [norm_nonneg (flattenVector x), norm_nonneg x]

def flattenIsometry :
    lp (fun i => lp (fun _ : Q i => H) 2) 2 →ₗᵢ[ℂ] lp (fun _ : Sigma Q => H) 2 where
  toFun := flattenVector
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := flattenVector_norm

omit [NormedSpace ℂ H] in
@[simp] theorem flatten_unflatten (x : lp (fun _ : Sigma Q => H) 2) :
    flattenVector (unflattenVector x) = x := by
  apply lp.ext
  rfl

omit [NormedSpace ℂ H] in
@[simp] theorem unflatten_flatten (x : lp (fun i => lp (fun _ : Q i => H) 2) 2) :
    unflattenVector (flattenVector x) = x := by
  apply lp.ext
  funext i
  apply lp.ext
  rfl

end CoarseAssembly

end

end OAI
