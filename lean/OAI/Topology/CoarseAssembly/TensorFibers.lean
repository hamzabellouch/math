import OAI.Topology.CoarseAssembly.FiberConstants
import Mathlib.Analysis.InnerProductSpace.TensorProduct

namespace OAI

/-! # Amplifying finite-fiber operators

The algebraic Hilbert tensor product of a finite scalar fiber with the
coefficient Hilbert space is isometrically the fiber's vector-valued ℓ²
space. This gives the norm-controlled amplification used in each transfer
block, using Mathlib's Hilbert tensor-product operator norm theorem.
-/

noncomputable section

namespace CoarseAssembly

open scoped TensorProduct

variable {Q R H : Type*} [Fintype Q] [Fintype R]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def fiberTensorBilinear : lp (fun _ : Q => ℂ) 2 →ₗ[ℂ]
    H →ₗ[ℂ] lp (fun _ : Q => H) 2 where
  toFun a :=
    { toFun := fun h => ⟨fun q => a q • h, Memℓp.all _⟩
      map_add' := by intro x y; apply lp.ext; funext q; exact smul_add _ _ _
      map_smul' := by intro c h; apply lp.ext; funext q; exact smul_comm _ _ _ }
  map_add' a b := by
    apply LinearMap.ext
    intro h
    apply lp.ext
    funext q
    exact add_smul (a q) (b q) h
  map_smul' c a := by
    apply LinearMap.ext
    intro h
    apply lp.ext
    funext q
    exact mul_smul c (a q) h

def fiberTensorMap : (lp (fun _ : Q => ℂ) 2 ⊗[ℂ] H) →ₗ[ℂ] lp (fun _ : Q => H) 2 :=
  TensorProduct.lift fiberTensorBilinear

@[simp] theorem fiberTensorMap_tmul_apply (a : lp (fun _ : Q => ℂ) 2) (h : H) (q : Q) :
    fiberTensorMap (a ⊗ₜ[ℂ] h) q = a q • h := rfl

theorem fiberTensorMap_inner (x y : lp (fun _ : Q => ℂ) 2 ⊗[ℂ] H) :
    inner ℂ (fiberTensorMap x) (fiberTensorMap y) = inner ℂ x y := by
  induction x using TensorProduct.inductionOn with
  | tmul a h =>
    induction y using TensorProduct.inductionOn with
    | tmul b k =>
      rw [TensorProduct.inner_tmul]
      change (∑' q : Q, inner ℂ (a q • h) (b q • k)) =
        (∑' q : Q, inner ℂ (a q) (b q)) * inner ℂ h k
      simp only [inner_smul_left, inner_smul_right, RCLike.inner_apply]
      calc
        _ = ∑' q : Q, (b q * (starRingEnd ℂ) (a q)) * inner ℂ h k :=
          tsum_congr (fun q => (mul_assoc _ _ _).symm)
        _ = _ := tsum_mul_right
    | add y z ihy ihz => simp only [map_add, inner_add_right, ihy, ihz]
  | add x z ihx ihz => simp only [map_add, inner_add_left, ihx, ihz]

def fiberTensorIsometry :
    (lp (fun _ : Q => ℂ) 2 ⊗[ℂ] H) →ₗᵢ[ℂ] lp (fun _ : Q => H) 2 where
  toLinearMap := fiberTensorMap
  norm_map' x := by
    have hs := norm_sq_eq_re_inner (𝕜 := ℂ) (fiberTensorMap x)
    rw [fiberTensorMap_inner] at hs
    have ht := norm_sq_eq_re_inner (𝕜 := ℂ) x
    nlinarith [norm_nonneg (fiberTensorMap x), norm_nonneg x]

variable [DecidableEq Q]

theorem fiberTensorMap_surjective : Function.Surjective (fiberTensorMap (Q := Q) (H := H)) := by
  intro x
  refine ⟨∑ q : Q, lp.single 2 q (1 : ℂ) ⊗ₜ[ℂ] x q, ?_⟩
  apply lp.ext
  funext r
  simp only [map_sum, lp.coeFn_sum, Finset.sum_apply, fiberTensorMap_tmul_apply]
  simp [lp.single_apply, Pi.single_apply]

def fiberTensorEquiv :
    (lp (fun _ : Q => ℂ) 2 ⊗[ℂ] H) ≃ₗᵢ[ℂ] lp (fun _ : Q => H) 2 :=
  LinearIsometryEquiv.ofSurjective fiberTensorIsometry fiberTensorMap_surjective

@[simp] theorem fiberTensorEquiv_apply (x : lp (fun _ : Q => ℂ) 2 ⊗[ℂ] H) :
    fiberTensorEquiv x = fiberTensorMap x := rfl

theorem fiberTensor_single (q : Q) (h : H) :
    fiberTensorEquiv (lp.single 2 q (1 : ℂ) ⊗ₜ[ℂ] h) = lp.single 2 q h := by
  apply lp.ext
  funext r
  simp [fiberTensorMap_tmul_apply, lp.single_apply, Pi.single_apply]

theorem fiberTensor_constant (h : H) :
    fiberTensorEquiv (fiberConstant Q (1 : ℂ) ⊗ₜ[ℂ] h) = fiberConstant Q h := by
  apply lp.ext
  funext q
  simp [fiberTensorMap_tmul_apply, fiberConstant_apply]

variable [DecidableEq R]

def amplifyFiber (O : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (T : H →L[ℂ] H) : lp (fun _ : Q => H) 2 →L[ℂ] lp (fun _ : R => H) 2 :=
  (fiberTensorEquiv (Q := R) (H := H)).toLinearIsometry.toContinuousLinearMap.comp
    ((TensorProduct.mapL O T).comp
      (fiberTensorEquiv (Q := Q) (H := H)).symm.toLinearIsometry.toContinuousLinearMap)

theorem amplifyFiber_norm_le (O : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (T : H →L[ℂ] H) : ‖amplifyFiber O T‖ ≤ ‖O‖ * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  change ‖fiberTensorEquiv (TensorProduct.mapL O T (fiberTensorEquiv.symm x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖TensorProduct.mapL O T‖ * ‖fiberTensorEquiv.symm x‖ :=
      (TensorProduct.mapL O T).le_opNorm _
    _ ≤ (‖O‖ * ‖T‖) * ‖x‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (TensorProduct.norm_mapL_le O T) (norm_nonneg _)

theorem amplifyFiber_tensor (O : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (T : H →L[ℂ] H) (a : lp (fun _ : Q => ℂ) 2) (h : H) :
    amplifyFiber O T (fiberTensorEquiv (a ⊗ₜ[ℂ] h)) =
      fiberTensorEquiv (O a ⊗ₜ[ℂ] T h) := by
  change fiberTensorEquiv (TensorProduct.mapL O T
    (fiberTensorEquiv.symm (fiberTensorEquiv (a ⊗ₜ[ℂ] h)))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, TensorProduct.mapL_tmul]

theorem amplifyFiber_single (O : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (T : H →L[ℂ] H) (q : Q) (r : R) (h : H) :
    amplifyFiber O T (lp.single 2 q h) r = O (lp.single 2 q 1) r • T h := by
  rw [← fiberTensor_single, amplifyFiber_tensor]
  rfl

theorem amplifyFiber_constant (O : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (T : H →L[ℂ] H)
    (hO : O (fiberConstant Q (1 : ℂ)) = fiberConstant R (1 : ℂ)) (h : H) :
    amplifyFiber O T (fiberConstant Q h) = fiberConstant R (T h) := by
  rw [← fiberTensor_constant, amplifyFiber_tensor, hO, fiberTensor_constant]

end CoarseAssembly

end

end OAI
