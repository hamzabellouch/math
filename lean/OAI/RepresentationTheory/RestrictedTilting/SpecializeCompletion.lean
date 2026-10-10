import Mathlib

namespace OAI

namespace FiberFunctorProof
section
open scoped TensorProduct
section CompletionScalar
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
lemma completion_map_scalar (a : R) (v : AdicCompletion I M) :
    AdicCompletion.map I (a • (LinearMap.id : M →ₗ[R] M)) v =
      algebraMap R (AdicCompletion I R) a • v := by
  ext n
  simp only [AdicCompletion.map_val_apply]
  change a • v.val n = _
  rw [algebraMap_smul]
  rfl
end CompletionScalar

 

variable {H L M F : Type*} [CommRing H] [Field L] [Algebra H L]
  [AddCommGroup M] [Module H M] [AddCommGroup F] [Module H F]
variable (W : M →ₗ[H] F) (Z : F →ₗ[H] M) (a : H)
  (hWZ : ∀ v, W (Z v) = a • v) (hZW : ∀ v, Z (W v) = a • v)

include hWZ in
lemma baseChange_scalar_inverse_left (v : L ⊗[H] F) :
    W.baseChange L (Z.baseChange L v) = algebraMap H L a • v := by
  induction v using TensorProduct.inductionOn with
  | add v w hv hw => simp only [map_add, smul_add, hv, hw]
  | tmul l v =>
    simp only [LinearMap.baseChange_tmul, hWZ, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', algebraMap_smul]

include hZW in
lemma baseChange_scalar_inverse_right (v : L ⊗[H] M) :
    Z.baseChange L (W.baseChange L v) = algebraMap H L a • v :=
  baseChange_scalar_inverse_left Z W a hZW v

noncomputable def specializedScalarEquiv (ha : algebraMap H L a ≠ 0) :
    (L ⊗[H] M) ≃ₗ[L] (L ⊗[H] F) :=
  LinearEquiv.ofLinearMap (W.baseChange L) ((algebraMap H L a)⁻¹ • Z.baseChange L)
    (by
      apply LinearMap.ext
      intro v
      change W.baseChange L ((algebraMap H L a)⁻¹ • Z.baseChange L v) = v
      rw [map_smul, baseChange_scalar_inverse_left W Z a hWZ, inv_smul_smul₀ ha])
    (by
      apply LinearMap.ext
      intro v
      change (algebraMap H L a)⁻¹ • Z.baseChange L (W.baseChange L v) = v
      rw [baseChange_scalar_inverse_right W Z a hZW, inv_smul_smul₀ ha])

@[simp] lemma specializedScalarEquiv_tmul (ha : algebraMap H L a ≠ 0) (l : L) (m : M) :
    specializedScalarEquiv W Z a hWZ hZW ha (l ⊗ₜ[H] m) = l ⊗ₜ[H] W m :=
  LinearMap.baseChange_tmul ..
end

open scoped TensorProduct
variable {k H L T M : Type*} [CommRing k] [CommRing H] [Field L]
  [Algebra k H] [Algebra H L] [Algebra k L] [IsScalarTower k H L]
  [AddCommGroup T] [Module k T] [AddCommGroup M] [Module H M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : (H ⊗[k] T) ≃ₗ[H] M) (W : M →ₗ[H] (ι → H)) (Z : (ι → H) →ₗ[H] M)
    (a : H) (hWZ : ∀ v, W (Z v) = a • v) (hZW : ∀ v, Z (W v) = a • v)
    (ha : algebraMap H L a ≠ 0)

noncomputable def fieldCoordinateTrivialization : (L ⊗[k] T) ≃ₗ[L] (ι → L) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange k H L L T).symm ≪≫ₗ
    (LinearEquiv.baseChange H L _ _ F) ≪≫ₗ
    specializedScalarEquiv W Z a hWZ hZW ha ≪≫ₗ
    TensorProduct.piRight H L L (fun _ : ι => H) ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ => TensorProduct.AlgebraTensorModule.rid H L L)

lemma fieldCoordinateTrivialization_one (t : T) (i : ι) :
    fieldCoordinateTrivialization F W Z a hWZ hZW ha (1 ⊗ₜ[k] t) i =
      algebraMap H L (W (F (1 ⊗ₜ[k] t)) i) := by
  simp only [fieldCoordinateTrivialization, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.baseChange_tmul, specializedScalarEquiv_tmul,
    TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, LinearEquiv.piCongrRight_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  simp only [Algebra.smul_def, mul_one]
end FiberFunctorProof

end OAI
