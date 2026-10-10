import Mathlib
import OAI.RingTheory.Multiplicity.ResidueExtension

namespace OAI

noncomputable section
open IsLocalRing
open scoped TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
lemma finite_module_isAdicComplete (I : Ideal R) [IsAdicComplete I R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by
  apply (AdicCompletion.of_bijective_iff (I:=I) (M:=M)).mp
  let e := (TensorProduct.lid R M).symm.trans
    (TensorProduct.congr (AdicCompletion.ofLinearEquiv I R) (LinearEquiv.refl R M))
  let e' := (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R
  have he : ∀ x : M, e' (e x)=AdicCompletion.of I M x := by
    intro x
    change AdicCompletion.ofTensorProduct I M
      ((AdicCompletion.of I R 1) ⊗ₜ[R] x)=_
    rw [AdicCompletion.ofTensorProduct_tmul]
    change (1 : AdicCompletion I R) • AdicCompletion.of I M x=_
    rw [one_smul]
  have hb := e'.bijective.comp e.bijective
  simpa only [Function.comp_def,he] using hb

lemma prime_quotient_complete [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (P : Ideal R) [P.IsPrime] [IsLocalRing (R ⧸ P)] :
    IsAdicComplete (maximalIdeal (R ⧸ P)) (R ⧸ P) := by
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have := finite_module_isAdicComplete (maximalIdeal R) (R ⧸ P)
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective]
  exact (IsAdicComplete.map_algebraMap_iff (maximalIdeal R) (R ⧸ P)).mpr inferInstance
end Lech

end

end OAI
