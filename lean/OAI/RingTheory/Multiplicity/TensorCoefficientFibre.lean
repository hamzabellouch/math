import Mathlib
import OAI.RingTheory.Multiplicity.TensorReduction

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open scoped TensorProduct
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  (I : Ideal R) (q : A →ₗ[A] M) (hq : Function.Surjective q)
  (hker : (q.restrictScalars R).ker = I • (⊤ : Submodule R A))
  (V : Type u) [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]

lemma map_ideal_smul_top {N P : Type u}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (e : N ≃ₗ[R] P) :
    Submodule.map e.toLinearMap (I • (⊤ : Submodule R N)) = I • (⊤ : Submodule R P) := by
  rw [Submodule.map_smul'',Submodule.map_top,LinearMap.range_eq_top.mpr e.surjective]

 

def quotientUnitTensorEquiv :
    (V ⧸ (I • (⊤ : Submodule R V))) ≃ₗ[R] (M ⊗[A] V) :=
  (Submodule.Quotient.equiv _ _ ((TensorProduct.lid A V).symm.restrictScalars R)
    (map_ideal_smul_top I _)).trans (quotientTensorEquiv I q hq hker V)

lemma quotientUnitTensorEquiv_mk (v : V) :
    quotientUnitTensorEquiv I q hq hker V (Submodule.Quotient.mk v) = q 1 ⊗ₜ[A] v := by
  change (((q.rTensor V).restrictScalars R).quotKerEquivOfSurjective
    (LinearMap.rTensor_surjective V hq))
      ((Submodule.quotEquivOfEq _ _ (kernel_rTensor I q hq hker V).symm)
        (Submodule.Quotient.mk (1 ⊗ₜ[A] v))) = _
  rw [Submodule.quotEquivOfEq_mk]
  rfl

end Lech.TensorIdeal

end

end OAI
