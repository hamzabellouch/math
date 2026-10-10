import Mathlib
import OAI.RingTheory.Multiplicity.FrobeniusFiniteLength

namespace OAI

noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace Lech
universe u
variable {D C : Type u} [CommRing D] [CommRing C]

def quotientExtensionEquiv (f : D →+* C) (I : Ideal D) :
    (ModuleCat.extendScalars f).obj (ModuleCat.of D (D ⧸ I)) ≃ₗ[C] C ⧸ I.map f := by
  letI : Algebra D C := f.toAlgebra
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).symm.toLinearEquiv

lemma finiteLength_primary_quotient [IsNoetherianRing D] [IsLocalRing D]
    (I : Ideal D) (hI : I.radical = IsLocalRing.maximalIdeal D) : IsFiniteLength D (D ⧸ I) := by
  apply Module.length_ne_top_iff.mp
  have h := Lech.Primary.length_ne_top I hI 1
  rw [pow_one] at h
  exact h
end Lech

end

end OAI
