import Mathlib
import OAI.RingTheory.Multiplicity.IdealQuotientFunctor

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (P : ModuleCat.{u} R) (M : ModuleCat.{u} R)

 

def tensorReductionEquiv :
    (P ⊗[R] (M ⧸ (I • (⊤ : Submodule R M)))) ≃ₗ[R]
      ((P ⊗[R] M) ⧸ (I • (⊤ : Submodule R (P ⊗[R] M)))) :=
  (TensorProduct.tensorQuotientEquiv P (I • (⊤ : Submodule R M))).trans
    (Submodule.quotEquivOfEq _ _ (by
      change (((I • (⊤ : Submodule R M)).subtype).lTensor P).range = _
      simpa only [pow_one] using range_lTensor I (I • (⊤ : Submodule R M)).subtype 1
        (by simp only [Submodule.range_subtype,pow_one]) P))

lemma tensorReductionEquiv_tmul (x : P) (y : M) :
    tensorReductionEquiv I P M (x ⊗ₜ[R] Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x ⊗ₜ[R] y) := rfl

 

def tensorReductionIso :
    quotientFunctor I ⋙ (curriedTensor (ModuleCat.{u} R)).obj P ≅
      (curriedTensor (ModuleCat.{u} R)).obj P ⋙ quotientFunctor I :=
  NatIso.ofComponents (fun M => (tensorReductionEquiv I P M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
        induction y using Submodule.Quotient.induction_on with
        | _ y => rfl)
end Lech.TensorIdeal

end

end OAI
