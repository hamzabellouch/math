import Mathlib
import OAI.RingTheory.Multiplicity.TensorConductor

namespace OAI

noncomputable section
open scoped TensorProduct
open TensorProduct
namespace Lech.TensorPushout
variable (A P E N : Type*) [CommRing A] [CommRing P] [CommRing E]
  [Algebra A P] [Algebra A E] [AddCommGroup N]
  [Module A N] [Module E N] [IsScalarTower A E N]

local instance : Algebra E (P ⊗[A] E) := Algebra.TensorProduct.rightAlgebra

def aux : (P ⊗[A] E) ⊗[E] N ≃ₗ[A] P ⊗[A] N :=
  ((TensorProduct.congr (Algebra.TensorProduct.commRight A E P).symm.toLinearEquiv
    (LinearEquiv.refl E N)).restrictScalars A).trans
  (((AlgebraTensorModule.rightComm E A E E P N).restrictScalars A).trans
    ((TensorProduct.congr ((TensorProduct.lid E N).restrictScalars A)
      (LinearEquiv.refl A P)).trans (TensorProduct.comm A N P)))

lemma aux_tmul (p : P) (e : E) (n : N) :
    aux A P E N ((p ⊗ₜ[A] e) ⊗ₜ[E] n) = p ⊗ₜ[A] (e • n) := rfl

def equiv : (P ⊗[A] E) ⊗[E] N ≃ₗ[P] P ⊗[A] N where
  __ := (aux A P E N).toAddEquiv
  map_smul' p x := by
    change aux A P E N (p • x) = p • aux A P E N x
    induction x using TensorProduct.inductionOn with
    | tmul b n =>
      induction b using TensorProduct.inductionOn with
      | tmul a e =>
        change aux A P E N (p • ((a ⊗ₜ[A] e) ⊗ₜ[E] n)) = _
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', aux_tmul, aux_tmul,
          TensorProduct.smul_tmul']
      | add b c hb hc =>
        change aux A P E N (p • ((b+c) ⊗ₜ[E] n)) = _
        simpa only [TensorProduct.add_tmul, smul_add, map_add] using congrArg₂ (·+·) hb hc
    | add x y hx hy =>
      change aux A P E N (p • (x+y)) = _
      simpa only [smul_add, map_add] using congrArg₂ (·+·) hx hy

@[simp] lemma equiv_tmul (p : P) (e : E) (n : N) :
    equiv A P E N ((p ⊗ₜ[A] e) ⊗ₜ[E] n) = p ⊗ₜ[A] (e • n) := rfl
end Lech.TensorPushout

namespace Lech.TensorConductor
variable {D R M N X : Type*} [CommRing D] [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup X]
  [Module D M] [Module D N] [Module D X]
  [Module R M] [Module R N] [SMulCommClass D R M] [SMulCommClass D R N]
def congrLeft (e : M ≃ₗ[D] N) (he : ∀ (r : R) x, e (r • x) = r • e x) :
    M ⊗[D] X ≃ₗ[R] N ⊗[D] X where
  __ := (TensorProduct.congr e (LinearEquiv.refl D X)).toAddEquiv
  map_smul' r x := (mapLeft e.toLinearMap he).map_smul r x
@[simp] lemma congrLeft_tmul (e : M ≃ₗ[D] N) (he : ∀ (r : R) x, e (r • x) = r • e x)
    (m : M) (x : X) : congrLeft e he (m ⊗ₜ[D] x) = e m ⊗ₜ[D] x := rfl
end Lech.TensorConductor

end

end OAI
