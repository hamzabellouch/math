import Mathlib
import OAI.RingTheory.Multiplicity.FrobeniusOrderTransfer
import OAI.RingTheory.Multiplicity.TensorRingTwist

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
open CategoryTheory
namespace Lech.FrobeniusIntermediate
open Lech.RootTower Lech.PerfectDomainStages
universe u
variable (σ : Type) (k D : Type u) [Fintype σ] [Field k] [CommRing D] [IsDomain D]
    [Algebra (MvPowerSeries σ k) D]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
    (B : Subalgebra (MvPowerSeries σ k) D)
    (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)
local instance : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _
local instance : CharP B p := B.val.toRingHom.charP Subtype.val_injective p
local instance : SMulCommClass B (PerfectClosure (MvPowerSeries σ k) p) (PerfectClosure B p) where
  smul_comm b r c := by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _

 
theorem normalizedLength_intermediate_tensor (M : ModuleCat.{u} D) :
    normalizedLength σ k p ((PerfectClosure D p) ⊗[D] M) =
      ((p : ℝ≥0∞)^(e*Fintype.card σ))⁻¹ *
        normalizedLength σ k p ((PerfectClosure B p) ⊗[B]
          ((ModuleCat.extendScalars (powerMap p B.toSubring e he)).obj M)) := by
  let P := PerfectClosure (MvPowerSeries σ k) p
  let C := PerfectClosure D p
  let C' := PerfectClosure B p
  let E := perfectAlgEquiv p B.val Subtype.val_injective
    ⟨e,fun d => ⟨⟨d^(p^e),he d⟩,rfl⟩⟩
  let f := (PerfectClosure.of B p).comp (powerMap p B.toSubring e he)
  have hx : E.toRingHom.comp f =
      (iterateFrobeniusEquiv C p e : C →+* C).comp (PerfectClosure.of D p) := by
    ext x
    change E (PerfectClosure.of B p (powerMap p B.toSubring e he x)) =
      iterateFrobeniusEquiv C p e (PerfectClosure.of D p x)
    refine (perfectAlgEquiv_of p B.val Subtype.val_injective
      ⟨e, fun d => ⟨⟨d^(p^e), he d⟩, rfl⟩⟩ (powerMap p B.toSubring e he x)).trans ?_
    rw [iterateFrobeniusEquiv_def,← map_pow]
    rfl
  have hl₁ : normalizedLength σ k p
      ((PerfectClosure B p) ⊗[B] ((ModuleCat.extendScalars (powerMap p B.toSubring e he)).obj M)) =
      normalizedLength σ k p ((ModuleCat.restrictScalars (algebraMap P C')).obj
        ((ModuleCat.extendScalars f).obj M)) := by
    let q := (ModuleCat.extendScalarsComp (powerMap p B.toSubring e he)
      (PerfectClosure.of B p)).app M
    exact ((regularTower σ k p).length_eq_of_equiv
      ((ModuleCat.restrictScalars (algebraMap P C')).mapIso q).toLinearEquiv).symm
  have hl₂ := (regularTower σ k p).length_eq_of_equiv
    (Lech.TensorTwist.algebraExtendEquiv f E M)
  change normalizedLength σ k p _ = normalizedLength σ k p _ at hl₂
  rw [hx] at hl₂
  rw [hl₁,hl₂]
  exact normalizedLength_frobenius_extend σ k p (PerfectClosure.of D p) e M
end Lech.FrobeniusIntermediate

end

end OAI
