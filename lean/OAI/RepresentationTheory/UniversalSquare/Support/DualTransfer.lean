import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.OneExtra

namespace OAI

/-! Dual Transfer. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def intertwiningDual {G X Y : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X}
    {σ : Representation ℂ G Y} (f : Representation.IntertwiningMap ρ σ) :
    Representation.IntertwiningMap σ.dual ρ.dual where
  toLinearMap := f.toLinearMap.dualMap
  isIntertwining' g := by
    ext l x
    change l (σ g⁻¹ (f x)) = l (f (ρ g⁻¹ x))
    rw [f.isIntertwining]

def intertwiningFlip {G X Y : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X}
    {σ : Representation ℂ G Y} (f : Representation.IntertwiningMap ρ σ.dual) :
    Representation.IntertwiningMap σ ρ.dual where
  toLinearMap := f.toLinearMap.flip
  isIntertwining' g := by
    ext y x
    change f x (σ g y) = f (ρ g⁻¹ x) y
    have h := congrArg (fun l : Module.Dual ℂ Y => l y) (LinearMap.congr_fun (f.isIntertwining' (g⁻¹)) x)
    change f (ρ g⁻¹ x) y = f x (σ (g⁻¹)⁻¹ y) at h
    rw [inv_inv] at h
    exact h.symm

lemma intertwiningFlip_ne_zero {G X Y : Type*} [Group G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ.dual) (hf : f ≠ 0) :
    intertwiningFlip f ≠ 0 := by
  intro hz
  apply hf
  ext x y
  exact congrArg (fun F => F y x) hz

theorem specht_support_of_dual {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) Y)
    (f : Representation.IntertwiningMap (spechtRep t) σ.dual) (hf : f ≠ 0) :
    ∃ h : Representation.IntertwiningMap (spechtRep t) σ, Function.Injective h := by
  let F := (spechtSelfDual t).symm.toIntertwiningMap.comp (intertwiningFlip f)
  have hF : F ≠ 0 := intertwining_comp_ne_zero
    (spechtSelfDual t).symm.toIntertwiningMap (spechtSelfDual t).symm.injective
    (intertwiningFlip f) (intertwiningFlip_ne_zero f hf)
  let := specht_irreducible t
  have hs : Function.Surjective F :=
    (Representation.IsIrreducible.surjective_or_eq_zero F).resolve_right hF
  obtain ⟨h, hh⟩ := intertwining_lift_surjective F hs
    (Representation.IntertwiningMap.id (spechtRep t))
  refine ⟨h, ?_⟩
  intro x y he
  have hx := congrArg (fun H => H x) hh
  have hy := congrArg (fun H => H y) hh
  exact hx.symm.trans ((congrArg F he).trans hy)

def tensorDualEquiv {G X Y : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [Module.Finite ℂ X] [Module.Finite ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) :
    (ρ.dual.tprod σ.dual).Equiv (ρ.tprod σ).dual where
  toLinearEquiv := TensorProduct.dualDistribEquiv ℂ X Y
  isIntertwining' g := by
    ext l m x y
    rfl

def tensorSignCancel {n : ℕ} {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (σ : Representation ℂ (Equiv.Perm (Fin n)) Y) :
    ((signTwist ρ).tprod (signTwist σ)).Equiv (ρ.tprod σ) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    ext x y
    change (signC g • ρ g x) ⊗ₜ[ℂ] (signC g • σ g y) = ρ g x ⊗ₜ[ℂ] σ g y
    rw [TensorProduct.smul_tmul_smul, signC_mul_self, one_smul]

end Saxl
end
end

end OAI
