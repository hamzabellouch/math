import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalancePacking

namespace OAI

/-! Signed Induction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def externalTensorMap {a b : ℕ} {X X' Y Y' : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Y'] [Module ℂ Y']
    {ρ : Representation ℂ (Equiv.Perm (Fin a)) X}
    {ρ' : Representation ℂ (Equiv.Perm (Fin a)) X'}
    {σ : Representation ℂ (Equiv.Perm (Fin b)) Y}
    {σ' : Representation ℂ (Equiv.Perm (Fin b)) Y'}
    (F : Representation.IntertwiningMap ρ ρ') (G : Representation.IntertwiningMap σ σ') :
    Representation.IntertwiningMap (externalTensor ρ σ) (externalTensor ρ' σ') where
  toLinearMap := TensorProduct.map F.toLinearMap G.toLinearMap
  isIntertwining' g := by
    ext x y
    change F (ρ g.1 x) ⊗ₜ[ℂ] G (σ g.2 y) =
      ρ' g.1 (F x) ⊗ₜ[ℂ] σ' g.2 (G y)
    rw [F.isIntertwining, G.isIntertwining]

lemma externalTensorMap_injective {a b : ℕ} {X X' Y Y' : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Y'] [Module ℂ Y']
    {ρ : Representation ℂ (Equiv.Perm (Fin a)) X}
    {ρ' : Representation ℂ (Equiv.Perm (Fin a)) X'}
    {σ : Representation ℂ (Equiv.Perm (Fin b)) Y}
    {σ' : Representation ℂ (Equiv.Perm (Fin b)) Y'}
    (F : Representation.IntertwiningMap ρ ρ') (G : Representation.IntertwiningMap σ σ')
    (hF : Function.Injective F) (hG : Function.Injective G) :
    Function.Injective (externalTensorMap F G) :=
  TensorProduct.map_injective_of_flat_flat _ _ hF hG

def signRestrictionMap {n a b : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin a)) Y}
    {τ : Representation ℂ (Equiv.Perm (Fin b)) Z}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (f : Representation.IntertwiningMap (ρ.comp (sumPermHom e)) (externalTensor σ τ)) :
    Representation.IntertwiningMap ((signTwist ρ).comp (sumPermHom e))
      (externalTensor (signTwist σ) (signTwist τ)) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext x
    change f (signC (sumPerm e g.1 g.2) • ρ (sumPerm e g.1 g.2) x) =
      TensorProduct.map (signTwist σ g.1) (signTwist τ g.2) (f x)
    rw [map_smul]
    have hf := LinearMap.congr_fun (f.isIntertwining' (g.1,g.2)) x
    change f (ρ (sumPerm e g.1 g.2) x) =
      TensorProduct.map (σ g.1) (τ g.2) (f x) at hf
    rw [hf,signC_sumPerm]
    generalize f x = z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,smul_add,hx,hy]
    | tmul x y =>
      change (signC g.1 * signC g.2) • (σ g.1 x ⊗ₜ[ℂ] τ g.2 y) =
        (signC g.1 • σ g.1 x) ⊗ₜ[ℂ] (signC g.2 • τ g.2 y)
      rw [TensorProduct.smul_tmul_smul]

lemma signRestrictionMap_ne_zero {n a b : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin a)) Y}
    {τ : Representation ℂ (Equiv.Perm (Fin b)) Z}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (f : Representation.IntertwiningMap (ρ.comp (sumPermHom e)) (externalTensor σ τ))
    (hf : f ≠ 0) : signRestrictionMap e f ≠ 0 := by
  intro h
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun H => H x) h

def signDomainMap {n : ℕ} {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    (f : Representation.IntertwiningMap ρ (signTwist σ)) :
    Representation.IntertwiningMap (signTwist ρ) σ where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext x
    change f (signC g • ρ g x) = σ g (f x)
    rw [map_smul]
    have h := LinearMap.congr_fun (f.isIntertwining' g) x
    change f (ρ g x) = signC g • σ g (f x) at h
    rw [h,smul_smul,signC_mul_self,one_smul]

theorem signed_external_cyclic_support {n a b d : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (σ : Representation ℂ (Equiv.Perm (Fin a)) Y)
    (τ : Representation ℂ (Equiv.Perm (Fin b)) Z)
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hv : v ∈ alphabetSub a d A)
    (hu : u ∈ alphabetSub b d (fun z => ¬ A z))
    (F : Representation.IntertwiningMap σ (signTwist (cyclic (wordRep a d) v).toRepresentation))
    (G : Representation.IntertwiningMap τ (signTwist (cyclic (wordRep b d) u).toRepresentation))
    (hF : Function.Injective F) (hG : Function.Injective G)
    (f : Representation.IntertwiningMap (ρ.comp (sumPermHom e)) (externalTensor σ τ))
    (hf : f ≠ 0) :
    ∃ H : Representation.IntertwiningMap (signTwist ρ)
      (cyclic (wordRep n d) (positionProduct e v u)).toRepresentation, H ≠ 0 := by
  exact external_cyclic_support (signTwist ρ) (signTwist σ) (signTwist τ) e v u A hv hu
    (signDomainMap F) (signDomainMap G) hF hG (signRestrictionMap e f)
    (signRestrictionMap_ne_zero e f hf)

end Saxl
end
end

end OAI
