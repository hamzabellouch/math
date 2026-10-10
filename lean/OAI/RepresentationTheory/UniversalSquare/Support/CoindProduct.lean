import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.SupportTransport

namespace OAI

/-! Coind Product. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def functionTensor {G H X Y : Type*} [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y] :
    (G → X) ⊗[ℂ] (H → Y) ≃ₗ[ℂ] (G × H → X ⊗[ℂ] Y) :=
  (TensorProduct.piLeft ℂ (H → Y) (fun _ : G => X)).trans
    ((LinearEquiv.piCongrRight (fun _ : G =>
      TensorProduct.piRight ℂ ℂ X (fun _ : H => Y))).trans
      { toFun := fun f g => f g.1 g.2
        invFun := fun f g h => f (g,h)
        left_inv := by intro f; rfl
        right_inv := by intro f; rfl
        map_add' := by intros; rfl
        map_smul' := by intros; rfl })

@[simp] lemma functionTensor_tmul {G H X Y : Type*} [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (f : G → X) (g : H → Y) (h : G × H) :
    functionTensor (f ⊗ₜ[ℂ] g) h = f h.1 ⊗ₜ[ℂ] g h.2 := rfl

def coindOuter {G H K L X Y : Type*} [Group G] [Group H] [Group K] [Group L]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : K →* G) (ψ : L →* H)
    (ρ : Representation ℂ K X) (σ : Representation ℂ L Y) :
    Representation.IntertwiningMap
      (outer (Representation.coind φ ρ) (Representation.coind ψ σ))
      (Representation.coind (φ.prodMap ψ) (outer ρ σ)) where
  toLinearMap :=
    ((functionTensor).toLinearMap.comp
      (TensorProduct.map (Representation.coindV φ ρ).subtype
        (Representation.coindV ψ σ).subtype)).codRestrict _ (by
      intro z
      induction z using TensorProduct.inductionOn with
      | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
      | tmul a b =>
        intro k g
        change a.val (φ k.1 * g.1) ⊗ₜ[ℂ] b.val (ψ k.2 * g.2) =
          TensorProduct.map (ρ k.1) (σ k.2) (a.val g.1 ⊗ₜ[ℂ] b.val g.2)
        rw [a.property,b.property,TensorProduct.map_tmul])
  isIntertwining' g := by
    ext a b h
    rfl

@[simp] lemma coindOuter_tmul {G H K L X Y : Type*}
    [Group G] [Group H] [Group K] [Group L]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : K →* G) (ψ : L →* H)
    (ρ : Representation ℂ K X) (σ : Representation ℂ L Y)
    (a : Representation.coindV φ ρ) (b : Representation.coindV ψ σ) (g : G × H) :
    (coindOuter φ ψ ρ σ (a ⊗ₜ[ℂ] b)).val g = a.val g.1 ⊗ₜ[ℂ] b.val g.2 := rfl

lemma coindOuter_injective {G H K L X Y : Type*}
    [Group G] [Group H] [Group K] [Group L]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : K →* G) (ψ : L →* H)
    (ρ : Representation ℂ K X) (σ : Representation ℂ L Y) :
    Function.Injective (coindOuter φ ψ ρ σ) := by
  intro a b h
  exact (TensorProduct.map_injective_of_flat_flat _ _
    (Representation.coindV φ ρ).injective_subtype
    (Representation.coindV ψ σ).injective_subtype)
    (functionTensor.injective (congrArg Subtype.val h))

def coindTrans {G H K X : Type*} [Group G] [Group H] [Group K]
    [AddCommMonoid X] [Module ℂ X]
    (φ : K →* H) (ψ : H →* G) (ρ : Representation ℂ K X) :
    Representation.IntertwiningMap (Representation.coind ψ (Representation.coind φ ρ))
      (Representation.coind (ψ.comp φ) ρ) where
  toLinearMap := {
    toFun a := ⟨fun g => (a.val g).val 1, by
      intro k g
      change (a.val (ψ (φ k) * g)).val 1 = ρ k ((a.val g).val 1)
      rw [a.property]
      change (a.val g).val (1*φ k) = ρ k ((a.val g).val 1)
      simpa only [one_mul,mul_one] using (a.val g).property k 1⟩
    map_add' a b := by ext g; rfl
    map_smul' a b := by ext g; rfl }
  isIntertwining' g := by ext a h; rfl

lemma coindTrans_injective {G H K X : Type*} [Group G] [Group H] [Group K]
    [AddCommMonoid X] [Module ℂ X]
    (φ : K →* H) (ψ : H →* G) (ρ : Representation ℂ K X) :
    Function.Injective (coindTrans φ ψ ρ) := by
  intro a b hab
  apply Subtype.ext
  funext g
  apply Subtype.ext
  funext h
  have hh := congrArg (fun z : Representation.coindV (ψ.comp φ) ρ =>
    z.val (ψ h * g)) hab
  change (a.val (ψ h*g)).val 1 = (b.val (ψ h*g)).val 1 at hh
  rw [a.property,b.property] at hh
  change (a.val g).val (1*h) = (b.val g).val (1*h) at hh
  simpa only [one_mul] using hh

end Saxl
end
end

end OAI
