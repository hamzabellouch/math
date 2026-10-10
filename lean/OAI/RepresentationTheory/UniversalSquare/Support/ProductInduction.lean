import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.OneExtra

namespace OAI

/-! Product Induction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def externalTensor {a b : ℕ} {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ (Equiv.Perm (Fin a)) X)
    (σ : Representation ℂ (Equiv.Perm (Fin b)) Y) :
    Representation ℂ (Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) (X ⊗[ℂ] Y) where
  toFun g := TensorProduct.map (ρ g.1) (σ g.2)
  map_one' := by ext x y; simp
  map_mul' g h := by ext x y; simp

def sumPermHom {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    (Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) →* Equiv.Perm (Fin n) where
  toFun g := sumPerm e g.1 g.2
  map_one' := sumPerm_one e
  map_mul' g h := sumPerm_mul e g.1 h.1 g.2 h.2

def externalWordMap {n a b d : ℕ} {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin a)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin b)) Y}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (F : Representation.IntertwiningMap ρ (wordRep a d))
    (G : Representation.IntertwiningMap σ (wordRep b d)) :
    Representation.IntertwiningMap (externalTensor ρ σ)
      ((wordRep n d).comp (sumPermHom e)) where
  toLinearMap := (positionTensor e).toLinearMap.comp
    (TensorProduct.map F.toLinearMap G.toLinearMap)
  isIntertwining' g := by
    ext x y w
    apply congrFun (a := w)
    change positionTensor e (F (ρ g.1 x) ⊗ₜ[ℂ] G (σ g.2 y)) =
      wordRep n d (sumPerm e g.1 g.2) (positionTensor e (F x ⊗ₜ[ℂ] G y))
    rw [F.isIntertwining, G.isIntertwining, positionTensor_tmul,
      positionTensor_tmul, positionProduct_equivariant]

lemma externalWordMap_tmul {n a b d : ℕ} {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin a)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin b)) Y}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (F : Representation.IntertwiningMap ρ (wordRep a d))
    (G : Representation.IntertwiningMap σ (wordRep b d)) (x : X) (y : Y) :
    externalWordMap e F G (x ⊗ₜ[ℂ] y) = positionProduct e (F x) (G y) :=
  positionTensor_tmul e (F x) (G y)

lemma externalWordMap_injective {n a b d : ℕ} {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin a)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin b)) Y}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (F : Representation.IntertwiningMap ρ (wordRep a d))
    (G : Representation.IntertwiningMap σ (wordRep b d))
    (hF : Function.Injective F) (hG : Function.Injective G) :
    Function.Injective (externalWordMap e F G) :=
  (positionTensor e).injective.comp
    (TensorProduct.map_injective_of_flat_flat _ _ hF hG)

theorem external_cyclic_support {n a b d : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (σ : Representation ℂ (Equiv.Perm (Fin a)) Y)
    (τ : Representation ℂ (Equiv.Perm (Fin b)) Z)
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hv : v ∈ alphabetSub a d A)
    (hu : u ∈ alphabetSub b d (fun z => ¬ A z))
    (F : Representation.IntertwiningMap σ (cyclic (wordRep a d) v).toRepresentation)
    (G : Representation.IntertwiningMap τ (cyclic (wordRep b d) u).toRepresentation)
    (hF : Function.Injective F) (hG : Function.Injective G)
    (f : Representation.IntertwiningMap (ρ.comp (sumPermHom e)) (externalTensor σ τ))
    (hf : f ≠ 0) :
    ∃ H : Representation.IntertwiningMap ρ
      (cyclic (wordRep n d) (positionProduct e v u)).toRepresentation, H ≠ 0 := by
  let F' := (subrepInclusion (cyclic (wordRep a d) v)).comp F
  let G' := (subrepInclusion (cyclic (wordRep b d) u)).comp G
  let T := externalWordMap e F' G'
  let L := T.comp f
  have hT : Function.Injective T := externalWordMap_injective e F' G'
    (Subtype.val_injective.comp hF) (Subtype.val_injective.comp hG)
  have hL : L ≠ 0 := intertwining_comp_ne_zero T hT f hf
  have hm (z : Y ⊗[ℂ] Z) : T z ∈ cyclic (wordRep n d) (positionProduct e v u) := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul x y =>
      rw [show T (x ⊗ₜ[ℂ] y) = positionProduct e (F' x) (G' y) from
        externalWordMap_tmul e F' G' x y]
      exact product_mem_cyclic e v u (F' x) (G' y) (F x).property (G y).property
  have hs (z : Y ⊗[ℂ] Z) : T z ∈
      coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A) := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul x y =>
      rw [show T (x ⊗ₜ[ℂ] y) = positionProduct e (F' x) (G' y) from
        externalWordMap_tmul e F' G' x y]
      exact positionProduct_sector e A (F' x) (G' y)
        (cyclic_alphabet A v hv _ (F x).property)
        (cyclic_alphabet (fun z => ¬ A z) u hu _ (G y).property)
  apply sector_support_transfer ρ (fun i => (e i).isLeft = true) A
    (positionProduct e v u) L.toLinearMap
  · intro hz
    exact hL (Representation.IntertwiningMap.ext hz)
  · intro g hg x
    let g' : sectorGroup (fun i => (e i).isLeft = true) := ⟨g,hg⟩
    have heq : sumPerm e (leftRestriction e g') (rightRestriction e g') = g :=
      sumPerm_restrictions e g'
    rw [← heq]
    exact LinearMap.congr_fun (L.isIntertwining'
      (leftRestriction e g', rightRestriction e g')) x
  · intro x
    exact hm (f x)
  · intro x w hw
    by_contra hn
    exact hw (hs (f x) w hn)

end Saxl
end
end

end OAI
