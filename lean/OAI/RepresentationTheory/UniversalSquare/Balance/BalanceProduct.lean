import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ProductInduction
import OAI.RepresentationTheory.UniversalSquare.Support.WordRelabel
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceProjection
import OAI.RepresentationTheory.UniversalSquare.Support.SupportTransport

namespace OAI

/-! Balance Product. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

def cyclicSquareMap {n d : ℕ} (v : WordSpace n d) :
    Representation.IntertwiningMap
      ((cyclic (wordRep n d) v).toRepresentation.tprod (cyclic (wordRep n d) v).toRepresentation)
      (wordRep n (d*d)) where
  toLinearMap := (wordTensor n d d).toLinearMap.comp
    (TensorProduct.map (cyclic (wordRep n d) v).toSubmodule.subtype
      (cyclic (wordRep n d) v).toSubmodule.subtype)
  isIntertwining' g := by
    ext x y w
    exact congrFun (wordTensor_equivariant g (x.val ⊗ₜ[ℂ] y.val)) w

@[simp] lemma cyclicSquareMap_tmul {n d : ℕ} (v : WordSpace n d)
    (x y : (cyclic (wordRep n d) v).toSubmodule) :
    cyclicSquareMap v (x ⊗ₜ[ℂ] y) = wordTensor n d d (x.val ⊗ₜ[ℂ] y.val) := rfl

theorem product_mem_square {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (u : WordSpace b d)
    (x : WordSpace a (d*d)) (y : WordSpace b (d*d))
    (hx : x ∈ (cyclicSquareMap v).range) (hy : y ∈ (cyclicSquareMap u).range) :
    positionProduct e x y ∈ (cyclicSquareMap (positionProduct e v u)).range := by
  obtain ⟨X,rfl⟩ := hx
  obtain ⟨Y,rfl⟩ := hy
  let W := (cyclicSquareMap (positionProduct e v u)).range.toSubmodule
  change positionProduct e (cyclicSquareMap v X) (cyclicSquareMap u Y) ∈ W
  rw [← positionTensor_tmul e (cyclicSquareMap v X) (cyclicSquareMap u Y)]
  induction X using TensorProduct.inductionOn with
  | add X X' h h' => simpa only [map_add,TensorProduct.add_tmul] using W.add_mem h h'
  | tmul x x' =>
    induction Y using TensorProduct.inductionOn with
    | add Y Y' h h' => simpa only [map_add,TensorProduct.tmul_add] using W.add_mem h h'
    | tmul y y' =>
      rw [cyclicSquareMap_tmul,cyclicSquareMap_tmul,positionTensor_tmul,
        ← wordTensor_positionProduct]
      refine ⟨(⟨positionProduct e x.val y.val,product_mem_cyclic e v u _ _ x.property y.property⟩ :
        (cyclic (wordRep n d) (positionProduct e v u)).toSubmodule) ⊗ₜ[ℂ]
        (⟨positionProduct e x'.val y'.val,product_mem_cyclic e v u _ _ x'.property y'.property⟩ :
        (cyclic (wordRep n d) (positionProduct e v u)).toSubmodule), rfl⟩

def joinedLabels {n a b : ℕ} {α : Type*} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → α) (c' : Fin b → α) : Fin n → α := fun i => Sum.elim c c' (e i)

@[simp] lemma joinedLabels_left {n a b : ℕ} {α : Type*} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → α) (c' : Fin b → α) (i : Fin a) :
    joinedLabels e c c' (e.symm (Sum.inl i)) = c i := by simp [joinedLabels]

@[simp] lemma joinedLabels_right {n a b : ℕ} {α : Type*} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → α) (c' : Fin b → α) (i : Fin b) :
    joinedLabels e c c' (e.symm (Sum.inr i)) = c' i := by simp [joinedLabels]

def joinedFiberHom {n a b : ℕ} {α : Type*} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → α) (c' : Fin b → α) :
    (fiberGroup c × fiberGroup c') →* fiberGroup (joinedLabels e c c') where
  toFun g := ⟨sumPerm e g.1.val g.2.val,by
    intro i
    obtain ⟨j,rfl⟩ := e.symm.surjective i
    cases j with
    | inl j => simpa only [sumPerm_left,joinedLabels_left] using g.1.property j
    | inr j => simpa only [sumPerm_right,joinedLabels_right] using g.2.property j⟩
  map_one' := Subtype.ext (sumPerm_one e)
  map_mul' g h := Subtype.ext (sumPerm_mul e g.1.val h.1.val g.2.val h.2.val)

lemma joinedFiberHom_surjective {n a b : ℕ} {α : Type*} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → α) (c' : Fin b → α) (hd : ∀ i j, c i ≠ c' j) :
    Function.Surjective (joinedFiberHom e c c') := by
  intro g
  have hg : g.val ∈ sectorGroup (fun i => (e i).isLeft = true) := by
    intro i
    have h := g.property i
    change Sum.elim c c' (e (g.val i)) = Sum.elim c c' (e i) at h
    cases he : e i with
    | inl j =>
      cases hf : e (g.val i) with
      | inl k => simp only [he,hf,Sum.isLeft_inl]
      | inr k => simp only [he,hf,Sum.elim_inl,Sum.elim_inr] at h; exact False.elim (hd j k h.symm)
    | inr j =>
      cases hf : e (g.val i) with
      | inl k => simp only [he,hf,Sum.elim_inl,Sum.elim_inr] at h; exact False.elim (hd k j h)
      | inr k => simp only [he,hf,Sum.isLeft_inr]
  let g' : sectorGroup (fun i => (e i).isLeft = true) := ⟨g.val,hg⟩
  have hl : leftRestriction e g' ∈ fiberGroup c := by
    intro i
    have hh := g.property (e.symm (Sum.inl i))
    rw [← leftRestriction_apply e g',joinedLabels_left,joinedLabels_left] at hh
    exact hh
  have hr : rightRestriction e g' ∈ fiberGroup c' := by
    intro i
    have hh := g.property (e.symm (Sum.inr i))
    rw [← rightRestriction_apply e g',joinedLabels_right,joinedLabels_right] at hh
    exact hh
  exact ⟨(⟨_,hl⟩,⟨_,hr⟩),Subtype.ext (sumPerm_restrictions e g')⟩

lemma componentWords_joined {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → ℕ) (c' : Fin b → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (w : Fin n → Fin d) :
    componentWords (joinedLabels e c c') A label w ↔
      componentWords c A label (leftWord e w) ∧ componentWords c' A label (rightWord e w) := by
  constructor
  · rintro ⟨hA,hl⟩
    exact ⟨⟨fun i => hA _,fun i => (hl _).trans (joinedLabels_left e c c' i)⟩,
      ⟨fun i => hA _,fun i => (hl _).trans (joinedLabels_right e c c' i)⟩⟩
  · rintro ⟨⟨hA,hl⟩,⟨hA',hl'⟩⟩
    constructor
    · intro i
      obtain ⟨j,rfl⟩ := e.symm.surjective i
      cases j with
      | inl j => exact hA j
      | inr j => exact hA' j
    · intro i
      obtain ⟨j,rfl⟩ := e.symm.surjective i
      cases j with
      | inl j => exact (hl j).trans (joinedLabels_left e c c' j).symm
      | inr j => exact (hl' j).trans (joinedLabels_right e c c' j).symm

lemma component_projection_product {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → ℕ) (c' : Fin b → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (x : WordSpace a d) (y : WordSpace b d) :
    coordinateProjection (componentWords (joinedLabels e c c') A label) (positionProduct e x y) =
      positionProduct e (coordinateProjection (componentWords c A label) x)
        (coordinateProjection (componentWords c' A label) y) := by
  classical
  ext w
  simp only [coordinateProjection_apply,componentWords_joined,positionProduct]
  split_ifs <;> simp_all

lemma joined_component_sum {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → ℕ) (c' : Fin b → ℕ) (z : Fin d → ℤ)
    (w : Fin n → Fin d) (k : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i => joinedLabels e c c' i = k), z (w i) =
      (∑ i ∈ Finset.univ.filter (fun i => c i = k), z (leftWord e w i)) +
      ∑ i ∈ Finset.univ.filter (fun i => c' i = k), z (rightWord e w i) := by
  classical
  simp only [Finset.sum_filter]
  rw [← Equiv.sum_comp e.symm, Fintype.sum_sum_type]
  simp only [joinedLabels_left,joinedLabels_right,leftWord,rightWord]

lemma product_fixed_sums {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → ℕ) (c' : Fin b → ℕ) (z : Fin d → ℤ)
    (σ σ' : ℕ → ℤ) (x : WordSpace a d) (y : WordSpace b d)
    (hx : FixedComponentSums c z σ x) (hy : FixedComponentSums c' z σ' y) :
    FixedComponentSums (joinedLabels e c c') z (σ+σ') (positionProduct e x y) := by
  intro w hw k
  obtain ⟨hxw,hyw⟩ := mul_ne_zero_iff.mp hw
  rw [joined_component_sum,hx _ hxw k,hy _ hyw k,Pi.add_apply]

def outerWordMap {n a b d : ℕ} {G H X Y : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (φ : G →* Equiv.Perm (Fin a)) (ψ : H →* Equiv.Perm (Fin b))
    (F : Representation.IntertwiningMap ρ ((wordRep a d).comp φ))
    (Q : Representation.IntertwiningMap σ ((wordRep b d).comp ψ)) :
    Representation.IntertwiningMap (outer ρ σ)
      ((wordRep n d).comp ((sumPermHom e).comp (φ.prodMap ψ))) where
  toLinearMap := (positionTensor e).toLinearMap.comp (TensorProduct.map F.toLinearMap Q.toLinearMap)
  isIntertwining' g := by
    ext x y w
    apply congrFun (a := w)
    change positionTensor e (F (ρ g.1 x) ⊗ₜ[ℂ] Q (σ g.2 y)) =
      wordRep n d (sumPerm e (φ g.1) (ψ g.2)) (positionTensor e (F x ⊗ₜ[ℂ] Q y))
    rw [F.isIntertwining,Q.isIntertwining,positionTensor_tmul,positionTensor_tmul]
    exact (positionProduct_equivariant e (φ g.1) (ψ g.2) (F x) (Q y)).symm

lemma outerWordMap_injective {n a b d : ℕ} {G H X Y : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (φ : G →* Equiv.Perm (Fin a)) (ψ : H →* Equiv.Perm (Fin b))
    (F : Representation.IntertwiningMap ρ ((wordRep a d).comp φ))
    (Q : Representation.IntertwiningMap σ ((wordRep b d).comp ψ))
    (hF : Function.Injective F) (hQ : Function.Injective Q) :
    Function.Injective (outerWordMap e φ ψ F Q) :=
  (positionTensor e).injective.comp (TensorProduct.map_injective_of_flat_flat _ _ hF hQ)

end Saxl.Balance
end
end

end OAI
