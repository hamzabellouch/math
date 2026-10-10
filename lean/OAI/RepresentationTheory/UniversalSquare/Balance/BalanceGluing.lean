import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceColumns
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceInduction
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceProduct

namespace OAI

/-! Balance Gluing. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

structure Piece {n d : ℕ} {G Y : Type*} [Group G] [AddCommGroup Y] [Module ℂ Y]
    (v : WordSpace n d) (c : Fin n → ℕ)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ) (σ : ℕ → ℤ)
    (φ : G →* fiberGroup c) (τ : Representation ℂ G Y) where
  surj : Function.Surjective φ
  raw : Y →ₗ[ℂ] WordSpace n (d*d)
  raw_mem : ∀ y, raw y ∈ (cyclicSquareMap v).range
  raw_sums : ∀ y, FixedComponentSums c (fun a => (output a : ℤ)) σ (raw y)
  projected : Representation.IntertwiningMap τ
    ((wordRep n (d*d)).comp ((fiberGroup c).subtype.comp φ))
  injective : Function.Injective projected
  projection_eq : ∀ y, coordinateProjection (componentWords c A label) (raw y) = projected y

def Piece.join {n a b d : ℕ} {G H X Y : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {v : WordSpace a d} {u : WordSpace b d}
    {c : Fin a → ℕ} {c' : Fin b → ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {σ σ' : ℕ → ℤ}
    {φ : G →* fiberGroup c} {ψ : H →* fiberGroup c'}
    {ρ : Representation ℂ G X} {τ : Representation ℂ H Y}
    (P : Piece v c A label σ φ ρ) (Q : Piece u c' A label σ' ψ τ)
    (e : Fin n ≃ Fin a ⊕ Fin b) (hd : ∀ i j, c i ≠ c' j) :
    letI : AddCommGroup (X ⊗[ℂ] Y) := Module.addCommMonoidToAddCommGroup ℂ
    Piece (positionProduct e v u) (joinedLabels e c c') A label (σ+σ')
      ((joinedFiberHom e c c').comp (φ.prodMap ψ)) (outer ρ τ) := by
  letI : AddCommGroup (X ⊗[ℂ] Y) := Module.addCommMonoidToAddCommGroup ℂ
  let L := (positionTensor e).toLinearMap.comp (TensorProduct.map P.raw Q.raw)
  let T := outerWordMap e ((fiberGroup c).subtype.comp φ)
    ((fiberGroup c').subtype.comp ψ) P.projected Q.projected
  refine {
    surj := (joinedFiberHom_surjective e c c' hd).comp (P.surj.prodMap Q.surj)
    raw := L
    raw_mem := ?_
    raw_sums := ?_
    projected := T
    injective := outerWordMap_injective e _ _ P.projected Q.projected P.injective Q.injective
    projection_eq := ?_ }
  · intro z
    change L z ∈ (cyclicSquareMap (positionProduct e v u)).range.toSubmodule
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul x y =>
      change positionTensor e (P.raw x ⊗ₜ[ℂ] Q.raw y) ∈ _
      rw [positionTensor_tmul]
      exact product_mem_square e v u _ _ (P.raw_mem x) (Q.raw_mem y)
  · intro z
    change L z ∈ fixedSumSpace (joinedLabels e c c') (fun a => (output a : ℤ)) (σ+σ')
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul x y =>
      change positionTensor e (P.raw x ⊗ₜ[ℂ] Q.raw y) ∈ _
      rw [positionTensor_tmul]
      exact product_fixed_sums e c c' _ σ σ' _ _ (P.raw_sums x) (Q.raw_sums y)
  · intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      change coordinateProjection _ (L (x+y)) = T.toLinearMap (x+y)
      rw [map_add,map_add,hx,hy,map_add]
      rfl
    | tmul x y =>
      change coordinateProjection (componentWords (joinedLabels e c c') A label)
        (positionTensor e (P.raw x ⊗ₜ[ℂ] Q.raw y)) =
        positionTensor e (P.projected x ⊗ₜ[ℂ] Q.projected y)
      rw [positionTensor_tmul,positionTensor_tmul,component_projection_product,
        P.projection_eq,Q.projection_eq]

theorem Piece.support {n d : ℕ} {G X Y : Type*}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {v : WordSpace n d} {c : Fin n → ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {σ : ℕ → ℤ}
    {φ : G →* fiberGroup c} {τ : Representation ℂ G Y}
    (P : Piece v c A label σ φ τ)
    (ho : ∀ a b, A a → A b → label a < label b → output a < output b)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (F : Representation.IntertwiningMap ρ (Representation.coind ((fiberGroup c).subtype.comp φ) τ))
    (hF : F ≠ 0) :
    ∃ T : Representation.IntertwiningMap ρ (cyclicSquareMap v).range.toRepresentation, T ≠ 0 := by
  exact balance_support_of_surjective ρ (cyclicSquareMap v).range c A label
    (fun a => (output a : ℤ)) σ (by intro a b ha hb hl; exact_mod_cast ho a b ha hb hl)
    φ P.surj τ P.raw P.raw_mem P.raw_sums P.projected P.injective P.projection_eq
    (coindEval ((fiberGroup c).subtype.comp φ) F)
    (coindEval_ne_zero ((fiberGroup c).subtype.comp φ) F hF)

lemma cyclicSquareMap_polytabloid {n : ℕ} {lam : YoungDiagram} (a : Tableau n lam) :
    cyclicSquareMap (polytabloid a) = spechtTensorMap a a := by
  unfold spechtTensorMap
  rfl

theorem Piece.kronecker_pos {n : ℕ} {G Y : Type*}
    [Group G] [Finite G] [AddCommGroup Y] [Module ℂ Y]
    {lam μ : YoungDiagram} (a : Tableau n lam) (t : Tableau n μ)
    {c : Fin n → ℕ} {A : Fin (lam.colLen 0 * lam.colLen 0) → Prop}
    {label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ} {σ : ℕ → ℤ}
    {φ : G →* fiberGroup c} {τ : Representation ℂ G Y}
    (P : Piece (polytabloid a) c A label σ φ τ)
    (ho : ∀ a b, A a → A b → label a < label b → output a < output b)
    (θ : YoungDiagram) (hc : μ.card = θ.card) (hd : Dominates μ θ)
    (w : Fin n → Fin (θ.colLen 0)) (e : Equiv.Perm (Fin (θ.colLen 0)))
    (hw : ∀ j, (Finset.univ.filter (fun i => w i = e j)).card = θ.rowLen j)
    (hpack : SupportLE (cyclic (wordRep n (θ.colLen 0)) (Pi.single w 1)).toRepresentation
      (Representation.coind ((fiberGroup c).subtype.comp φ) τ)) :
    0 < kronecker a a t := by
  exact kronecker_pos_of_packing a t c A label σ ho φ P.surj τ P.raw (by
    intro y
    obtain ⟨z,hz⟩ := P.raw_mem y
    exact ⟨z, by rw [←cyclicSquareMap_polytabloid]; exact hz⟩)
    P.raw_sums P.projected P.injective P.projection_eq θ hc hd w e hw hpack

end Saxl.Balance
end
end

end OAI
