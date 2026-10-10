import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CoordinateLine
import OAI.RepresentationTheory.UniversalSquare.Support.DualTransfer

namespace OAI

/-! Projected Tensor. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def invariantCoordinateProjection {n d : ℕ}
    (P : (Fin n → Fin d) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n d) where
  toLinearMap := coordinateProjection P
  isIntertwining' g := by
    classical
    apply LinearMap.ext
    intro x
    funext w
    change (if P w then x (w ∘ g) else 0) = (if P (w ∘ g) then x (w ∘ g) else 0)
    rw [hP]

def projectedSpechtTensor {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β)
    (P : (Fin n → Fin (α.colLen 0 * β.colLen 0)) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w) :=
  ((invariantCoordinateProjection P hP).comp (spechtTensorMap a b)).range

def projectedTensorQuotient {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β)
    (P : (Fin n → Fin (α.colLen 0 * β.colLen 0)) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w) :
    Representation.IntertwiningMap ((spechtRep a).tprod (spechtRep b))
      (projectedSpechtTensor a b P hP).toRepresentation where
  toLinearMap := ((invariantCoordinateProjection P hP).comp
    (spechtTensorMap a b)).toLinearMap.rangeRestrict
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun
      (((invariantCoordinateProjection P hP).comp (spechtTensorMap a b)).isIntertwining' g) x

def projectedTensorEvaluation {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β)
    (P : (Fin n → Fin (α.colLen 0 * β.colLen 0)) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w)
    (w : Fin n → Fin (α.colLen 0 * β.colLen 0)) :
    Module.Dual ℂ (projectedSpechtTensor a b P hP).toSubmodule :=
  { toFun := fun x => x.val w
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

lemma projectedTensorEvaluation_pullback {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β)
    (P : (Fin n → Fin (α.colLen 0 * β.colLen 0)) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w)
    (v : Fin n → Fin (α.colLen 0)) (w : Fin n → Fin (β.colLen 0))
    (hp : P (mergeWords v w)) :
    intertwiningDual (X := Specht a ⊗[ℂ] Specht b) (projectedTensorQuotient a b P hP)
      (projectedTensorEvaluation a b P hP (mergeWords v w)) =
      tensorDualEquiv (spechtRep a) (spechtRep b)
        (coordinateRestriction a v ⊗ₜ[ℂ] coordinateRestriction b w) := by
  classical
  ext x y
  change coordinateProjection P (spechtTensorMap a b (x ⊗ₜ[ℂ] y)) (mergeWords v w) = y.val w * x.val v
  rw [coordinateProjection_apply, ite_eq_left hp]
  rw [spechtTensorMap]
  change wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val) (mergeWords v w) = _
  simp only [wordTensor_tmul, splitLeft_merge, splitRight_merge, mul_comm]

def dualSignMap {n : ℕ} {α : YoungDiagram} (a : Tableau n α)
    (φ : (spechtRep a).Equiv (signTwist (spechtRep (transposeTableau a)))) :
    Representation.IntertwiningMap (spechtRep a).dual
      (signTwist (spechtRep (transposeTableau a))) :=
  φ.toIntertwiningMap.comp (spechtSelfDual a).symm.toIntertwiningMap

def dualTensorSignMap {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β)
    (φ : (spechtRep a).Equiv (signTwist (spechtRep (transposeTableau a))))
    (ψ : (spechtRep b).Equiv (signTwist (spechtRep (transposeTableau b)))) :
    Representation.IntertwiningMap ((spechtRep a).tprod (spechtRep b)).dual
      (wordRep n (α.transpose.colLen 0 * β.transpose.colLen 0)) :=
  (spechtTensorMap (transposeTableau a) (transposeTableau b)).comp
    ((tensorSignCancel (spechtRep (transposeTableau a))
      (spechtRep (transposeTableau b))).toIntertwiningMap.comp
      (((dualSignMap a φ).tensor (dualSignMap b ψ)).comp
        (tensorDualEquiv (spechtRep a) (spechtRep b)).symm.toIntertwiningMap))

lemma dualTensorSignMap_coordinates {n : ℕ} {α β : YoungDiagram}
    (a s : Tableau n α) (b t : Tableau n β)
    (φ : (spechtRep a).Equiv (signTwist (spechtRep (transposeTableau a))))
    (ψ : (spechtRep b).Equiv (signTwist (spechtRep (transposeTableau b)))) :
    ∃ c : ℂ, c ≠ 0 ∧
      dualTensorSignMap a b φ ψ
        (tensorDualEquiv (spechtRep a) (spechtRep b)
          (coordinateRestriction a (rowWord s) ⊗ₜ[ℂ] coordinateRestriction b (rowWord t))) =
        c • wordTensor _ _ _
          (polytabloid (transposeTableau s) ⊗ₜ[ℂ] polytabloid (transposeTableau t)) := by
  obtain ⟨c,hc,hφ⟩ := signEquiv_coordinate_line a s φ
  obtain ⟨d,hd,hψ⟩ := signEquiv_coordinate_line b t ψ
  refine ⟨c*d, mul_ne_zero hc hd, ?_⟩
  change spechtTensorMap (transposeTableau a) (transposeTableau b)
    (TensorProduct.map (dualSignMap a φ).toLinearMap (dualSignMap b ψ).toLinearMap
      ((tensorDualEquiv (spechtRep a) (spechtRep b)).symm
        (tensorDualEquiv (spechtRep a) (spechtRep b)
          (coordinateRestriction a (rowWord s) ⊗ₜ[ℂ] coordinateRestriction b (rowWord t))))) = _
  rw [Representation.Equiv.symm_apply_apply, TensorProduct.map_tmul]
  rw [spechtTensorMap]
  change wordTensor _ _ _
    ((φ (projectedCoordinate a (rowWord s))).val ⊗ₜ[ℂ]
      (ψ (projectedCoordinate b (rowWord t))).val) = _
  rw [hφ,hψ,TensorProduct.smul_tmul_smul,map_smul]

theorem pair_coordinate_in_projected_dual_image {n : ℕ} {α β : YoungDiagram}
    (a s : Tableau n α) (b t : Tableau n β)
    (P : (Fin n → Fin (α.colLen 0 * β.colLen 0)) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w)
    (hp : P (mergeWords (rowWord s) (rowWord t)))
    (φ : (spechtRep a).Equiv (signTwist (spechtRep (transposeTableau a))))
    (ψ : (spechtRep b).Equiv (signTwist (spechtRep (transposeTableau b)))) :
    wordTensor _ _ _ (polytabloid (transposeTableau s) ⊗ₜ[ℂ]
      polytabloid (transposeTableau t)) ∈
      ((dualTensorSignMap a b φ ψ).comp
        (intertwiningDual (X := Specht a ⊗[ℂ] Specht b) (projectedTensorQuotient a b P hP))).range := by
  obtain ⟨c,hc,he⟩ := dualTensorSignMap_coordinates a s b t φ ψ
  apply (Submodule.smul_mem_iff _ hc).mp
  refine ⟨projectedTensorEvaluation a b P hP (mergeWords (rowWord s) (rowWord t)), ?_⟩
  change dualTensorSignMap a b φ ψ (intertwiningDual (X := Specht a ⊗[ℂ] Specht b) (projectedTensorQuotient a b P hP)
    (projectedTensorEvaluation a b P hP (mergeWords (rowWord s) (rowWord t)))) = _
  rw [projectedTensorEvaluation_pullback a b P hP _ _ hp]
  exact he

theorem projectedTensor_support_of_coordinate {n : ℕ} {α β μ : YoungDiagram}
    (a s : Tableau n α) (b t : Tableau n β) (u : Tableau n μ)
    (P : (Fin n → Fin (α.colLen 0 * β.colLen 0)) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w)
    (hp : P (mergeWords (rowWord s) (rowWord t)))
    (f : Representation.IntertwiningMap (spechtRep u)
      (cyclic (wordRep n (α.transpose.colLen 0 * β.transpose.colLen 0))
        (wordTensor _ _ _ (polytabloid (transposeTableau s) ⊗ₜ[ℂ]
          polytabloid (transposeTableau t)))).toRepresentation) (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep u)
      (projectedSpechtTensor a b P hP).toRepresentation, Function.Injective F := by
  obtain ⟨φ⟩ := specht_sign_transpose a
  obtain ⟨ψ⟩ := specht_sign_transpose b
  let Q := (dualTensorSignMap a b φ ψ).comp
    (intertwiningDual (X := Specht a ⊗[ℂ] Specht b) (projectedTensorQuotient a b P hP))
  have hm := pair_coordinate_in_projected_dual_image a s b t P hP hp φ ψ
  obtain ⟨i,hi⟩ := subrepresentation_embeds_of_le_range Q
    (cyclic (wordRep n (α.transpose.colLen 0 * β.transpose.colLen 0))
      (wordTensor _ _ _ (polytabloid (transposeTableau s) ⊗ₜ[ℂ]
        polytabloid (transposeTableau t)))) ((cyclic_le _ _ _).mpr hm)
  exact specht_support_of_dual u _ (i.comp f) (intertwining_comp_ne_zero i hi f hf)

end Saxl
end
end

end OAI
