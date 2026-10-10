import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceGluing

namespace OAI

/-! Balance Leaves. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

def singleFiberHom (n k : ℕ) : Equiv.Perm (Fin n) →* fiberGroup (fun _ : Fin n => k) where
  toFun g := ⟨g,fun _ => rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl

lemma singleFiberHom_surjective (n k : ℕ) : Function.Surjective (singleFiberHom n k) :=
  fun g => ⟨g.val,Subtype.ext rfl⟩

lemma specht_fixed_single_sum {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (k : ℕ) (x : Specht t) :
    x.val ∈ fixedSumSpace (fun _ : Fin n => k) (fun a : Fin (μ.colLen 0) => a.val)
      (columnRowSums t (fun _ => k)) := by
  rcases x with ⟨x,hx⟩
  change x ∈ Submodule.span ℂ (Set.range fun g : Equiv.Perm (Fin n) =>
    wordRep n (μ.colLen 0) g (polytabloid t)) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g,rfl⟩ := hy
    exact fixedSumSpace_invariant _ _ _ g (fun _ => rfl) _
      (polytabloid_fixed_column_sums t _ (fun _ _ _ => rfl))
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih => exact Submodule.smul_mem _ a ih

lemma spechtTensor_fixed_single_sum {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (k : ℕ) (x : Specht t ⊗[ℂ] Specht t) :
    FixedComponentSums (fun _ : Fin n => k) (fun a => (output a : ℤ))
      (columnOutputSums t (fun _ => k)) (spechtTensorMap t t x) := by
  classical
  change spechtTensorMap t t x ∈ fixedSumSpace (fun _ : Fin n => k)
    (fun a => (output a : ℤ)) (columnOutputSums t (fun _ => k))
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | tmul x y =>
    intro w hw i
    rw [spechtTensorMap] at hw
    change wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val) w ≠ 0 at hw
    rw [wordTensor_tmul] at hw
    obtain ⟨hx,hy⟩ := mul_ne_zero_iff.mp hw
    have hs₁ := specht_fixed_single_sum t k x (splitLeft w) hx i
    have hs₂ := specht_fixed_single_sum t k y (splitRight w) hy i
    change (∑ p ∈ Finset.univ.filter (fun _ : Fin n => k = i), (output (w p) : ℤ)) = _
    simp only [output, Nat.cast_add, Nat.cast_one, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    change (∑ p ∈ Finset.univ.filter (fun _ : Fin n => k = i), ((splitLeft w p).val : ℤ)) +
      (∑ p ∈ Finset.univ.filter (fun _ : Fin n => k = i), ((splitRight w p).val : ℤ)) + _ = _
    rw [hs₁,hs₂]
    dsimp only [columnOutputSums]
    ring

lemma componentWords_single {n d : ℕ} (k : ℕ) (I : Set ℕ)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (h : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I) (w : Fin n → Fin (d*d)) :
    componentWords (fun _ : Fin n => k) A label w ↔ inOutputs I w := by
  constructor
  · rintro ⟨hA,hl⟩ i
    exact (h _).mp ⟨hA i,hl i⟩
  · intro hw
    exact ⟨fun i => ((h _).mpr (hw i)).1,fun i => ((h _).mpr (hw i)).2⟩

def projectedPiece {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (k : ℕ) (I : Set ℕ)
    (A : Fin (μ.colLen 0 * μ.colLen 0) → Prop)
    (label : Fin (μ.colLen 0 * μ.colLen 0) → ℕ)
    (h : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I) :
    Piece (polytabloid t) (fun _ : Fin n => k) A label
      (columnOutputSums t (fun _ => k)) (singleFiberHom n k)
      (projectedSpechtTensor t t (inOutputs I) (inOutputs_invariant I)).toRepresentation := by
  let W := projectedSpechtTensor t t (inOutputs I) (inOutputs_invariant I)
  let Q := projectedTensorQuotient t t (inOutputs I) (inOutputs_invariant I)
  have hQ : Function.Surjective Q := by
    rintro ⟨y,x,rfl⟩
    exact ⟨x,rfl⟩
  letI : AddCommGroup (Specht t ⊗[ℂ] Specht t) := Module.addCommMonoidToAddCommGroup ℂ
  let s := Classical.choose (intertwining_lift_surjective Q hQ
    (Representation.IntertwiningMap.id W.toRepresentation))
  have hs := Classical.choose_spec (intertwining_lift_surjective Q hQ
    (Representation.IntertwiningMap.id W.toRepresentation))
  let T : Representation.IntertwiningMap W.toRepresentation
      ((wordRep n (μ.colLen 0 * μ.colLen 0)).comp
        ((fiberGroup (fun _ : Fin n => k)).subtype.comp (singleFiberHom n k))) :=
    subrepInclusion W
  refine {
    surj := singleFiberHom_surjective n k
    raw := (spechtTensorMap t t).toLinearMap.comp s.toLinearMap
    raw_mem := ?_
    raw_sums := fun y => spechtTensor_fixed_single_sum t k (s y)
    projected := T
    injective := Subtype.val_injective
    projection_eq := ?_ }
  · intro y
    refine ⟨s y,?_⟩
    change cyclicSquareMap (polytabloid t) (s y) = spechtTensorMap t t (s y)
    rw [cyclicSquareMap_polytabloid]
    rfl
  · intro y
    have he := congrArg Subtype.val (congrArg (fun F : Representation.IntertwiningMap
      W.toRepresentation W.toRepresentation => F y) hs)
    change coordinateProjection (inOutputs I) (spechtTensorMap t t (s y)) = y.val at he
    change coordinateProjection (componentWords (fun _ : Fin n => k) A label)
      (spechtTensorMap t t (s y)) = y.val
    convert he using 2
    apply congrArg coordinateProjection
    funext w
    exact propext (componentWords_single k I A label h w)

end Saxl.Balance
end
end

end OAI
