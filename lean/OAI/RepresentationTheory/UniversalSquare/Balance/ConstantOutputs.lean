import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPacking

namespace OAI

/-! Constant Outputs. -/

section

noncomputable section
open scoped TensorProduct Classical
namespace Saxl.Balance

def constantOutputMap (n d k : ℕ) :
    Representation.IntertwiningMap (wordRep n (d*d)) (wordRep n 1) :=
  wordMap (fun a _ => if output a = k then 1 else 0)

lemma constantOutputMap_single {n d : ℕ} (k : ℕ) (w : Fin n → Fin (d*d))
    (z : Fin n → Fin 1) :
    constantOutputMap n d k (Pi.single w 1) z =
      if inOutputs {k} w then 1 else 0 := by
  classical
  rw [constantOutputMap,wordMap_single]
  by_cases h : inOutputs {k} w
  · rw [ite_eq_left h]
    have he : ∀ i, output (w i) = k := h
    simp only [he,ite_true,Finset.prod_const_one]
  · rw [ite_eq_right h]
    change ¬ ∀ i, output (w i) = k at h
    push Not at h
    obtain ⟨i,hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma constantOutputMap_projection {n d : ℕ} (k : ℕ) (x : WordSpace n (d*d)) :
    constantOutputMap n d k (coordinateProjection (inOutputs {k}) x) =
      constantOutputMap n d k x := by
  classical
  rw [← (Pi.basisFun ℂ (Fin n → Fin (d*d))).sum_repr x]
  simp only [map_sum,map_smul,Pi.basisFun_apply,coordinateProjection_single]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases h : inOutputs {k} w
  · rw [ite_eq_left h]
  · rw [ite_eq_right h,map_zero,smul_zero]
    funext z
    simp only [Pi.zero_apply,Pi.smul_apply,smul_eq_mul,constantOutputMap_single,ite_eq_right h,mul_zero]

lemma constantOutputMap_pairSum {n d e : ℕ} (k : ℕ)
    (t : Fin n → Fin e) (ht : ∀ i, (t i).val+1 = k)
    (x : WordSpace n (d*d)) (z : Fin n → Fin 1) :
    constantOutputMap n d k x z = pairSumMap n d e x t := by
  classical
  rw [← (Pi.basisFun ℂ (Fin n → Fin (d*d))).sum_repr x]
  simp only [map_sum,map_smul,Pi.basisFun_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  rw [constantOutputMap_single,← merge_split w,pairSumMap_single]
  congr 1
  apply propext
  change (∀ i, output (mergeWords (splitLeft w) (splitRight w) i) = k) ↔ _
  simp only [mergeWords,output,Equiv.symm_apply_apply]
  constructor <;> intro h i <;> have hi := ht i <;> have he := h i <;> omega

theorem constant_output_support {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (k : ℕ) (hk : ∀ i, (columnLengthWord t i).val+1 = k) :
    SupportLE (wordRep n 1)
      (projectedSpechtTensor t t (inOutputs {k}) (inOutputs_invariant {k})).toRepresentation := by
  classical
  let W := projectedSpechtTensor t t (inOutputs {k}) (inOutputs_invariant {k})
  let Q := (constantOutputMap n (μ.colLen 0) k).comp (subrepInclusion W)
  let v : Specht t := ⟨polytabloid t,mem_cyclic _ _⟩
  let y := projectedTensorQuotient t t (inOutputs {k}) (inOutputs_invariant {k}) (v ⊗ₜ[ℂ] v)
  let C : ℂ := (Nat.card (columnGroup t) : ℂ) * signC (columnReversal t).val
  have hC : C ≠ 0 := column_projection_coefficient_ne_zero t
  have hy (z : Fin n → Fin 1) : Q y z = C := by
    change constantOutputMap n (μ.colLen 0) k
      (coordinateProjection (inOutputs {k}) (spechtTensorMap t t (v ⊗ₜ[ℂ] v))) z = C
    rw [constantOutputMap_projection,constantOutputMap_pairSum k (columnLengthWord t) hk]
    have he := congrFun (squared_polytabloid_projection t) (columnLengthWord t)
    change (if wordOrbit (columnLengthWord t) (columnLengthWord t) then
      pairSumMap n (μ.colLen 0) (μ.colLen 0)
        (wordTensor _ _ _ (polytabloid t ⊗ₜ[ℂ] polytabloid t)) (columnLengthWord t) else 0) = _ at he
    rw [ite_eq_left ⟨1,rfl⟩,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one] at he
    unfold spechtTensorMap
    exact he
  have hQ : Function.Surjective Q := by
    intro x
    let z : Fin n → Fin 1 := fun _ => 0
    refine ⟨(x z / C) • y,?_⟩
    funext w
    rw [map_smul,Pi.smul_apply,smul_eq_mul,hy]
    have he : z = w := Subsingleton.elim _ _
    rw [div_mul_cancel₀ _ hC,he]
  obtain ⟨s,hs⟩ := intertwining_lift_surjective Q hQ
    (Representation.IntertwiningMap.id (wordRep n 1))
  apply SupportLE.of_injective s
  intro x y hxy
  have he := congrArg Q hxy
  change (Q.comp s) x = (Q.comp s) y at he
  rw [hs] at he
  exact he

def constantPacking {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (k : ℕ)
    (hk : ∀ i, (columnLengthWord t i).val+1 = k)
    (j : ℕ) (A : Fin (μ.colLen 0 * μ.colLen 0) → Prop)
    (label : Fin (μ.colLen 0 * μ.colLen 0) → ℕ)
    (h : ∀ a, (A a ∧ label a = j) ↔ output a = k) :
    Packing (polytabloid t) A label (Pi.single (fun _ : Fin n => (0 : Fin 1)) 1) :=
  boundedPacking t j {k} A label h (constant_output_support t k hk) _

end Saxl.Balance
end
end

end OAI
