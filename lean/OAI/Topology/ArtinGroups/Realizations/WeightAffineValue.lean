import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver
import OAI.Topology.ArtinGroups.Realizations.WeightInclusion

namespace OAI

namespace HarmonicArtin
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {P E : Type*} [PartialOrder P] [AddCommGroup E] [Module ℝ E]

noncomputable def weightAffineValue (z : P → E) (w : OrderWeights P) : E :=
  Finsupp.linearCombination ℝ z w.weights

lemma weightAffineValue_sum (z : P → E) (w : OrderWeights P) :
    weightAffineValue z w = ∑ p ∈ w.weights.support, w.weights p • z p := rfl

lemma weightAffineValue_fintype [Fintype P] (z : P → E) (w : OrderWeights P) :
    weightAffineValue z w = ∑ p, w.weights p • z p :=
  w.weights.sum_fintype _ (fun p => zero_smul ℝ (z p))

lemma OrderWeights.total_fintype [Fintype P] (w : OrderWeights P) : ∑ p,w.weights p = 1 := by
  rw [←w.total]
  exact (w.weights.sum_fintype (fun _ a => a) (fun _ => rfl)).symm

lemma weightAffineValue_vertex (z : P → E) (p : P) : weightAffineValue z (weightVertex p) = z p := by
  simp [weightAffineValue,weightVertex,Finsupp.linearCombination_single]

lemma weightAffineValue_delete (z : P → E) (w : OrderWeights P) (p : P) (hp : w.weights p < 1) :
    weightAffineValue z w = (1-w.weights p) • weightAffineValue z (weightDelete p w hp) +
      w.weights p • z p := by
  have hn : 1-w.weights p ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  change Finsupp.linearCombination ℝ z w.weights =
    (1-w.weights p) • Finsupp.linearCombination ℝ z ((1-w.weights p)⁻¹ • w.weights.erase p) + _
  rw [map_smul,smul_smul,mul_inv_cancel₀ hn,one_smul]
  rw [←Finsupp.linearCombination_single,←map_add,add_comm,Finsupp.single_add_erase]

lemma weightAffineValue_continuous [Fintype P] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] (z : P → E) : Continuous (weightAffineValue z) := by
  rw [show weightAffineValue z = fun w => ∑ p,w.weights p • z p from funext (weightAffineValue_fintype z)]
  exact continuous_finsetSum _ (fun p _ => (weightEval_continuous p).smul continuous_const)

lemma weightAffineValue_mem (z : P → E) (w : OrderWeights P) (K : Set E)
    (hK : Convex ℝ K) (hz : ∀ p ∈ w.weights.support,z p ∈ K) :
    weightAffineValue z w ∈ K :=
  hK.sum_mem (fun p _ => w.nonneg p) w.total hz

lemma weightAffineValue_map [Fintype P] (z : P → E) (w : OrderWeights P) (f : E →ₗ[ℝ] ℝ) :
    f (weightAffineValue z w) = ∑ p, w.weights p * f (z p) := by
  rw [weightAffineValue_fintype,map_sum]
  simp only [map_smul,smul_eq_mul]

lemma weightAffineValue_le [Fintype P] (z : P → E) (w : OrderWeights P) (f : E →ₗ[ℝ] ℝ)
    (b : ℝ) (hb : ∀ p,f (z p) ≤ b) : f (weightAffineValue z w) ≤ b := by
  rw [weightAffineValue_map]
  calc
    ∑ p,w.weights p * f (z p) ≤ ∑ p,w.weights p * b :=
      Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hb p) (w.nonneg p))
    _ = b := by rw [←Finset.sum_mul,w.total_fintype,one_mul]

lemma weightAffineValue_eq_iff [Fintype P] (z : P → E) (w : OrderWeights P) (f : E →ₗ[ℝ] ℝ)
    (b : ℝ) (hb : ∀ p,f (z p) ≤ b) :
    f (weightAffineValue z w) = b ↔ ∀ p ∈ w.weights.support, f (z p) = b := by
  rw [weightAffineValue_map]
  have hsum : b = ∑ p,w.weights p * b := by rw [←Finset.sum_mul,w.total_fintype,one_mul]
  conv_lhs => rhs; rw [hsum]
  rw [Finset.sum_eq_sum_iff_of_le (fun p _ => mul_le_mul_of_nonneg_left (hb p) (w.nonneg p))]
  constructor
  · intro h p hp
    exact mul_left_cancel₀ (Finsupp.mem_support_iff.mp hp) (h p (Finset.mem_univ _))
  · intro h p _
    by_cases hp : p ∈ w.weights.support
    · rw [h p hp]
    · simp only [Finsupp.notMem_support_iff.mp hp,zero_mul]

noncomputable def weightMax (w : OrderWeights P) : P := weightChain w (Fin.last (weightDim w))

lemma weightMax_mem (w : OrderWeights P) : weightMax w ∈ w.weights.support :=
  (weightEnum w (Fin.last (weightDim w))).property

lemma le_weightMax (w : OrderWeights P) (p : P) (hp : p ∈ w.weights.support) : p ≤ weightMax w := by
  have he : weightChain w ((weightEnum w).symm ⟨p,hp⟩) = p :=
    congrArg Subtype.val ((weightEnum w).apply_symm_apply ⟨p,hp⟩)
  rw [←he]
  exact (weightChain w).monotone (Fin.le_last _)

lemma weightAffineValue_cone {Q : Type*} [PartialOrder Q] (z : P → E)
    (f : Q →o P) (c : P) (hc : ∀q,f q ≤ c ∨ c ≤ f q) (t : unitInterval) (w : OrderWeights Q) :
    weightAffineValue z (coneWeights f c hc t w) =
      (1-t.val) • weightAffineValue z (weightMap f w) + t.val • z c := by
  change Finsupp.linearCombination ℝ z (_+_) = _
  rw [map_add,map_smul,Finsupp.linearCombination_single]
  rfl

end HarmonicArtin

end OAI
