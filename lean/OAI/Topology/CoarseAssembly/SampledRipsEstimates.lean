import OAI.Topology.CoarseAssembly.SampledHomotopyEstimates
import OAI.Topology.CoarseAssembly.PartitionMapNorm
import OAI.Topology.CoarseAssembly.RipsUniformHomotopy
import OAI.Topology.CoarseAssembly.SeparatedFamilyNearby

namespace OAI

/-! # Bounds for the localized finite sums used in homotopy telescoping -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X]

theorem sampledFiniteSum_partition_sub_norm_le
    (r : ℝ) (h : OddHomotopy C(Point X r, ℂ)) (χ : C(Point X r, ℂ) →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ σ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) (δ : ℝ) (hδ : 0 ≤ δ)
    (hnear : ∀ x j, j < N → ‖h.representation (τ j) (sqrtCoordinate r x) -
      h.representation (σ j) (sqrtCoordinate r x)‖ ≤ δ) :
    ‖(show repeatedHilbert h.space →L[ℂ] Module X (repeatedHilbert h.space) from
        partitionMap (representedSqrt r (sampledFiniteSum h χ N τ C hC hF))) -
      (show repeatedHilbert h.space →L[ℂ] Module X (repeatedHilbert h.space) from
        partitionMap (representedSqrt r (sampledFiniteSum h χ N σ C hC hF)))‖ ≤
      (Fintype.card X : ℝ) * δ := by
  apply (partitionMap_sub_norm_le_sum _ _).trans
  calc
    _ ≤ ∑ _x : X, δ := Finset.sum_le_sum (fun x _ =>
      sampledFiniteSum_representation_sub_norm_le h χ N τ σ C hC hF
        (sqrtCoordinate r x) δ hδ (hnear x))
    _ = _ := by simp

theorem sampledFiniteSum_ample_sub_norm_le
    (r : ℝ) (h : OddHomotopy C(Point X r, ℂ)) (χ : C(Point X r, ℂ) →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ σ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) (hπ : ∀ t, h.representation t 1 = 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hop : ∀ j, j < N → ‖h.operator (τ j) - h.operator (σ j)‖ ≤ δ)
    (hrep : ∀ x j, j < N → ‖h.representation (τ j) (sqrtCoordinate r x) -
      h.representation (σ j) (sqrtCoordinate r x)‖ ≤ δ) :
    ‖ampleRipsOperator r (sampledFiniteSum h χ N τ C hC hF)
        (sampledFiniteSum_unital h χ N τ C hC hF hπ) -
      ampleRipsOperator r (sampledFiniteSum h χ N σ C hC hF)
        (sampledFiniteSum_unital h χ N σ C hC hF hπ)‖ ≤
      δ + (4 * C + 2) * ((Fintype.card X : ℝ) * δ) := by
  apply (coefficientExtension_sub_norm_le (ampleIsometry (repeatedHilbert h.space)) _ _).trans
  apply (localizedSpatialOperator_variation_norm_le _ _ _ _ _ _ C
    (sampledFiniteSum_norm_le h χ N σ C hC hF)).trans
  exact add_le_add (sampledFiniteSum_operator_sub_norm_le h χ N τ σ C hC hF δ hδ hop)
    (mul_le_mul_of_nonneg_left
      (sampledFiniteSum_partition_sub_norm_le r h χ N τ σ C hC hF δ hδ hrep)
      (by linarith))

end CoarseAssembly.Rips

end

end OAI
