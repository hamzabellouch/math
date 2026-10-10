import OAI.Topology.CoarseAssembly.AmpleRipsFamily
import OAI.Topology.CoarseAssembly.FamilyEmbeddingIndependence
import OAI.Topology.CoarseAssembly.SeparatedBoundaryCongruence

namespace OAI

/-! # Whole-union Rips boundaries are independent of the ample embeddings -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

def ripsFamilyBoundaryWithEmbeddings (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (hπ : ∀ i, (c i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖(c i).operator‖ ≤ C)
    (V : ∀ i, (c i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) :
    letI := separatedMetric o
    OperatorKTheory.K1 (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2)) :=
  coefficientFamilyBoundary o (fun i => ripsSpatialOperator r (c i) (hπ i))
    (C + 2) (by linarith)
    (fun i => (ripsSpatialOperator_norm_le r (c i) (hπ i)).trans (by linarith [hc i]))
    (r + r) (add_nonneg hr hr) (fun i => ripsSpatialOperator_propagation r hr (c i) (hπ i))
    (fun i => ripsSpatialOperator_selfAdjoint r (c i) (hπ i) (hF i))
    (fun i => ripsSpatialOperator_square_compact r (c i) (hπ i) (hF i)) V

theorem ripsFamilyBoundaryWithEmbeddings_independent (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (hπ : ∀ i, (c i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖(c i).operator‖ ≤ C)
    (V W : ∀ i, (c i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) :
    letI := separatedMetric o
    ripsFamilyBoundaryWithEmbeddings o r hr c hπ hF C hC hc V =
      ripsFamilyBoundaryWithEmbeddings o r hr c hπ hF C hC hc W := by
  let := separatedMetric o
  apply coefficientFamilyBoundary_independent

/-- The previously constructed ample boundary is the representative with the chosen embeddings. -/
theorem ampleRipsFamilyBoundary_eq_withEmbeddings (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (hπ : ∀ i, (c i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖(c i).operator‖ ≤ C) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr c hπ hF C hC hc =
      ripsFamilyBoundaryWithEmbeddings o r hr c hπ hF C hC hc
        (fun i => ampleIsometry (c i).space) := by
  let := separatedMetric o
  apply separatedFamilyBoundary_bound_independent
  · exact fun i => ampleRipsOperator_selfAdjoint r (c i) (hπ i) (hF i)
  · exact fun i => ampleRipsOperator_square_compact r (c i) (hπ i) (hF i)

/-- In particular, every choice of ample embeddings gives the existing whole-union class. -/
theorem ampleRipsFamilyBoundary_embeddings (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (hπ : ∀ i, (c i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖(c i).operator‖ ≤ C)
    (V : ∀ i, (c i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr c hπ hF C hC hc =
      ripsFamilyBoundaryWithEmbeddings o r hr c hπ hF C hC hc V := by
  let := separatedMetric o
  exact (ampleRipsFamilyBoundary_eq_withEmbeddings o r hr c hπ hF C hC hc).trans
    (ripsFamilyBoundaryWithEmbeddings_independent o r hr c hπ hF C hC hc _ V)

end CoarseAssembly.Rips

end

end OAI
