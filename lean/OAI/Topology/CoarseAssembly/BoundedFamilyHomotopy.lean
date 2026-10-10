import OAI.Topology.CoarseAssembly.ControlledRipsCycles
import OAI.Topology.CoarseAssembly.SampledHomotopyDecomposition
import OAI.Topology.CoarseAssembly.SampledRipsEstimates

namespace OAI

/-! # Bounded analytic homotopies without uniform continuity assumptions -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable (Q : ℕ → Type) [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] (r : ℝ)

structure BoundedFamilyHomotopy where
  homotopy : ∀ i, OddHomotopy C(Point (Q i) r, ℂ)
  unital : ∀ t i, (homotopy i).representation t 1 = 1
  selfAdjoint : ∀ t i, IsSelfAdjoint ((homotopy i).operator t)
  bound : ℝ
  one_le_bound : 1 ≤ bound
  norm_le : ∀ t i, ‖(homotopy i).operator t‖ ≤ bound

variable {Q r}

namespace BoundedFamilyHomotopy

def eval (h : BoundedFamilyHomotopy Q r) (τ : ℕ → Interval) : ControlledCycleFamily Q r where
  cycle i := (h.homotopy i).eval (τ i)
  unital i := h.unital (τ i) i
  selfAdjoint i := h.selfAdjoint (τ i) i
  bound := h.bound
  bound_nonneg := zero_le_one.trans h.one_le_bound
  norm_le i := h.norm_le (τ i) i

def sample (h : BoundedFamilyHomotopy Q r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (N : ℕ → ℕ) (τ : ℕ → ℕ → Interval) : ControlledCycleFamily Q r where
  cycle i := sampledFiniteSum (h.homotopy i) (χ i) (N i) (τ i) h.bound h.one_le_bound
    (fun t => h.norm_le t i)
  unital i := sampledFiniteSum_unital _ _ _ _ _ _ _ (fun t => h.unital t i)
  selfAdjoint i := sampledFiniteSum_selfAdjoint _ _ _ _ _ _ _ (fun t => h.selfAdjoint t i)
  bound := h.bound
  bound_nonneg := zero_le_one.trans h.one_le_bound
  norm_le _ := sampledFiniteSum_norm_le _ _ _ _ _ _ _

theorem sample_head_tail_boundary (h : BoundedFamilyHomotopy Q r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (o : ∀ i, Q i) (hr : 0 ≤ r) (N : ℕ → ℕ) (τ : ℕ → ℕ → Interval) :
    (h.sample χ (fun i => N i + 1) τ).boundary o hr =
      (h.eval (fun i => τ i 0)).boundary o hr +
      (h.sample χ N (fun i j => τ i (j + 1))).boundary o hr := by
  let := separatedMetric o
  exact ampleRipsFamilyBoundary_directSum o r hr _ _ _
    (fun i => sampledFiniteSum_head_tail (h.homotopy i) (χ i) (N i) (τ i)
      h.bound h.one_le_bound (fun t => h.norm_le t i))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem sample_rotate_boundary (h : BoundedFamilyHomotopy Q r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (o : ∀ i, Q i) (hr : 0 ≤ r) (N : ℕ → ℕ) (τ : ℕ → ℕ → Interval) :
    (h.sample χ (fun i => N i + 1) (fun i => lastEndpointFirst (N i) (τ i))).boundary o hr =
      (h.sample χ (fun i => N i + 1) (fun i j => τ i (j + 1))).boundary o hr := by
  let := separatedMetric o
  exact ampleRipsFamilyBoundary_unitary o r hr _ _
    (fun i => sampledFiniteSum_rotate (h.homotopy i) (χ i) (N i) (τ i)
      h.bound h.one_le_bound (fun t => h.norm_le t i)) _ _ _ _ _ _ _ _ _ _

end BoundedFamilyHomotopy

end CoarseAssembly.Rips

end

end OAI
