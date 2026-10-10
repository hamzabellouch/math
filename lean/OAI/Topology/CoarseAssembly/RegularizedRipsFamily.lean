import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RegularizedCycle
import OAI.Topology.CoarseAssembly.UnrestrictedBoundedHomotopy

namespace OAI

/-! # Whole-union Roe boundaries of arbitrary families of analytic cycles -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

theorem regularizedFamily_homotopy
    (h : ∀ i, OddHomotopy C(Point (Q i) r, ℂ))
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (o : ∀ i, Q i) (hr : 0 ≤ r) :
    (regularizedFamily (fun i => (h i).eval start) χ).boundary o hr =
      (regularizedFamily (fun i => (h i).eval finish) χ).boundary o hr := by
  let H : BoundedFamilyHomotopy Q r := {
    homotopy := fun i => (h i).regularize (χ i)
    unital := fun t i => ((h i).eval t).regularize_unital (χ i)
    selfAdjoint := fun t i => ((h i).eval t).regularize_selfAdjoint (χ i)
    bound := 1
    one_le_bound := le_rfl
    norm_le := fun t i => ((h i).eval t).regularize_norm_le (χ i) }
  exact H.endpoint_boundary_eq χ o hr

end CoarseAssembly.Rips

end

end OAI
