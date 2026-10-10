import OAI.Topology.CoarseAssembly.LocalizationNormContinuity
import OAI.Topology.CoarseAssembly.SeparatedFamilyHomotopy

namespace OAI

/-! # Uniform operator homotopies with fixed representations

The hypothesis controls the whole family's operator norm. Representation-
varying homotopies and quotient descent are separate obligations.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe Filter Topology

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

theorem ampleRipsFamilyBoundary_fixedRepresentationHomotopy
    (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ i, OddHomotopy C(Point (Q i) r, ℂ))
    (hrep : ∀ s t i, (h i).representation s = (h i).representation t)
    (hπ : ∀ t i, ((h i).eval t).representation 1 = 1)
    (hF : ∀ t i, IsSelfAdjoint ((h i).eval t).operator)
    (C : ℝ) (hC : 0 ≤ C) (hnorm : ∀ t i, ‖(h i).operator t‖ ≤ C)
    (hcont : ∀ t ε, 0 < ε → ∀ᶠ s in 𝓝 t, ∀ i, ‖(h i).operator s - (h i).operator t‖ ≤ ε) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr (fun i => (h i).eval start) (hπ start) (hF start)
      C hC (hnorm start) =
    ampleRipsFamilyBoundary o r hr (fun i => (h i).eval finish) (hπ finish) (hF finish)
      C hC (hnorm finish) := by
  let := separatedMetric o
  have hcontinuous : ∀ t ε, 0 < ε → ∀ᶠ s in 𝓝 t, ∀ i,
      ‖ampleRipsOperator r ((h i).eval s) (hπ s i) -
        ampleRipsOperator r ((h i).eval t) (hπ t i)‖ ≤ ε := by
    intro t ε hε
    filter_upwards [hcont t ε hε] with s hs
    intro i
    exact (ampleRipsOperator_homotopy_norm_le r (h i) s t (hπ s i) (hπ t i)
      (hrep s t i)).trans (hs i)
  exact separatedFamilyBoundary_homotopy o
    (fun t i => ampleRipsOperator r ((h i).eval t) (hπ t i))
    (C + 4) (by linarith)
    (fun t i => (ampleRipsOperator_norm_le r ((h i).eval t) (hπ t i)).trans
      (show ‖((h i).eval t).operator‖ + 4 ≤ C + 4 from
        add_le_add (hnorm t i) le_rfl))
    (r + r) (add_nonneg hr hr)
    (fun t i => ampleRipsOperator_propagation r hr ((h i).eval t) (hπ t i))
    (fun t i => ampleRipsOperator_selfAdjoint r ((h i).eval t) (hπ t i) (hF t i))
    (fun t i => ampleRipsOperator_square_compact r ((h i).eval t) (hπ t i) (hF t i)) hcontinuous

end CoarseAssembly.Rips

end

end OAI
