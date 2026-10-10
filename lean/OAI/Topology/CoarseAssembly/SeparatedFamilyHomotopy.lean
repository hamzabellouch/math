import OAI.Topology.CoarseAssembly.SeparatedFamilyBoundary
import OAI.Topology.CoarseAssembly.DiagonalFamilyContinuity
import OAI.Topology.CoarseAssembly.MultiplierBoundaryHomotopy

namespace OAI

/-! # Whole-union boundary classes under uniform family homotopies -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic Filter Topology

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem separatedFamilyBoundary_homotopy (o : ∀ i, V i)
    (A : Interval → ∀ i, Operator (V i) H) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t i, ‖A t i‖ ≤ C) (r : ℝ) (hr : 0 ≤ r)
    (hp : ∀ t i, PropagationLE r (A t i))
    (hself : ∀ t i, IsSelfAdjoint (A t i))
    (hsq : ∀ t i, IsCompactOperator (A t i * A t i - (1 : Operator (V i) H)))
    (hcont : ∀ t ε, 0 < ε → ∀ᶠ s in 𝓝 t, ∀ i, ‖A s i - A t i‖ ≤ ε) :
    letI := separatedMetric o
    separatedFamilyBoundary o (A start) C hC (hA start) r hr (hp start)
        (hself start) (hsq start) =
      separatedFamilyBoundary o (A finish) C hC (hA finish) r hr (hp finish)
        (hself finish) (hsq finish) := by
  let := separatedMetric o
  exact multiplierBoundaryClass_homotopy
    (fun t => separatedFamilyMultiplier o (A t) C hC (hA t) r hr (hp t))
    (fun t => separatedFamilyMultiplier_selfAdjoint o (A t) C hC (hA t) r hr (hp t) (hself t))
    (fun t => diagonalFamily_square_mem_roe o (A t) C hC (hA t) r hr (hp t) (hself t) (hsq t))
    ((continuous_diagonalFamily A C hC hA hcont).subtype_mk _)

end CoarseAssembly.DiscreteRoe

end

end OAI
