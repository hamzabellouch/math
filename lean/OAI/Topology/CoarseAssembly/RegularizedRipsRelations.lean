import OAI.Topology.CoarseAssembly.RegularizedRipsFamily
import OAI.Topology.CoarseAssembly.CycleDirectSumNormalization
import OAI.Topology.CoarseAssembly.DegenerateRegularization

namespace OAI

/-! # The regularized whole-union boundary respects all analytic cycle relations -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

theorem regularizedFamily_unitary
    (c d : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (h : ∀ i, (c i).UnitaryEquivalent (d i))
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ) (o : ∀ i, Q i) (hr : 0 ≤ r) :
    (regularizedFamily c χ).boundary o hr = (regularizedFamily d χ).boundary o hr := by
  let := separatedMetric o
  let C := regularizedFamily c χ
  let D := regularizedFamily d χ
  exact ampleRipsFamilyBoundary_unitary o r hr C.cycle D.cycle
    (fun i => (h i).regularize (χ i)) C.unital D.unital C.selfAdjoint D.selfAdjoint
    C.bound D.bound C.bound_nonneg D.bound_nonneg C.norm_le D.norm_le

theorem regularizedFamily_directSum
    (c d e : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (h : ∀ i, (c i).IsDirectSum (d i) (e i))
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ) (o : ∀ i, Q i) (hr : 0 ≤ r) :
    (regularizedFamily e χ).boundary o hr =
      (regularizedFamily c χ).boundary o hr + (regularizedFamily d χ).boundary o hr := by
  let := separatedMetric o
  let C := regularizedFamily c χ
  let D := regularizedFamily d χ
  let E := regularizedFamily e χ
  exact ampleRipsFamilyBoundary_directSum o r hr C.cycle D.cycle E.cycle
    (fun i => (h i).regularize (χ i)) C.unital D.unital E.unital
    C.selfAdjoint D.selfAdjoint E.selfAdjoint C.bound D.bound E.bound
    C.bound_nonneg D.bound_nonneg E.bound_nonneg C.norm_le D.norm_le E.norm_le

theorem regularizedFamily_degenerate
    (c : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (h : ∀ i, (c i).Degenerate)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ) (o : ∀ i, Q i) (hr : 0 ≤ r) :
    (regularizedFamily c χ).boundary o hr = 0 := by
  let := separatedMetric o
  let C := regularizedFamily c χ
  exact ampleRipsFamilyBoundary_degenerate o r hr C.cycle C.unital C.selfAdjoint
    C.bound C.bound_nonneg C.norm_le (fun i => (h i).regularize (χ i))

end CoarseAssembly.Rips

end

end OAI
