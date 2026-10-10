import OAI.Topology.CoarseAssembly.RegularizedPrecomposition
import OAI.Topology.CoarseAssembly.RegularizedRipsFamily
import OAI.Topology.CoarseAssembly.ControlledRipsCoarsening

namespace OAI

/-! # Explicit regularization is compatible with Rips coarsening -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r s : ℝ}

omit [∀ i, DecidableEq (Q i)] in
theorem ControlledCycleFamily.eq_of_cycles_bound (c d : ControlledCycleFamily Q r)
    (hc : c.cycle = d.cycle) (hb : c.bound = d.bound) : c = d := by
  cases c
  cases d
  cases hc
  cases hb
  rfl

omit [∀ i, DecidableEq (Q i)] in
theorem regularizedFamily_coarsen (hrs : r ≤ s)
    (c : ∀ i, OddCycle C(Point (Q i) r, ℂ))
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ) :
    regularizedFamily (fun i => coarsenedCycle hrs (c i))
      (fun i => (χ i).comp (scaleFunctionHom hrs)) = (regularizedFamily c χ).coarsen hrs := by
  apply ControlledCycleFamily.eq_of_cycles_bound _ _ _ rfl
  funext i
  exact (c i).regularize_precomp_eq (scaleFunctionHom hrs) (χ i)

theorem regularizedFamily_boundary_coarsen (o : ∀ i, Q i)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s)
    (c : ∀ i, OddCycle C(Point (Q i) r, ℂ))
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ) :
    (regularizedFamily (fun i => coarsenedCycle hrs (c i))
      (fun i => (χ i).comp (scaleFunctionHom hrs))).boundary o hs =
        (regularizedFamily c χ).boundary o hr := by
  have h1 := congrArg (fun d : ControlledCycleFamily Q s => d.boundary o hs)
    (regularizedFamily_coarsen hrs c χ)
  exact h1.trans (ampleRipsFamilyBoundary_scale hrs o hr hs
    (regularizedFamily c χ).cycle (regularizedFamily c χ).unital
    (regularizedFamily c χ).selfAdjoint (regularizedFamily c χ).bound
    (regularizedFamily c χ).bound_nonneg (regularizedFamily c χ).norm_le)

end CoarseAssembly.Rips

end

end OAI
