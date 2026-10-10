import OAI.Topology.CoarseAssembly.UnrestrictedBoundedHomotopy
import OAI.Topology.CoarseAssembly.BoundedRipsTransform

namespace OAI

/-! # Arbitrary componentwise analytic homotopies preserve the Rips boundary

Only the endpoint cycle families need uniform operator bounds. The rational
transform gives norm-one intermediate operators, and finite telescoping
allows arbitrary componentwise speeds.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

theorem ampleRipsFamilyBoundary_homotopy
    (o : ∀ i, Q i) (hr : 0 ≤ r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (h : ∀ i, OddHomotopy C(Point (Q i) r, ℂ))
    (hπ : ∀ t i, (h i).representation t 1 = 1)
    (hs : ∀ t i, IsSelfAdjoint ((h i).operator t))
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hn0 : ∀ i, ‖(h i).operator start‖ ≤ C)
    (hn1 : ∀ i, ‖(h i).operator finish‖ ≤ D) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr (fun i => (h i).eval start) (hπ start) (hs start) C hC hn0 =
      ampleRipsFamilyBoundary o r hr (fun i => (h i).eval finish) (hπ finish) (hs finish) D hD hn1 := by
  let c : ControlledCycleFamily Q r := ⟨(fun i => (h i).eval start), hπ start, hs start, C, hC, hn0⟩
  let d : ControlledCycleFamily Q r := ⟨(fun i => (h i).eval finish), hπ finish, hs finish, D, hD, hn1⟩
  let H : BoundedFamilyHomotopy Q r := {
    homotopy := fun i => (h i).bounded (fun t => hπ t i) (fun t => hs t i)
    unital := hπ
    selfAdjoint := fun t i => boundedTransform_selfAdjoint _ _
    bound := 1
    one_le_bound := le_rfl
    norm_le := fun t i => boundedTransform_norm_le _ _ }
  have he : c.bounded.boundary o hr = d.bounded.boundary o hr := H.endpoint_boundary_eq χ o hr
  exact (c.bounded_boundary o hr).symm.trans (he.trans (d.bounded_boundary o hr))

end CoarseAssembly.Rips

end

end OAI
