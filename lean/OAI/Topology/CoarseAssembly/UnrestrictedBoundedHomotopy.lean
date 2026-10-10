import OAI.Topology.CoarseAssembly.BoundedFamilySubdivision

namespace OAI

/-! # Whole-union boundary invariance without uniform homotopy speeds

Finite subdivisions are chosen separately on each component. The two sums
of consecutive samples have uniformly close localized operators. Rotation
and direct-sum additivity cancel the common interior samples in actual Roe K₁.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

namespace BoundedFamilyHomotopy

theorem sampled_telescope (h : BoundedFamilyHomotopy Q r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (o : ∀ i, Q i) (hr : 0 ≤ r) (N : ℕ → ℕ) (τ : ℕ → ℕ → Interval)
    (hnear : (h.sample χ (fun i => N i + 1) τ).boundary o hr =
      (h.sample χ (fun i => N i + 1) (fun i j => τ i (j + 1))).boundary o hr) :
    (h.eval (fun i => τ i 0)).boundary o hr =
      (h.eval (fun i => τ i (N i + 1))).boundary o hr := by
  let := separatedMetric o
  have hleft := h.sample_head_tail_boundary χ o hr N τ
  have hright := h.sample_head_tail_boundary χ o hr N
    (fun i => lastEndpointFirst (N i) (τ i))
  have hh : (fun i => lastEndpointFirst (N i) (τ i) 0) =
      (fun i => τ i (N i + 1)) := funext (fun i => lastEndpointFirst_zero (N i) (τ i))
  have ht : (fun i j => lastEndpointFirst (N i) (τ i) (j + 1)) =
      (fun i j => τ i (j + 1)) := funext (fun i => funext (fun j => lastEndpointFirst_succ (N i) (τ i) j))
  have hh' := congrArg (fun t : ℕ → Interval => (h.eval t).boundary o hr) hh
  have ht' := congrArg (fun t : ℕ → ℕ → Interval => (h.sample χ N t).boundary o hr) ht
  have hright' := hright.trans (congrArg₂ (fun a b => a + b) hh' ht')
  have hrotate := h.sample_rotate_boundary χ o hr N τ
  exact add_right_cancel (hleft.symm.trans (hnear.trans (hrotate.symm.trans hright')))

theorem endpoint_boundary_eq (h : BoundedFamilyHomotopy Q r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (o : ∀ i, Q i) (hr : 0 ≤ r) :
    (h.eval (fun _ => start)).boundary o hr = (h.eval (fun _ => finish)).boundary o hr := by
  let s := h.smallSubdivision
  have he := h.sampled_telescope χ o hr s.count s.time
    (h.sampled_boundary_eq χ o hr s.count s.time s.step)
  have h0 : (fun i => s.time i 0) = (fun _ => start) := funext s.at_start
  have h1 : (fun i => s.time i (s.count i + 1)) = (fun _ => finish) := funext s.at_finish
  have he0 := congrArg (fun t : ℕ → Interval => (h.eval t).boundary o hr) h0
  have he1 := congrArg (fun t : ℕ → Interval => (h.eval t).boundary o hr) h1
  exact he0.symm.trans (he.trans he1)

end BoundedFamilyHomotopy

/-- Arbitrary componentwise continuous unital self-adjoint homotopies with
a common operator bound preserve the whole-union Roe boundary. -/
theorem ampleRipsFamilyBoundary_boundedHomotopy
    (o : ∀ i, Q i) (hr : 0 ≤ r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (h : ∀ i, OddHomotopy C(Point (Q i) r, ℂ))
    (hπ : ∀ t i, (h i).representation t 1 = 1)
    (hs : ∀ t i, IsSelfAdjoint ((h i).operator t))
    (C : ℝ) (hC : 1 ≤ C) (hn : ∀ t i, ‖(h i).operator t‖ ≤ C) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr (fun i => (h i).eval start) (hπ start) (hs start)
      C (zero_le_one.trans hC) (hn start) =
    ampleRipsFamilyBoundary o r hr (fun i => (h i).eval finish) (hπ finish) (hs finish)
      C (zero_le_one.trans hC) (hn finish) := by
  let H : BoundedFamilyHomotopy Q r := ⟨h, hπ, hs, C, hC, hn⟩
  exact H.endpoint_boundary_eq χ o hr

end CoarseAssembly.Rips

end

end OAI
