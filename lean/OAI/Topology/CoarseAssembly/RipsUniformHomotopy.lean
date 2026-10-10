import OAI.Topology.CoarseAssembly.LocalizationUniformEstimate
import OAI.Topology.CoarseAssembly.SeparatedFamilyHomotopy

namespace OAI

/-! # Uniform analytic homotopies of Rips families

Continuity is imposed on the Fredholm operators and partition isometries,
before taking the Roe boundary. The estimate has no component-size factor.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe Filter Topology

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X]

theorem ampleRipsOperator_variation_norm_le (r : ℝ) (h : OddHomotopy C(Point X r, ℂ))
    (s t : Interval) (hs : (h.eval s).representation 1 = 1)
    (ht : (h.eval t).representation 1 = 1) (C : ℝ) (hC : ‖h.operator t‖ ≤ C) :
    ‖ampleRipsOperator r (h.eval s) hs - ampleRipsOperator r (h.eval t) ht‖ ≤
      ‖h.operator s - h.operator t‖ + (4 * C + 2) *
        ‖(show h.space →L[ℂ] Module X h.space from partitionMap (representedSqrt r (h.eval s))) -
          (show h.space →L[ℂ] Module X h.space from partitionMap (representedSqrt r (h.eval t)))‖ := by
  apply (coefficientExtension_sub_norm_le (ampleIsometry h.space) _ _).trans
  exact localizedSpatialOperator_variation_norm_le
    (show X → End h.space from representedSqrt r (h.eval s))
    (show X → End h.space from representedSqrt r (h.eval t))
    (representedSqrt_partition r (h.eval s) hs) (representedSqrt_partition r (h.eval t) ht)
    (h.operator s) (h.operator t) C hC

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

theorem ampleRipsFamilyBoundary_uniformHomotopy
    (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ i, OddHomotopy C(Point (Q i) r, ℂ))
    (hπ : ∀ t i, ((h i).eval t).representation 1 = 1)
    (hF : ∀ t i, IsSelfAdjoint ((h i).eval t).operator)
    (C : ℝ) (hC : 0 ≤ C) (hnorm : ∀ t i, ‖(h i).operator t‖ ≤ C)
    (hoperator : ∀ t ε, 0 < ε → ∀ᶠ s in 𝓝 t, ∀ i,
      ‖(h i).operator s - (h i).operator t‖ ≤ ε)
    (hpartition : ∀ t ε, 0 < ε → ∀ᶠ s in 𝓝 t, ∀ i,
      ‖(show (h i).space →L[ℂ] Module (Q i) (h i).space from
          partitionMap (representedSqrt r ((h i).eval s))) -
        (show (h i).space →L[ℂ] Module (Q i) (h i).space from
          partitionMap (representedSqrt r ((h i).eval t)))‖ ≤ ε) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr (fun i => (h i).eval start) (hπ start) (hF start)
      C hC (hnorm start) =
    ampleRipsFamilyBoundary o r hr (fun i => (h i).eval finish) (hπ finish) (hF finish)
      C hC (hnorm finish) := by
  let := separatedMetric o
  have hcont : ∀ t ε, 0 < ε → ∀ᶠ s in 𝓝 t, ∀ i,
      ‖ampleRipsOperator r ((h i).eval s) (hπ s i) -
        ampleRipsOperator r ((h i).eval t) (hπ t i)‖ ≤ ε := by
    intro t ε hε
    let δ := ε / (4 * C + 3)
    have hden : 0 < 4 * C + 3 := by positivity
    have hδ : 0 < δ := div_pos hε hden
    filter_upwards [hoperator t δ hδ, hpartition t δ hδ] with s hs hp
    intro i
    calc
      _ ≤ ‖(h i).operator s - (h i).operator t‖ + (4 * C + 2) *
          ‖(show (h i).space →L[ℂ] Module (Q i) (h i).space from
              partitionMap (representedSqrt r ((h i).eval s))) -
            (show (h i).space →L[ℂ] Module (Q i) (h i).space from
              partitionMap (representedSqrt r ((h i).eval t)))‖ :=
        ampleRipsOperator_variation_norm_le r (h i) s t (hπ s i) (hπ t i) C (hnorm t i)
      _ ≤ δ + (4 * C + 2) * δ :=
        add_le_add (hs i) (mul_le_mul_of_nonneg_left (hp i) (by positivity))
      _ = ε := by dsimp [δ]; field_simp; ring
  exact separatedFamilyBoundary_homotopy o
    (fun t i => ampleRipsOperator r ((h i).eval t) (hπ t i))
    (C + 4) (by linarith)
    (fun t i => (ampleRipsOperator_norm_le r ((h i).eval t) (hπ t i)).trans
      (show ‖((h i).eval t).operator‖ + 4 ≤ C + 4 from add_le_add (hnorm t i) le_rfl))
    (r + r) (add_nonneg hr hr)
    (fun t i => ampleRipsOperator_propagation r hr ((h i).eval t) (hπ t i))
    (fun t i => ampleRipsOperator_selfAdjoint r ((h i).eval t) (hπ t i) (hF t i))
    (fun t i => ampleRipsOperator_square_compact r ((h i).eval t) (hπ t i) (hF t i)) hcont

end CoarseAssembly.Rips

end

end OAI
