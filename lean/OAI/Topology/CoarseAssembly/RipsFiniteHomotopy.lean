import OAI.Topology.CoarseAssembly.LocalizationContinuity
import OAI.Topology.CoarseAssembly.SeparatedFamilyHomotopy

namespace OAI

/-! # Whole-union invariance for finitely supported analytic homotopies

The representations may vary throughout the homotopy. Finitely many changing
components give the uniform continuity required by the actual Roe algebra.
-/

noncomputable section

namespace CoarseAssembly

open Filter Topology

theorem uniform_continuity_of_finite_variation {T I : Type*} [TopologicalSpace T]
    {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
    (f : ∀ i, T → E i) (hf : ∀ i, Continuous (f i))
    (s : Finset I) (hfix : ∀ i ∉ s, ∀ t u, f i t = f i u) :
    ∀ t ε, 0 < ε → ∀ᶠ u in 𝓝 t, ∀ i, ‖f i u - f i t‖ ≤ ε := by
  intro t ε hε
  have hi : ∀ i ∈ s, ∀ᶠ u in 𝓝 t, ‖f i u - f i t‖ < ε := by
    intro i _
    have hc : ContinuousAt (fun u => ‖f i u - f i t‖) t :=
      ((hf i).sub continuous_const).norm.continuousAt
    exact hc.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [(Filter.eventually_all_finset s).mpr hi] with u hu
  intro i
  by_cases his : i ∈ s
  · exact (hu i his).le
  · rw [hfix i his u t, sub_self, norm_zero]
    exact hε.le

namespace Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

theorem ampleRipsFamilyBoundary_finiteHomotopy
    (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ i, OddHomotopy C(Point (Q i) r, ℂ))
    (hπ : ∀ t i, ((h i).eval t).representation 1 = 1)
    (hF : ∀ t i, IsSelfAdjoint ((h i).eval t).operator)
    (C : ℝ) (hC : 0 ≤ C) (hnorm : ∀ t i, ‖(h i).operator t‖ ≤ C)
    (s : Finset ℕ)
    (hfix : ∀ i ∉ s, ∀ t u,
      (h i).representation t = (h i).representation u ∧
        (h i).operator t = (h i).operator u) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr (fun i => (h i).eval start) (hπ start) (hF start)
      C hC (hnorm start) =
    ampleRipsFamilyBoundary o r hr (fun i => (h i).eval finish) (hπ finish) (hF finish)
      C hC (hnorm finish) := by
  let := separatedMetric o
  have hstatic : ∀ i ∉ s, ∀ t u,
      ampleRipsOperator r ((h i).eval t) (hπ t i) =
        ampleRipsOperator r ((h i).eval u) (hπ u i) := by
    intro i hi t u
    obtain ⟨hrep, hop⟩ := hfix i hi t u
    have ha : (show Q i → End (h i).space from representedSqrt r ((h i).eval t)) =
        (show Q i → End (h i).space from representedSqrt r ((h i).eval u)) := by
      funext x
      exact congrArg (fun ρ => ρ (sqrtCoordinate r x)) hrep
    change coefficientExtension (ampleIsometry (h i).space)
      (localizedSpatialOperator _ _ ((h i).operator t)) =
      coefficientExtension (ampleIsometry (h i).space)
      (localizedSpatialOperator _ _ ((h i).operator u))
    simp only [ha, hop]
  have hcont := uniform_continuity_of_finite_variation
    (fun i t => ampleRipsOperator r ((h i).eval t) (hπ t i))
    (fun i => continuous_ampleRipsOperator r (h i) (fun t => hπ t i)) s hstatic
  exact separatedFamilyBoundary_homotopy o
    (fun t i => ampleRipsOperator r ((h i).eval t) (hπ t i))
    (C + 4) (by linarith)
    (fun t i => (ampleRipsOperator_norm_le r ((h i).eval t) (hπ t i)).trans
      (show ‖((h i).eval t).operator‖ + 4 ≤ C + 4 from add_le_add (hnorm t i) le_rfl))
    (r + r) (add_nonneg hr hr)
    (fun t i => ampleRipsOperator_propagation r hr ((h i).eval t) (hπ t i))
    (fun t i => ampleRipsOperator_selfAdjoint r ((h i).eval t) (hπ t i) (hF t i))
    (fun t i => ampleRipsOperator_square_compact r ((h i).eval t) (hπ t i) (hF t i)) hcont

end Rips

end CoarseAssembly

end

end OAI
