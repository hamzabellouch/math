import OAI.RepresentationTheory.VertexAlgebra.CreationBoundaryDerivative

namespace OAI

noncomputable section
namespace CreationBoundary
open Filter Topology

def zeroExtension (f : ℂ → ℂ) (z : ℂ) : ℂ := if ‖z‖ ≤ 1 then f z else 0

theorem zeroExtension_hasDerivAt {f d : ℂ → ℂ}
    (hd : ∀ w, ‖w‖ ≤ 1 → HasDerivWithinAt f (d w) {z | ‖z‖ ≤ 1} w)
    {w : ℂ} (hb : ‖w‖ = 1 → f w = 0 ∧ d w = 0) :
    DifferentiableAt ℂ (zeroExtension f) w := by
  rcases lt_trichotomy ‖w‖ 1 with hw | hw | hw
  · have hh := (hd w hw.le).hasDerivAt
      (mem_of_superset ((isOpen_lt continuous_norm continuous_const).mem_nhds hw)
        (fun z (h : ‖z‖ < 1) => (show ‖z‖ ≤ 1 from h.le)))
    apply (hh.congr_of_eventuallyEq _).differentiableAt
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hw] with z hz
    simp [zeroExtension, hz.le]
  · obtain ⟨hfw, hdw⟩ := hb hw
    have hin : HasDerivWithinAt (zeroExtension f) 0 {z | ‖z‖ ≤ 1} w := by
      rw [← hdw]
      apply (hd w hw.le).congr
      · intro z hz
        change ‖z‖ ≤ 1 at hz
        simp [zeroExtension, hz]
      · simp [zeroExtension, hw]
    have hout : HasDerivWithinAt (zeroExtension f) 0 {z | ‖z‖ ≤ 1}ᶜ w := by
      apply (hasDerivWithinAt_const w _ (0:ℂ)).congr
      · intro z hz
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hz
        simp [zeroExtension, hz]
      · simp [zeroExtension, hw, hfw]
    have h := hin.union hout
    rw [Set.union_compl_self, hasDerivWithinAt_univ] at h
    exact h.differentiableAt
  · apply ((hasDerivAt_const w (0:ℂ)).congr_of_eventuallyEq _).differentiableAt
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with z hz
    simp [zeroExtension, not_le.mpr hz]

theorem boundary_zero_near_one {c : ℕ → ℂ} (hc : Summable (weightTwo c))
    {ε : ℝ} (hε : 0 < ε)
    (hzero : ∀ t : ℝ, |t| < ε → powerSum c (circlePoint t) = 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ w ∈ Metric.ball (1:ℂ) δ,
      ‖w‖ = 1 → powerSum c w = 0 ∧ powerDeriv c w = 0 := by
  have ha : ContinuousAt Complex.arg (1:ℂ) :=
    Complex.continuousAt_arg (by simp [Complex.mem_slitPlane_iff])
  have ho : ∀ᶠ w : ℂ in nhds 1, |Complex.arg w| < ε :=
    ha.abs.eventually (gt_mem_nhds (by simpa using hε))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp ho
  refine ⟨min r 1, lt_min hr zero_lt_one, min_le_right _ _, ?_⟩
  intro w hw hwn
  have harg : |Complex.arg w| < ε := hsub (Metric.ball_subset_ball (min_le_left _ _) hw)
  have he : circlePoint (Complex.arg w) = w := by
    simpa [circlePoint, hwn] using Complex.norm_mul_exp_arg_mul_I w
  rw [← he]
  exact ⟨hzero _ harg, powerDeriv_zero_of_boundary hc hzero harg⟩

theorem analytic_zeroExtension_near_one {c : ℕ → ℂ} (hc : Summable (weightTwo c))
    {δ : ℝ} (hb : ∀ w ∈ Metric.ball (1:ℂ) δ, ‖w‖ = 1 →
      powerSum c w = 0 ∧ powerDeriv c w = 0) :
    AnalyticOnNhd ℂ (zeroExtension (powerSum c)) (Metric.ball (1:ℂ) δ) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro w hw
  exact (zeroExtension_hasDerivAt (fun z hz => hasDerivWithinAt_powerSum hc hz)
    (hb w hw)).differentiableWithinAt

end CreationBoundary

end

end OAI
