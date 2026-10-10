import OAI.RepresentationTheory.VertexAlgebra.CreationZeroExtension

namespace OAI

noncomputable section
namespace CreationBoundary
open Filter Topology

theorem powerSum_zero_of_boundary {c : ℕ → ℂ} (hc : Summable (weightTwo c))
    {ε : ℝ} (hε : 0 < ε)
    (hzero : ∀ t : ℝ, |t| < ε → powerSum c (circlePoint t) = 0) :
    ∀ w : ℂ, ‖w‖ < 1 → powerSum c w = 0 := by
  obtain ⟨δ, hδ, hδ1, hb⟩ := boundary_zero_near_one hc hε hzero
  have ha := analytic_zeroExtension_near_one hc hb
  have hp : ((1+δ/2:ℝ):ℂ) ∈ Metric.ball (1:ℂ) δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, show (1+δ/2:ℝ)-1 = δ/2 by ring, abs_of_pos (by positivity)]
    linarith
  have hn : 1 < ‖((1+δ/2:ℝ):ℂ)‖ := by
    rw [Complex.norm_of_nonneg (by linarith)]
    linarith
  have he : zeroExtension (powerSum c) =ᶠ[nhds ((1+δ/2:ℝ):ℂ)] (fun _ => 0) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hn] with z hz
    simp [zeroExtension, not_le.mpr hz]
  have hball : Set.EqOn (zeroExtension (powerSum c)) (fun _ => 0) (Metric.ball (1:ℂ) δ) :=
    ha.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_ball (1:ℂ) δ).isPreconnected hp he
  have hq : ((1-δ/2:ℝ):ℂ) ∈ Metric.ball (1:ℂ) δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, show (1-δ/2:ℝ)-1 = -(δ/2) by ring, abs_neg,
      abs_of_pos (by positivity)]
    linarith
  have hqn : ‖((1-δ/2:ℝ):ℂ)‖ < 1 := by
    rw [Complex.norm_of_nonneg (by linarith)]
    linarith
  have heq : powerSum c =ᶠ[nhds ((1-δ/2:ℝ):ℂ)] (fun _ => 0) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hq,
      (isOpen_lt continuous_norm continuous_const).mem_nhds hqn] with z hz hzn
    simpa [zeroExtension, hzn.le] using hball hz
  have qall : Set.EqOn (powerSum c) (fun _ => 0) (Metric.ball (0:ℂ) 1) :=
    (analyticOnNhd_powerSum hc).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (convex_ball (0:ℂ) 1).isPreconnected
      (by simpa using hqn) heq
  intro w hw
  exact qall (by simpa using hw)

theorem constant_zero_of_boundary {c : ℕ → ℂ} (hc : Summable (weightTwo c))
    {ε : ℝ} (hε : 0 < ε)
    (hzero : ∀ t : ℝ, |t| < ε → powerSum c (circlePoint t) = 0) : c 0 = 0 := by
  have hz := powerSum_zero_of_boundary hc hε hzero 0 (by simp)
  have hs : powerSum c 0 = c 0 := by
    unfold powerSum
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [zero_pow hn]
  rwa [hs] at hz

end CreationBoundary

end

end OAI
