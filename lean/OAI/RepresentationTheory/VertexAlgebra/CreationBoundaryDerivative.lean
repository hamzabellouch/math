import OAI.RepresentationTheory.VertexAlgebra.CreationBoundaryTaylor

namespace OAI

noncomputable section
namespace CreationBoundary
open Filter Topology

theorem hasDerivWithinAt_powerSum {c : ℕ → ℂ} (hc : Summable (weightTwo c))
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    HasDerivWithinAt (powerSum c) (powerDeriv c w) {z | ‖z‖ ≤ 1} w := by
  rw [hasDerivWithinAt_iff_isLittleO]
  have hO : (fun z => powerSum c z-powerSum c w-(z-w)•powerDeriv c w)
      =O[nhdsWithin w {z | ‖z‖ ≤ 1}] (fun z => (z-w)^2) := by
    apply Asymptotics.IsBigO.of_bound (∑' n, weightTwo c n)
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa only [smul_eq_mul, norm_pow] using powerSum_remainder_norm hc hz hw
  have ht : Tendsto (fun z : ℂ => z-w) (nhdsWithin w {z | ‖z‖ ≤ 1}) (nhds 0) := by
    simpa using ((continuous_sub_right w).tendsto w).mono_left nhdsWithin_le_nhds
  have hl := (Asymptotics.isLittleO_pow_pow (𝕜 := ℂ) (m := 1) (n := 2) (by omega)).comp_tendsto ht
  simpa only [Function.comp_def, pow_one] using hO.trans_isLittleO hl

theorem hasDerivAt_powerSum {c : ℕ → ℂ} (hc : Summable (weightTwo c))
    {w : ℂ} (hw : ‖w‖ < 1) : HasDerivAt (powerSum c) (powerDeriv c w) w := by
  apply (hasDerivWithinAt_powerSum hc hw.le).hasDerivAt
  exact mem_of_superset ((isOpen_lt continuous_norm continuous_const).mem_nhds hw)
    (fun z (h : ‖z‖ < 1) => (show ‖z‖ ≤ 1 from h.le))

theorem analyticOnNhd_powerSum {c : ℕ → ℂ} (hc : Summable (weightTwo c)) :
    AnalyticOnNhd ℂ (powerSum c) (Metric.ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro w hw
  exact (hasDerivAt_powerSum hc (by simpa using hw)).differentiableAt.differentiableWithinAt

def circlePoint (t : ℝ) : ℂ := Complex.exp ((t:ℂ)*Complex.I)

@[simp] theorem norm_circlePoint (t : ℝ) : ‖circlePoint t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I t

theorem hasDerivAt_circlePoint (t : ℝ) :
    HasDerivAt circlePoint (circlePoint t*Complex.I) t := by
  have H := ((Complex.hasDerivAt_exp ((t:ℂ)*Complex.I)).comp (t:ℂ)
    ((hasDerivAt_id (t:ℂ)).mul_const Complex.I)).comp_ofReal
  simpa [circlePoint] using! H

theorem powerDeriv_zero_of_boundary {c : ℕ → ℂ} (hc : Summable (weightTwo c))
    {ε : ℝ} (hzero : ∀ t : ℝ, |t| < ε → powerSum c (circlePoint t) = 0)
    {t : ℝ} (ht : |t| < ε) : powerDeriv c (circlePoint t) = 0 := by
  have hd := (hasDerivWithinAt_powerSum hc (by simp : ‖circlePoint t‖ ≤ 1)).comp_hasDerivAt t
    (hasDerivAt_circlePoint t) (Filter.Eventually.of_forall (fun s => by simp))
  have hz : HasDerivAt (powerSum c ∘ circlePoint) 0 t := by
    apply (hasDerivAt_const t (0:ℂ)).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds ht] with s hs
    exact hzero s hs
  have H := hd.unique hz
  exact (mul_eq_zero.mp H).resolve_right (mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero)

end CreationBoundary

end

end OAI
