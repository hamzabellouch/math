import OAI.RepresentationTheory.VertexAlgebra.MobiusGeometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma density_smooth (M : SL(2,ℝ)) : ContDiff ℝ ∞ (density M) := by
  have he : density M=fun x => constant M+cosine M*Real.cos x+sine M*Real.sin x :=
    funext (density_trigonometric M)
  rw [he]
  exact (contDiff_const.add (contDiff_const.mul Real.contDiff_cos)).add
    (contDiff_const.mul Real.contDiff_sin)
lemma density_derivative (M : SL(2,ℝ)) (x : ℝ) :
    deriv (density M) x= -cosine M*Real.sin x+sine M*Real.cos x := by
  have he : density M=fun x => constant M+cosine M*Real.cos x+sine M*Real.sin x :=
    funext (density_trigonometric M)
  rw [he]
  convert (((Real.hasDerivAt_cos x).const_mul (cosine M)).const_add (constant M)).add
    ((Real.hasDerivAt_sin x).const_mul (sine M)) |>.deriv using 1
  first | rfl | ring
lemma density_derivative_square (M : SL(2,ℝ)) (x : ℝ) :
    (deriv (density M) x)^2= -(density M x)^2+2*constant M*density M x-1 := by
  rw [density_derivative,density_trigonometric]
  linear_combination (cosine M^2+sine M^2)*cos_sq_add_sin_sq x-determinant_constants M
lemma density_pos (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) (x : ℝ) :
    0 < density M x := by
  rw [← F.apply_inv_apply x,← derivative_density M F hF]
  exact F.derivative_positive _
lemma inverse_derivative (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) (x : ℝ) :
    deriv (fun x => F⁻¹ x) x=1/density M x := by
  have h := F.derivative_mul F⁻¹ x
  have hid : (fun y => (F*F⁻¹) y)=fun y => y := by simp
  rw [hid,show deriv (fun y : ℝ => y) x=1 from (hasDerivAt_id x).deriv,
    derivative_density M F hF,F.apply_inv_apply] at h
  exact (eq_div_iff (ne_of_gt (density_pos M F hF x))).mpr (by nlinarith)
lemma integral_inverse_density (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) :
    (∫ x in 0..2*Real.pi, 1/density M x)=2*Real.pi := by
  have he : (fun x => 1/density M x)=deriv (fun x => F⁻¹ x) := funext fun x => (inverse_derivative M F hF x).symm
  rw [he,intervalIntegral.integral_deriv_eq_sub (fun x _ => F⁻¹.differentiable x)
    ((contDiff_infty_iff_deriv.mp F⁻¹.smooth).2.continuous.intervalIntegrable _ _)]
  have hp := F⁻¹.period 0
  simp only [zero_add] at hp
  rw [hp]; ring
lemma integral_density (M : SL(2,ℝ)) :
    (∫ x in 0..2*Real.pi, density M x)=2*Real.pi*constant M := by
  have he : density M=fun x => constant M+cosine M*Real.cos x+sine M*Real.sin x :=
    funext (density_trigonometric M)
  have hc : IntervalIntegrable (fun x => cosine M*Real.cos x) volume 0 (2*Real.pi) :=
    (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun x => sine M*Real.sin x) volume 0 (2*Real.pi) :=
    (continuous_const.mul Real.continuous_sin).intervalIntegrable _ _
  have ha : IntervalIntegrable (fun _ : ℝ => constant M) volume 0 (2*Real.pi) :=
    continuous_const.intervalIntegrable _ _
  rw [he,intervalIntegral.integral_add (ha.add hc) hs,
    intervalIntegral.integral_add ha hc,
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,integral_cos,integral_sin]
  simp [Real.sin_two_pi,Real.cos_two_pi,smul_eq_mul]
lemma anomaly_density (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) (x : ℝ) :
    RealCircleCalculus.anomalyDensity (density M) x=
      2*density M x-2*constant M+1/density M x := by
  rw [RealCircleCalculus.anomalyDensity,density_derivative_square]
  field_simp [ne_of_gt (density_pos M F hF x)]
  ring
lemma anomaly_energy (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) :
    RealCircleCalculus.anomalyEnergy (2*Real.pi) (density M)=2*Real.pi := by
  have hd := (density_smooth M).continuous
  have hi : Continuous (fun x => 1/density M x) :=
    continuous_const.div hd (fun x => ne_of_gt (density_pos M F hF x))
  unfold RealCircleCalculus.anomalyEnergy
  simp_rw [anomaly_density M F hF]
  have h2 : IntervalIntegrable (fun x => 2*density M x) volume 0 (2*Real.pi) :=
    (continuous_const.mul hd).intervalIntegrable _ _
  have ha : IntervalIntegrable (fun _ : ℝ => 2*constant M) volume 0 (2*Real.pi) :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h2.sub ha) (hi.intervalIntegrable _ _),
    intervalIntegral.integral_sub h2 ha,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const,
    integral_density,integral_inverse_density M F hF]
  simp only [sub_zero,smul_eq_mul]
  ring
lemma anomaly_constant_zero (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) (c : ℂ) :
    F.anomaly (fun _ => 1) c=0 := by
  rw [SmoothCircleLift.anomaly,push_constant M F hF,anomaly_energy M F hF]
  have he : RealCircleCalculus.anomalyEnergy (2*Real.pi) (fun _ => 1)=2*Real.pi := by
    simp [RealCircleCalculus.anomalyEnergy,RealCircleCalculus.anomalyDensity]
  rw [he,sub_self,mul_zero,Complex.ofReal_zero,mul_zero]
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
