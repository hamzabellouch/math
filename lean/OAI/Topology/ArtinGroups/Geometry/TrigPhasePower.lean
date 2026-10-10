import Mathlib
import OAI.Topology.ArtinGroups.Geometry.Reflect

namespace OAI

namespace HarmonicArtin.Geometric

lemma trig_phase_power (m : ℕ) (hm : 2 ≤ m) :
    phase (Real.cos (Real.pi / m)) (Real.sin (Real.pi / m)) ^ (2*m) = 1 := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [phase, Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.cos_add_sin_mul_I_pow]
  have ha : (↑(2*m) : ℂ) * (↑(Real.pi / m) : ℂ) = ↑(2*Real.pi) := by
    push_cast
    field_simp [hm0]
  rw [ha,← Complex.ofReal_cos,← Complex.ofReal_sin,Real.cos_two_pi,Real.sin_two_pi]
  simp

lemma trig_phase_nonzero (m : ℕ) (hm : 2 ≤ m) :
    Real.sin (Real.pi / m) ≠ 0 := by
  have hm1 : (1:ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  apply ne_of_gt
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · exact div_lt_self Real.pi_pos hm1

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma reflection_pair_order (e d : E) (f g : E →ₗ[ℝ] ℝ)
    (hf : f e=2) (hg : g d=2) (m : ℕ) (hm : 2 ≤ m)
    (hfd : f d = -(2*Real.cos (Real.pi/m)))
    (hge : g e = -(2*Real.cos (Real.pi/m))) :
    (reflection e f hf * reflection d g hg)^m = 1 := by
  apply LinearEquiv.toLinearMap_injective
  have h := pair_power_eq_id e d f g (Real.cos (Real.pi/m)) (Real.sin (Real.pi/m))
    hf hg hfd hge (by nlinarith [Real.sin_sq_add_cos_sq (Real.pi/m)])
    (trig_phase_nonzero m hm) m (trig_phase_power m hm)
  change (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
    ((reflection e f hf * reflection d g hg)^m)) = 1
  rw [map_pow, map_mul]
  exact h

end HarmonicArtin.Geometric

end OAI
