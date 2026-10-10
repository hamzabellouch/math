import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin.Geometric

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def reflect (e : E) (f : E →ₗ[ℝ] ℝ) : Module.End ℝ E :=
  LinearMap.id - f.smulRight e

@[simp] lemma reflect_apply (e : E) (f : E →ₗ[ℝ] ℝ) (x : E) :
    reflect e f x = x - f x • e := rfl

lemma reflect_involutive (e : E) (f : E →ₗ[ℝ] ℝ) (hf : f e = 2) :
    Function.Involutive (reflect e f) := by
  intro x
  simp only [reflect_apply, map_sub, map_smul, hf]
  module

noncomputable def reflection (e : E) (f : E →ₗ[ℝ] ℝ) (hf : f e = 2) :
    E ≃ₗ[ℝ] E where
  toLinearMap := reflect e f
  invFun := reflect e f
  left_inv := reflect_involutive e f hf
  right_inv := reflect_involutive e f hf

lemma pair_left (e d : E) (f g : E →ₗ[ℝ] ℝ) (a : ℝ)
    (hf : f e = 2) (hfd : f d = -a) (x : E) :
    f ((reflect e f * reflect d g) x) = - f x - a * g x := by
  simp only [Module.End.mul_apply, reflect_apply, map_sub, map_smul, hf, hfd]
  ring

lemma pair_right (e d : E) (f g : E →ₗ[ℝ] ℝ) (a : ℝ)
    (hg : g d = 2) (hfd : f d = -a) (hge : g e = -a) (x : E) :
    g ((reflect e f * reflect d g) x) = a * f x + (a^2-1) * g x := by
  simp only [Module.End.mul_apply, reflect_apply, map_sub, map_smul, hg, hfd, hge]
  ring

lemma pair_difference (e d : E) (f g : E →ₗ[ℝ] ℝ) (x : E) :
    ∃ p q : ℝ, (reflect e f * reflect d g) x = x + p • e + q • d := by
  refine ⟨-f (x-g x • d), -g x, ?_⟩
  simp only [Module.End.mul_apply, reflect_apply]
  module

lemma pair_power_difference (e d : E) (f g : E →ₗ[ℝ] ℝ) (x : E) (n : ℕ) :
    ∃ p q : ℝ, ((reflect e f * reflect d g)^n) x = x + p • e + q • d := by
  induction n with
  | zero => exact ⟨0, 0, by simp⟩
  | succ n ih =>
    obtain ⟨p,q,h⟩ := ih
    obtain ⟨u,v,hu⟩ := pair_difference e d f g (((reflect e f * reflect d g)^n) x)
    refine ⟨p+u, q+v, ?_⟩
    rw [pow_succ', Module.End.mul_apply, hu,h]
    module

noncomputable def phase (c s : ℝ) : ℂ := (c : ℂ) + (s : ℂ) * Complex.I

lemma phase_quad (c s : ℝ) (h : c^2+s^2=1) :
    phase c s ^ 2 = 2*(c : ℂ)*phase c s-1 := by
  apply Complex.ext <;> simp [phase,Complex.mul_re,Complex.mul_im,pow_two] <;> nlinarith

lemma phase_im (c s : ℝ) : (phase c s).im = s := by simp [phase]

lemma pair_phase (e d : E) (f g : E →ₗ[ℝ] ℝ) (c s : ℝ)
    (hf : f e=2) (hg : g d=2) (hfd : f d = -(2*c)) (hge : g e = -(2*c))
    (hcs : c^2+s^2=1) (x : E) :
    (f ((reflect e f * reflect d g) x) : ℂ) + phase c s * g ((reflect e f * reflect d g) x) =
      (phase c s)^2 * ((f x : ℂ) + phase c s * g x) := by
  rw [pair_left e d f g (2*c) hf hfd, pair_right e d f g (2*c) hg hfd hge]
  push_cast
  have hh := phase_quad c s hcs
  calc
    _ = (2*(c:ℂ)*phase c s-1) * ((f x:ℂ)+phase c s*g x) := by
      linear_combination -(g x : ℂ) * (2*(c:ℂ)) * hh
    _ = _ := by rw [hh]

lemma pair_phase_power (e d : E) (f g : E →ₗ[ℝ] ℝ) (c s : ℝ)
    (hf : f e=2) (hg : g d=2) (hfd : f d = -(2*c)) (hge : g e = -(2*c))
    (hcs : c^2+s^2=1) (x : E) (n : ℕ) :
    (f (((reflect e f * reflect d g)^n) x) : ℂ) + phase c s * g (((reflect e f * reflect d g)^n) x) =
      (phase c s)^(2*n) * ((f x : ℂ) + phase c s * g x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, pair_phase e d f g c s hf hg hfd hge hcs, ih]
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega

lemma phase_coordinates_injective (c s : ℝ) (hs : s ≠ 0) {a b a' b' : ℝ}
    (h : (a:ℂ)+phase c s*b = (a':ℂ)+phase c s*b') : a=a' ∧ b=b' := by
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im,Complex.ofReal_im,zero_add,Complex.mul_im,
    Complex.ofReal_re,mul_zero,phase_im] at him
  have hb : b=b' := mul_left_cancel₀ hs him
  subst b'
  have ha : (a:ℂ)=(a':ℂ) := add_right_cancel h
  exact ⟨Complex.ofReal_injective ha,rfl⟩

lemma pair_power_eq_id (e d : E) (f g : E →ₗ[ℝ] ℝ) (c s : ℝ)
    (hf : f e=2) (hg : g d=2) (hfd : f d = -(2*c)) (hge : g e = -(2*c))
    (hcs : c^2+s^2=1) (hs : s ≠ 0) (n : ℕ) (hn : phase c s ^ (2*n) = 1) :
    (reflect e f * reflect d g)^n = 1 := by
  ext x
  obtain ⟨p,q,hpq⟩ := pair_power_difference e d f g x n
  have hh := pair_phase_power e d f g c s hf hg hfd hge hcs x n
  rw [hn,one_mul] at hh
  obtain ⟨hff,hgg⟩ := phase_coordinates_injective c s hs hh
  rw [hpq] at hff hgg
  simp only [map_add,map_smul,hf,hg,hfd,hge,smul_eq_mul] at hff hgg
  have hc : c^2 < 1 := by nlinarith [sq_pos_of_ne_zero hs]
  have hqp : q = c*p := by linarith
  have hmul : (1-c^2)*p=0 := by rw [hqp] at hff; nlinarith [hff]
  have hp : p=0 := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt (sub_pos.mpr hc))
  have hq : q=0 := by rw [hqp,hp,mul_zero]
  simpa [hp,hq] using hpq

end HarmonicArtin.Geometric

end OAI
