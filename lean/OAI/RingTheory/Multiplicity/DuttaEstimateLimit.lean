import Mathlib
import OAI.RingTheory.Multiplicity.DuttaPerfectionValue

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Lech
lemma dutta_estimate_limit (p d c : ℕ) (hp : 1<p) (e A b B L : ℝ)
    (H : ∀ n : ℕ,c < p^n →
      e*((p^n-c:ℕ):ℝ)^d*(b-A/((p^n-c:ℕ):ℝ)*B) ≤ ((p:ℝ)^n)^d*L) :
    e*b ≤ L := by
  have hpR : 1<(p:ℝ) := by exact_mod_cast hp
  have hp0 : 0<(p:ℝ) := lt_trans zero_lt_one hpR
  have hq : Tendsto (fun n : ℕ => (p:ℝ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hpR
  have hqc : Tendsto (fun n : ℕ => (p:ℝ)^n-(c:ℝ)) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(c:ℝ)) hq
  have hr : Tendsto (fun n : ℕ => ((p:ℝ)^n-(c:ℝ))/(p:ℝ)^n) atTop (𝓝 1) := by
    have hh := (hq.const_div_atTop (c:ℝ)).const_sub 1
    simp only [sub_zero] at hh
    apply hh.congr
    intro n
    have hn : (p:ℝ)^n ≠ 0 := (pow_pos hp0 n).ne'
    field_simp
  have hh := ((hr.pow d).mul
    ((hqc.const_div_atTop A).mul_const B |>.const_sub b)).const_mul e
  simp only [one_pow,zero_mul,sub_zero,one_mul] at hh
  apply le_of_tendsto hh
  have hqn : Tendsto (fun n : ℕ => p^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hp
  filter_upwards [hqn.eventually_ge_atTop (c+1)] with n hn
  have hn' : c < p^n := by omega
  have hh := H n hn'
  rw [Nat.cast_sub hn'.le,Nat.cast_pow] at hh
  have heq : e*(((p:ℝ)^n-(c:ℝ))/(p:ℝ)^n)^d*(b-A/((p:ℝ)^n-(c:ℝ))*B) =
      (e*((p:ℝ)^n-(c:ℝ))^d*(b-A/((p:ℝ)^n-(c:ℝ))*B))/((p:ℝ)^n)^d := by
    rw [div_pow]
    ring
  change e*(_*_ ) ≤ L
  rw [← mul_assoc,heq]
  apply (div_le_iff₀ (pow_pos (pow_pos hp0 n) d)).mpr
  simpa only [mul_comm L] using hh
end Lech

end

end OAI
