import OAI.RingTheory.DirectFiniteness.SlabEvents

namespace OAI

noncomputable section
namespace KaplanskyCounterexample.FiniteGeometry

lemma slab_probability_bound {q : ℝ} (hq : 2 ≤ q) :
    0 ≤ (q^2-1)/(q^119-1) ∧ (q^2-1)/(q^119-1) ≤ 2/q^117 := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hpow119 : 2 ≤ q^119 := hq.trans (by simpa using pow_le_pow_right₀ hq1 (show 1 ≤ 119 by decide))
  have hpow117 : 1 ≤ q^117 := one_le_pow₀ hq1
  have hd : 0 < q^119-1 := by linarith
  refine ⟨div_nonneg (by nlinarith) (le_of_lt hd),?_⟩
  apply (div_le_div_iff₀ hd (pow_pos hq0 _)).mpr
  have he : (q^2-1)*q^117 = q^119-q^117 := by ring
  rw [he]
  linarith

lemma slab_two_count_bound {q r : ℝ} {k : ℕ}
    (hq : 1 ≤ q) (hr : r ≤ 2*q^100) (hk : k ≤ 5) :
    r*(k:ℝ)^2*2^k*(100*q)^2*q^k ≤ 16000000*q^107 := by
  have hq0 : 0 ≤ q := by linarith
  have hk' : (k:ℝ) ≤ 5 := by exact_mod_cast hk
  have htwo : (2:ℝ)^k ≤ 32 := (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (by norm_num)
  have hqk : q^k ≤ q^5 := pow_le_pow_right₀ hq hk
  calc
    _ ≤ (2*q^100)*5^2*32*(100*q)^2*q^5 := by gcongr
    _ = 16000000*q^107 := by ring

lemma slab_four_count_bound {q r : ℝ} {k : ℕ}
    (hq : 1 ≤ q) (hr : r ≤ 2*q^100) (hk : k ≤ 5) :
    (r*q)*(k:ℝ)^4*3^k*(q*q^119)*(q*q^119)^2*q^k ≤ 303750*q^466 := by
  have hq0 : 0 ≤ q := by linarith
  have hk' : (k:ℝ) ≤ 5 := by exact_mod_cast hk
  have hthree : (3:ℝ)^k ≤ 243 := (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hk).trans_eq (by norm_num)
  have hqk : q^k ≤ q^5 := pow_le_pow_right₀ hq hk
  calc
    _ ≤ ((2*q^100)*q)*5^4*243*(q*q^119)*(q*q^119)^2*q^5 := by gcongr
    _ = 303750*q^466 := by ring

lemma slab_weighted_bounds {q p : ℝ} (hq : 2 ≤ q) (hp0 : 0 ≤ p) (hp : p ≤ 2/q^117) :
    10000*p ≤ 20000/q ∧
    (16000000*q^107)*p^2 ≤ 64000000/q ∧
    (303750*q^466)*p^4 ≤ 4860000/q := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hm (n : ℕ) (hn : 1 ≤ n) : q ≤ q^n := by simpa using pow_le_pow_right₀ hq1 hn
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ 10000*(2/q^117) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ = 20000/q^117 := by ring
      _ ≤ 20000/q := div_le_div_of_nonneg_left (by norm_num) hq0 (hm _ (by decide))
  · calc
      _ ≤ (16000000*q^107)*(2/q^117)^2 := by gcongr
      _ = 64000000/q^127 := by field_simp; norm_num
      _ ≤ 64000000/q := div_le_div_of_nonneg_left (by norm_num) hq0 (hm _ (by decide))
  · calc
      _ ≤ (303750*q^466)*(2/q^117)^4 := by gcongr
      _ = 4860000/q^2 := by field_simp; norm_num
      _ ≤ 4860000/q := div_le_div_of_nonneg_left (by norm_num) hq0 (hm _ (by decide))

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
