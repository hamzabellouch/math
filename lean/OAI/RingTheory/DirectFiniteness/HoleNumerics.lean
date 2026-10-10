import OAI.RingTheory.DirectFiniteness.HoleSelection

namespace OAI

noncomputable section
namespace KaplanskyCounterexample.FiniteGeometry

lemma hole_numeric_powers {q D : ℝ} (hq : 12 ≤ q) (hD : q^100 ≤ D) :
    0 < D ∧ q^73 ≤ D^2 ∧ 8*q^75 ≤ D ∧ 4*q^302 ≤ D^4 ∧ 101*q^19695 ≤ D^198 := by
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hd0 : 0 < D := (pow_pos hq0 _).trans_le hD
  have hp (i j : ℕ) (h : i ≤ j) : q^i ≤ q^j := pow_le_pow_right₀ hq1 h
  refine ⟨hd0,?_,?_,?_,?_⟩
  · calc
      q^73 ≤ q^200 := hp _ _ (by decide)
      _ = (q^100)^2 := by rw [← pow_mul]
      _ ≤ D^2 := pow_le_pow_left₀ (le_of_lt (pow_pos hq0 _)) hD _
  · calc
      8*q^75 ≤ q*q^75 := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hq0.le _)
      _ = q^76 := by ring
      _ ≤ q^100 := hp _ _ (by decide)
      _ ≤ D := hD
  · calc
      4*q^302 ≤ q*q^302 := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hq0.le _)
      _ = q^303 := by ring
      _ ≤ q^400 := hp _ _ (by decide)
      _ = (q^100)^4 := by rw [← pow_mul]
      _ ≤ D^4 := pow_le_pow_left₀ (le_of_lt (pow_pos hq0 _)) hD _
  · calc
      101*q^19695 ≤ q^2*q^19695 := mul_le_mul_of_nonneg_right (by nlinarith) (pow_nonneg hq0.le _)
      _ = q^19697 := by rw [← pow_add]
      _ ≤ q^19800 := hp _ _ (by decide)
      _ = (q^100)^198 := by rw [← pow_mul]
      _ ≤ D^198 := pow_le_pow_left₀ (le_of_lt (pow_pos hq0 _)) hD _

lemma hole_probability_mem {q D : ℝ} (hq : 12 ≤ q) (hD : q^100 ≤ D) :
    q^73/D^2 ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨hd,hpow,_,_,_⟩ := hole_numeric_powers hq hD
  constructor
  · positivity
  · exact (div_le_one (sq_pos_of_pos hd)).mpr hpow

/-- Explicit finite alteration arithmetic. The three costs refer to the actual
pair, four-witness rectangle, and 101-point occupancy event families. -/
lemma hole_alteration_numeric {q D N S C B H : ℝ}
    (hq : 12 ≤ q) (hD : q^100 ≤ D) (hN : 0 ≤ N) (hS : 0 ≤ S)
    (hdensity : N ≤ q^72*S)
    (hC : C ≤ D*S*q^2) (hB : B ≤ D^2*N*q^10)
    (hH : H ≤ D^2*N*(q^122)^101) :
    3*N/D^2 ≤ S*(q^73/D^2) -
      (C*2*(q^73/D^2)^2 + B*4*(q^73/D^2)^4 + H*101*(q^73/D^2)^101) := by
  obtain ⟨hd,hpow,hsmall,hrect,hocc⟩ := hole_numeric_powers hq hD
  have hq0 : 0 < q := by linarith
  have hdne : D ≠ 0 := ne_of_gt hd
  let p := q^73/D^2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hmass : 0 ≤ N/D^2 := div_nonneg hN (sq_nonneg D)
  have hpair : C*2*p^2 ≤ S*p/4 := by
    calc
      C*2*p^2 ≤ (D*S*q^2)*2*p^2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by norm_num)) (sq_nonneg p)
      _ = (S*p)*(2*q^75/D) := by dsimp [p]; field_simp
      _ ≤ (S*p)*(1/4) := mul_le_mul_of_nonneg_left
        ((div_le_iff₀ hd).mpr (by nlinarith [hsmall])) (mul_nonneg hS hp)
      _ = S*p/4 := by ring
  have hb : B*4*p^4 ≤ N/D^2 := by
    calc
      B*4*p^4 ≤ (D^2*N*q^10)*4*p^4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB (by norm_num)) (pow_nonneg hp _)
      _ = (N/D^2)*(4*q^302/D^4) := by dsimp [p]; field_simp
      _ ≤ (N/D^2)*1 := mul_le_mul_of_nonneg_left ((div_le_one (pow_pos hd _)).mpr hrect) hmass
      _ = N/D^2 := mul_one _
  have hh : H*101*p^101 ≤ N/D^2 := by
    calc
      H*101*p^101 ≤ (D^2*N*(q^122)^101)*101*p^101 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hH (by norm_num)) (pow_nonneg hp _)
      _ = (N/D^2)*(101*q^19695/D^198) := by dsimp [p]; field_simp
      _ ≤ (N/D^2)*1 := mul_le_mul_of_nonneg_left ((div_le_one (pow_pos hd _)).mpr hocc) hmass
      _ = N/D^2 := mul_one _
  have hE : 12*(N/D^2) ≤ S*p := by
    calc
      12*(N/D^2) ≤ q*(N/D^2) := mul_le_mul_of_nonneg_right hq hmass
      _ = N*(q/D^2) := by ring
      _ ≤ (q^72*S)*(q/D^2) := mul_le_mul_of_nonneg_right hdensity (by positivity)
      _ = S*p := by dsimp [p]; ring
  change 3*N/D^2 ≤ S*p - (C*2*p^2+B*4*p^4+H*101*p^101)
  have heq : 3*N/D^2=3*(N/D^2) := by ring
  rw [heq]
  linarith [hpair,hb,hh,hE]

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
