import OAI.RingTheory.DirectFiniteness.PrimeCertificate

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry

def sourceQ : ℕ := 2^217

lemma sourceQ_ge : 2^200 ≤ sourceQ := by
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 200 ≤ 217)

lemma sourceQ_large : 4800 ≤ sourceQ := by
  exact (by norm_num : 4800 ≤ (2:ℕ)^200).trans sourceQ_ge

lemma sourceQ_pos : 0 < sourceQ := lt_of_lt_of_le (by decide : 0 < 4800) sourceQ_large

lemma exponent_comparison (x : ℕ) (hx : 0 < x) : (x^13)^1200 ≤ (x^217)^72 := by
  rw [← pow_mul,← pow_mul]
  exact pow_le_pow_right₀ (by omega : 1 ≤ x) (by decide : 13*1200 ≤ 217*72)

lemma sourceQ_density : (4800:ℕ)^1200 ≤ sourceQ^72 := by
  exact (pow_le_pow_left' (by norm_num : (4800:ℕ) ≤ 2^13) 1200).trans
    (exponent_comparison 2 (by decide))

lemma source_prime_exists : ∃ p : ℕ, p.Prime ∧ sourceQ^100 ∣ p+1 := by
  have hp : 2*sourceQ^100-1 = mersenne 21701 := by
    unfold sourceQ mersenne
    have h : 21701=217*100+1 := by decide
    rw [h,pow_add,pow_mul,pow_one]
    rw [Nat.mul_comm]
  refine ⟨2*sourceQ^100-1,(by rw [hp]; exact mersenne_21701_prime),?_⟩
  have hpos : 0 < sourceQ^100 := pow_pos sourceQ_pos _
  rw [Nat.sub_add_cancel (by omega : 1 ≤ 2*sourceQ^100)]
  exact dvd_mul_left _ _

local instance : DecidablePred (fun p : ℕ => p.Prime ∧ sourceQ^100 ∣ p+1) := Classical.decPred _

def sourcePrime : ℕ := Nat.find source_prime_exists

def sourceD : ℕ := sourcePrime+1

lemma sourcePrime_prime : sourcePrime.Prime := (Nat.find_spec source_prime_exists).1
lemma sourcePrime_le (p : ℕ) (hp : p.Prime) (hc : sourceQ^100 ∣ p+1) : sourcePrime ≤ p :=
  Nat.find_min' source_prime_exists ⟨hp,hc⟩
lemma sourceD_divisible : sourceQ^100 ∣ sourceD := (Nat.find_spec source_prime_exists).2

lemma sourceD_bounds : sourceQ^100 ≤ sourceD ∧ sourceD ≤ 2*sourceQ^100 := by
  refine ⟨Nat.le_of_dvd (by unfold sourceD; omega) sourceD_divisible,?_⟩
  have hp : 2*sourceQ^100-1 = mersenne 21701 := by
    unfold sourceQ mersenne
    have h : 21701=217*100+1 := by decide
    rw [h,pow_add,pow_mul,pow_one,Nat.mul_comm]
  have hd : sourceQ^100 ∣ (2*sourceQ^100-1)+1 := by
    rw [Nat.sub_add_cancel (by have := pow_pos sourceQ_pos 100; omega)]
    exact dvd_mul_left _ _
  have hb : sourcePrime ≤ 2*sourceQ^100-1 := Nat.find_min' source_prime_exists ⟨(by rw [hp]; exact mersenne_21701_prime),hd⟩
  unfold sourceD
  have := pow_pos sourceQ_pos 100
  omega

lemma sourceD_q_dvd : sourceQ ∣ sourceD :=
  (dvd_pow_self sourceQ (by decide : 100 ≠ 0)).trans sourceD_divisible

lemma sourceD_log : Nat.log sourceQ sourceD = 100 := by
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · exact sourceD_bounds.1
  · calc
      sourceD ≤ 2*sourceQ^100 := sourceD_bounds.2
      _ < sourceQ^100*sourceQ := by
        rw [Nat.mul_comm 2]
        exact Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le (by decide : 2 < 4800) sourceQ_large)
          (pow_pos sourceQ_pos _)
      _ = sourceQ^(100+1) := (pow_succ _ _).symm

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
