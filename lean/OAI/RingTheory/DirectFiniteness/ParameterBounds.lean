import OAI.RingTheory.DirectFiniteness.FrameTransport

namespace OAI

noncomputable section
namespace KaplanskyCounterexample.FiniteGeometry

lemma sourceQ_very_large : 3305600000 ≤ sourceQ :=
  (by norm_num : 3305600000 ≤ (2:ℕ)^200).trans sourceQ_ge

lemma sourcePrime_ge : 3 ≤ sourcePrime := by
  have hp : sourceQ ≤ sourceQ^100 := by
    simpa using pow_le_pow_right₀ (by have := sourceQ_pos; omega : 1 ≤ sourceQ) (show 1 ≤ 100 by decide)
  have hb := sourceD_bounds.1
  have hq := sourceQ_large
  unfold sourceD at hb
  omega

lemma sourcePrime_odd : Odd sourcePrime := sourcePrime_prime.odd_of_ne_two (by have := sourcePrime_ge; omega)

lemma small_degree_square {q D : ℕ} (hq : 4 ≤ q) (hD : D ≤ 2*q^100) : D^2 ≤ q^1200 := by
  have hq1 : 1 ≤ q := by omega
  calc
    D^2 ≤ (2*q^100)^2 := Nat.pow_le_pow_left hD 2
    _ = 4*q^200 := by ring
    _ ≤ q*q^200 := Nat.mul_le_mul_right _ hq
    _ = q^201 := by ring
    _ ≤ q^1200 := pow_le_pow_right₀ hq1 (by decide)

lemma small_degree_frame_size {q D : ℕ} (hq : 4 ≤ q) (hD : D ≤ 2*q^100) (hdvd : q ∣ D) :
    D/q+(D/q)*q ≤ q^120 := by
  have hq1 : 1 ≤ q := by omega
  have he := Nat.div_mul_cancel hdvd
  have hb := Nat.div_le_self D q
  calc
    D/q+(D/q)*q ≤ D+D := by omega
    _ ≤ 4*q^100 := by omega
    _ ≤ q*q^100 := Nat.mul_le_mul_right _ hq
    _ = q^101 := by ring
    _ ≤ q^120 := pow_le_pow_right₀ hq1 (by decide)

lemma sourceD_square_le : sourceD^2 ≤ sourceQ^1200 :=
  small_degree_square (sourceQ_large.trans' (by decide)) sourceD_bounds.2

lemma source_frame_size : sourceD/sourceQ+(sourceD/sourceQ)*sourceQ ≤ sourceQ^120 :=
  small_degree_frame_size (sourceQ_large.trans' (by decide)) sourceD_bounds.2 sourceD_q_dvd

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
