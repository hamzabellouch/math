import OAI.RingTheory.DirectFiniteness.FiniteParameters

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

def Qcard (h : ℕ) : ℕ := 2^h

lemma prime_exists (h : ℕ) : ∃ p : ℕ, p.Prime ∧ (Qcard h)^100 ∣ p+1 := by
  have hq : (Qcard h)^100 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by decide : 2 ≠ 0))
  let : NeZero ((Qcard h)^100) := ⟨hq⟩
  obtain ⟨p,_,hp,he⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((isUnit_one : IsUnit (1 : ZMod ((Qcard h)^100))).neg) 0
  refine ⟨p,hp,?_⟩
  apply (ZMod.natCast_eq_zero_iff (p+1) ((Qcard h)^100)).mp
  simp only [Nat.cast_add,Nat.cast_one,he,neg_add_cancel]

local instance (h : ℕ) : DecidablePred (fun p : ℕ => p.Prime ∧ (Qcard h)^100 ∣ p+1) :=
  Classical.decPred _

def prime (h : ℕ) : ℕ := Nat.find (prime_exists h)
def degree (h : ℕ) : ℕ := prime h + 1
def exponent (h : ℕ) : ℕ := Nat.log (Qcard h) (degree h)
def blockdim (h : ℕ) : ℕ := exponent h + 20
def dimension (h : ℕ) : ℕ := 10*blockdim h

lemma prime_prime (h : ℕ) : (prime h).Prime := (Nat.find_spec (prime_exists h)).1
lemma prime_congruent (h : ℕ) : (Qcard h)^100 ∣ prime h+1 :=
  (Nat.find_spec (prime_exists h)).2
lemma prime_le (h p : ℕ) (hp : p.Prime) (hc : (Qcard h)^100 ∣ p+1) : prime h ≤ p :=
  Nat.find_min' _ ⟨hp,hc⟩
lemma prime_pos (h : ℕ) : 0 < prime h := (prime_prime h).pos
lemma prime_ge (h : ℕ) (hh : 2 ≤ h) : 3 ≤ prime h := by
  have hq : 4 ≤ Qcard h := by exact Nat.pow_le_pow_right (by decide : 0 < 2) hh
  have hpow : Qcard h ≤ (Qcard h)^100 := by
    simpa using pow_le_pow_right₀ (by omega : 1 ≤ Qcard h) (by decide : 1 ≤ 100)
  have hl : Qcard h ≤ prime h+1 := hpow.trans
    (Nat.le_of_dvd (by omega) (prime_congruent h))
  omega
lemma prime_odd (h : ℕ) (hh : 2 ≤ h) : Odd (prime h) :=
  (prime_prime h).odd_of_ne_two (by have := prime_ge h hh; omega)
lemma dimension_pos (h : ℕ) : 0 < dimension h := by
  unfold dimension blockdim
  omega

lemma prime_217 : prime 217=FiniteGeometry.sourcePrime := by
  apply le_antisymm
  · exact prime_le 217 _ FiniteGeometry.sourcePrime_prime FiniteGeometry.sourceD_divisible
  · exact FiniteGeometry.sourcePrime_le _ (prime_prime 217) (prime_congruent 217)
lemma degree_217 : degree 217=FiniteGeometry.sourceD := by
  simp only [degree,prime_217,FiniteGeometry.sourceD]
lemma dimension_217 : dimension 217=1200 := by
  unfold dimension blockdim exponent
  rw [degree_217]
  change 10*(Nat.log FiniteGeometry.sourceQ FiniteGeometry.sourceD+20)=1200
  rw [FiniteGeometry.sourceD_log]

end KaplanskyCounterexample.Prescription
end

end OAI
