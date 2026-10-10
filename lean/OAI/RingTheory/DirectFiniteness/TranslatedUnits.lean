import OAI.RingTheory.DirectFiniteness.FiniteBlock

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.TranslatedUnits
variable {R : Type u_1} {m : Type u_2} [Ring R]
variable (s t : m → R) (p : R)

def unit (i j : m) : R := s i * p * t j

variable (hts : ∀ i, t i * s i = 1) (hpp : p * p = p)
include hts hpp

lemma unit_middle (i j k : m) : unit s t p i j * unit s t p j k = unit s t p i k := by
  simp only [unit, mul_assoc]
  rw [← mul_assoc (t j), hts, one_mul, ← mul_assoc p p, hpp]

lemma products (horth : ∀ j k, j ≠ k → unit s t p j j * unit s t p k k = 0)
    (i j k r : m) :
    unit s t p i j * unit s t p k r = if j = k then unit s t p i r else 0 := by
  by_cases hjk : j = k
  · subst k
    simpa using unit_middle s t p hts hpp i j r
  · rw [ite_eq_right hjk]
    calc
      _ = (unit s t p i j * unit s t p j j) *
          (unit s t p k k * unit s t p k r) := by
        rw [unit_middle s t p hts hpp, unit_middle s t p hts hpp]
      _ = unit s t p i j * (unit s t p j j * unit s t p k k) * unit s t p k r := by
        simp only [mul_assoc]
      _ = 0 := by rw [horth j k hjk, mul_zero, zero_mul]

omit hpp in
lemma unit_ne_zero (hp : p ≠ 0) (i j : m) : unit s t p i j ≠ 0 := by
  intro h
  apply hp
  have hh : t i * unit s t p i j * s j = p := by
    simp only [unit, ← mul_assoc]
    rw [hts, one_mul, mul_assoc p, hts, mul_one]
  rw [h, mul_zero, zero_mul] at hh
  exact hh.symm

end KaplanskyCounterexample.TranslatedUnits
end

end OAI
