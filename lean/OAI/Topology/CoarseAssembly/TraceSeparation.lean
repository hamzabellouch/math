import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.LinearCombination

namespace OAI

/-!
# Trace separation for the congruence-fiber construction

These are elementary ingredients of Lemma 3.1 of *A counterexample to the
coarse Novikov conjecture* (September 23, 2026). No analytic index theorem or
property (T) is assumed here. The actual reduction maps are the existing
`PadicInt.toZModPow` maps.
-/

namespace CoarseAssembly

section LaurentTrace

variable {R : Type*} [CommRing R]

/-- The trace of `diag(t^n,t^(-n),1)`, expressed using a unit so that the
inverse is available in an arbitrary commutative ring. -/
def diagonalTrace (t : Rˣ) (n : ℕ) : R :=
  (t ^ n : Rˣ) + ((t ^ n)⁻¹ : Rˣ) + 1

/-- An integral trace would make the positive power of the unit a root of
`X² + (1-c)X + 1`. Thus a transcendental unit has no such trace. -/
theorem diagonalTrace_ne_int (t : Rˣ) (ht : Transcendental ℤ (t : R))
    {n : ℕ} (hn : 0 < n) (c : ℤ) : diagonalTrace t n ≠ (c : R) := by
  intro h
  let y : R := (t ^ n : Rˣ)
  let z : R := ((t ^ n)⁻¹ : Rˣ)
  have hyz : y * z = 1 := Units.mul_inv (t ^ n)
  have heq : y + z + 1 = (c : R) := h
  have hmul := congrArg (fun a : R => a * y) heq
  have hroot : y ^ 2 + (1 - (c : R)) * y + 1 = 0 := by
    linear_combination hmul - hyz
  let f : Polynomial ℤ := Polynomial.X ^ 2 + Polynomial.C (1 - c) * Polynomial.X + 1
  have htrans : Transcendental ℤ y := by
    simpa [y] using ht.pow hn
  have hf : Polynomial.aeval y f = 0 := by
    simpa [f] using hroot
  have hfzero : f = 0 := (transcendental_iff.mp htrans) f hf
  have hcoeff := congrArg (fun q : Polynomial ℤ => q.coeff 0) hfzero
  simp [f] at hcoeff

end LaurentTrace

section FiniteReduction

variable {p : ℕ} [Fact p.Prime]

/-- Once two p-adic integers differ modulo `p^m`, they differ at every
deeper level. This is the compatibility needed by the short-loop argument. -/
theorem reduction_ne_of_le {x y : ℤ_[p]} {m n : ℕ} (hmn : m ≤ n)
    (hxy : PadicInt.toZModPow m x ≠ PadicInt.toZModPow m y) :
    PadicInt.toZModPow n x ≠ PadicInt.toZModPow n y := by
  intro h
  apply hxy
  rw [← PadicInt.cast_toZModPow m n hmn x, ← PadicInt.cast_toZModPow m n hmn y, h]

/-- Distinct p-adic integers are separated by some finite quotient. -/
theorem exists_reduction_ne {x y : ℤ_[p]} (hxy : x ≠ y) :
    ∃ n : ℕ, PadicInt.toZModPow n x ≠ PadicInt.toZModPow n y := by
  by_contra h
  apply hxy
  exact PadicInt.ext_of_toZModPow.mp (by simpa only [not_exists, not_not] using h)

/-- A finite collection of unequal p-adic pairs has one common positive
level above which every pair remains separated. -/
theorem finite_uniform_reduction_separation {ι : Type*} (s : Finset ι)
    (x y : ι → ℤ_[p]) (hxy : ∀ i ∈ s, x i ≠ y i) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n → ∀ i ∈ s,
      PadicInt.toZModPow n (x i) ≠ PadicInt.toZModPow n (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, le_rfl, by simp⟩
  | @insert i s his ih =>
    obtain ⟨N, hN, hs⟩ := ih (fun j hj => hxy j (Finset.mem_insert_of_mem hj))
    obtain ⟨m, hm⟩ := exists_reduction_ne (hxy i (Finset.mem_insert_self _ _))
    refine ⟨max N m, hN.trans (le_max_left _ _), ?_⟩
    intro n hn j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact reduction_ne_of_le ((le_max_right _ _).trans hn) hm
    · exact hs n ((le_max_left _ _).trans hn) j hj

/-- The specialization used in the paper: for finitely many integral word
traces and a bounded positive exponent, every sufficiently deep congruence
quotient separates the diagonal holonomy trace from all the word traces.

For a nonzero signed charge, use its positive absolute value; the diagonal
trace is unchanged by reversing the sign. -/
theorem finite_trace_separation (t : ℤ_[p]ˣ)
    (ht : Transcendental ℤ (t : ℤ_[p])) (A : ℕ) (traces : Finset ℤ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n → ∀ m ∈ Finset.Icc 1 A, ∀ c ∈ traces,
      PadicInt.toZModPow n (diagonalTrace t m) ≠ (c : ZMod (p ^ n)) := by
  obtain ⟨N, hN, hsep⟩ := finite_uniform_reduction_separation
    ((Finset.Icc 1 A).product traces)
    (fun q => diagonalTrace t q.1) (fun q => (q.2 : ℤ_[p])) (by
      intro q hq
      have hqm := (Finset.mem_product.mp hq).1
      exact diagonalTrace_ne_int t ht (Finset.mem_Icc.mp hqm).1 q.2)
  refine ⟨N, hN, ?_⟩
  intro n hn m hm c hc
  simpa only [map_intCast] using hsep n hn (m, c) (Finset.mem_product.mpr ⟨hm, hc⟩)

end FiniteReduction

end CoarseAssembly

end OAI
