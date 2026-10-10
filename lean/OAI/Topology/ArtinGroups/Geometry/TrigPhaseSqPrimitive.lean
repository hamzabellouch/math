import Mathlib
import OAI.Topology.ArtinGroups.Geometry.Cartan

namespace OAI

namespace HarmonicArtin.Geometric

lemma trig_phase_sq_primitive (m : ℕ) (hm : m ≠ 0) :
    IsPrimitiveRoot (phase (Real.cos (Real.pi/m)) (Real.sin (Real.pi/m)) ^ 2) m := by
  have he : phase (Real.cos (Real.pi/m)) (Real.sin (Real.pi/m)) =
      Complex.exp ((Real.pi/(m:ℝ):ℝ)*Complex.I) := by
    rw [Complex.exp_mul_I]
    simp only [phase, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [he, ← Complex.exp_nat_mul]
  convert Complex.isPrimitiveRoot_exp m hm using 2
  push_cast
  ring

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma infinite_pair_power (e d : E) (f g : E →ₗ[ℝ] ℝ)
    (hf : f e=2) (hg : g d=2) (hfd : f d = -2) (hge : g e = -2) (n : ℕ) :
    ((reflect e f * reflect d g)^n) e = (2*(n:ℝ)+1) • e + (2*(n:ℝ)) • d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    simp only [Module.End.mul_apply, reflect_apply, map_add, map_sub, map_smul,
      hf,hg,hfd,hge, Nat.cast_add, Nat.cast_one]
    module

variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
variable {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma simple_pair_pow_eq_one_iff (i j : S) (hij : i ≠ j) (n : ℕ) :
    (cs.simple i*cs.simple j)^n=1 ↔ M i j ∣ n := by
  constructor
  · intro h
    have hrep := congrArg (representation cs) h
    simp only [map_pow, map_mul, representation_simple, map_one] at hrep
    have hlin := congrArg LinearEquiv.automorphismGroup.toLinearMapMonoidHom hrep
    simp only [map_pow, map_mul, map_one] at hlin
    change (reflect (Pi.single i 1) (rootRow M i) *
      reflect (Pi.single j 1) (rootRow M j))^n = 1 at hlin
    by_cases hm : M i j = 0
    · have hh := infinite_pair_power (Pi.single i 1) (Pi.single j 1)
        (rootRow M i) (rootRow M j) (by simp) (by simp)
        (by simp [cartan,hij,hm])
        (by simp [cartan,Ne.symm hij,← M.symmetric i j,hm]) n
      rw [hlin] at hh
      have hc := congrFun hh i
      simp only [Module.End.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_same, Pi.single_eq_of_ne hij, mul_one, mul_zero, add_zero] at hc
      have hn : n=0 := by exact_mod_cast (by linarith : (n:ℝ)=0)
      simp [hn]
    · have hm2 : 2 ≤ M i j := by have := M.off_diagonal i j hij; omega
      let c := Real.cos (Real.pi / (M i j:ℝ))
      let s := Real.sin (Real.pi / (M i j:ℝ))
      have hfd : rootRow M i (Pi.single j 1) = -(2*c) := by
        simp [cartan,hij,hm,c]
      have hge : rootRow M j (Pi.single i 1) = -(2*c) := by
        simp [cartan,Ne.symm hij,← M.symmetric i j,hm,c]
      have hcs : c^2+s^2=1 := by dsimp [c,s]; nlinarith [Real.sin_sq_add_cos_sq (Real.pi/(M i j:ℝ))]
      have hh := pair_phase_power (Pi.single i 1) (Pi.single j 1)
        (rootRow M i) (rootRow M j) c s (by simp) (by simp) hfd hge hcs (Pi.single i 1) n
      rw [hlin, Module.End.one_apply] at hh
      have hnonzero : ((rootRow M i (Pi.single i 1):ℝ):ℂ) +
          phase c s * rootRow M j (Pi.single i 1) ≠ 0 := by
        intro hz
        have hz' := phase_coordinates_injective c s (trig_phase_nonzero (M i j) hm2)
          (a:=rootRow M i (Pi.single i 1)) (b:=rootRow M j (Pi.single i 1))
          (a':=0) (b':=0) (by simpa using hz)
        norm_num at hz'
      have hp : phase c s ^ (2*n)=1 := by
        apply mul_right_cancel₀ hnonzero
        simpa only [one_mul] using hh.symm
      exact ((trig_phase_sq_primitive (M i j) hm).pow_eq_one_iff_dvd n).mp
        (by simpa only [pow_mul] using hp)
  · rintro ⟨k,rfl⟩
    rw [pow_mul, cs.simple_mul_simple_pow, one_pow]

end HarmonicArtin.Geometric

end OAI
