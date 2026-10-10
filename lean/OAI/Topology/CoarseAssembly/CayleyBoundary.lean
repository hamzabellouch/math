import OAI.Topology.CoarseAssembly.Definitions
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # A rational representative of the odd analytic boundary

For a self-adjoint `F`, the square of its Cayley transform, with a minus sign,
equals one modulo the square defect `F² - 1`. This construction will be applied
to the Roe ideal in the controlled pseudolocal algebra.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

theorem selfAdjoint_add_I_isUnit (F : A) (hF : IsSelfAdjoint F) :
    IsUnit (F + algebraMap ℂ A Complex.I) := by
  have hn : -Complex.I ∉ spectrum ℂ F := by
    intro h
    have hi := hF.im_eq_zero_of_mem_spectrum h
    simp at hi
  have hu : IsUnit (algebraMap ℂ A (-Complex.I) - F) :=
    not_not.mp (fun h => hn (spectrum.mem_iff.mpr h))
  convert hu.neg using 1
  simp only [map_neg, neg_sub, sub_neg_eq_add]

@[simp] theorem cayleyDenominator_val (F : A) (hF : IsSelfAdjoint F) :
    (cayleyDenominator F hF : A) = F + algebraMap ℂ A Complex.I :=
  (selfAdjoint_add_I_isUnit F hF).unit_spec

theorem cayleyDenominator_star (F : A) (hF : IsSelfAdjoint F) :
    star (cayleyDenominator F hF : A) = F - algebraMap ℂ A Complex.I := by
  rw [cayleyDenominator_val, star_add, hF.star_eq]
  simp only [← algebraMap_star_comm, Complex.star_def, Complex.conj_I, map_neg,
    sub_eq_add_neg]

theorem cayleyDenominator_normal (F : A) (hF : IsSelfAdjoint F) :
    Commute (star (cayleyDenominator F hF : A)) (cayleyDenominator F hF : A) := by
  rw [cayleyDenominator_star, cayleyDenominator_val]
  have hc : Commute (algebraMap ℂ A Complex.I) F := Algebra.commutes _ _
  exact ((Commute.refl F).sub_left hc).add_right
    (hc.symm.sub_left (Commute.refl _))

@[simp] theorem cayleyUnitary_val (F : A) (hF : IsSelfAdjoint F) :
    (cayleyUnitary F hF : A) =
      star (cayleyDenominator F hF : A) * (↑(cayleyDenominator F hF)⁻¹ : A) := rfl

theorem rationalBoundaryUnitary_defect (F : A) (hF : IsSelfAdjoint F) :
    ((rationalBoundaryUnitary F hF : A) - 1) *
        (cayleyDenominator F hF : A) ^ 2 = -2 * (F ^ 2 - 1) := by
  let b := cayleyDenominator F hF
  have hc : Commute (star (b : A)) (b : A) := cayleyDenominator_normal F hF
  have hci : Commute (star (b : A)) (↑b⁻¹ : A) := hc.units_inv_right
  have he : (cayleyUnitary F hF : A) ^ 2 * (b : A) ^ 2 = star (b : A) ^ 2 := by
    rw [cayleyUnitary_val, hci.mul_pow, mul_assoc,
      ← (Commute.refl (b : A)).units_inv_left.mul_pow, Units.inv_mul, one_pow, mul_one]
  simp only [rationalBoundaryUnitary, Unitary.coe_neg, Submonoid.coe_mul]
  rw [← pow_two]
  rw [sub_mul, neg_mul, he, one_mul]
  rw [cayleyDenominator_star, cayleyDenominator_val]
  have hI : (algebraMap ℂ A Complex.I) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hcI := Algebra.commutes (R := ℂ) (A := A) Complex.I F
  have hI' : algebraMap ℂ A Complex.I * algebraMap ℂ A Complex.I = -1 := by
    simpa only [pow_two] using hI
  noncomm_ring [hcI, hI']
  norm_num

theorem rationalBoundaryUnitary_sub_one_mem (I : TwoSidedIdeal A)
    (F : A) (hF : IsSelfAdjoint F) (hdefect : F ^ 2 - 1 ∈ I) :
    (rationalBoundaryUnitary F hF : A) - 1 ∈ I := by
  let b := cayleyDenominator F hF
  have h : ((rationalBoundaryUnitary F hF : A) - 1) * (b : A) ^ 2 ∈ I := by
    rw [rationalBoundaryUnitary_defect]
    exact I.mul_mem_left _ _ hdefect
  have h' := I.mul_mem_right _ ((↑b⁻¹ : A) ^ 2) h
  have hc : Commute (b : A) (↑b⁻¹ : A) := (Commute.refl (b : A)).units_inv_right
  simpa only [mul_assoc, ← hc.mul_pow, Units.mul_inv, one_pow, mul_one] using h'

theorem rationalBoundaryUnitary_eq_one (F : A) (hF : IsSelfAdjoint F)
    (hsq : F ^ 2 = 1) : rationalBoundaryUnitary F hF = 1 := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  have h := rationalBoundaryUnitary_defect F hF
  rw [hsq, sub_self, mul_zero] at h
  apply (Units.mul_left_inj (cayleyDenominator F hF ^ 2)).mp
  simpa only [Units.val_pow_eq_pow_val, zero_mul, Submonoid.coe_one] using h

end CoarseAssembly.Analytic

end

end OAI
