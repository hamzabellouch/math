import Mathlib
import OAI.RingTheory.FormalGroup.PrimeTorsion
import OAI.GroupTheory.GroupCohomology.CyclicResidue

namespace OAI

/-! The first coordinate correction and its nonzero cyclic residue class. -/

noncomputable section

namespace LowerCoefficientIntegration

open LowerFormalGroup LowerSphereCyclic

def firstCorrection {K : Type} [Field K] {F : FormalGroup K}
    (σ : LowerFormalGroup.End F) (p : ℕ) : K :=
  PowerSeries.coeff p (σ.series - PowerSeries.X)

theorem order_p_correction_and_residue_class
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (K : Type) [Field K] [CharP K p]
    (F : FormalGroup K) [F.IsComm] (σ : LowerFormalGroup.End F)
    (hσp : iterate σ.series p = PowerSeries.X)
    (hσne : σ.series ≠ PowerSeries.X)
    (hheight : (pSeries F p).order = (↑(p ^ (p - 1)) : ℕ∞)) :
    firstCorrection σ p ≠ 0 ∧
      (∃ r : PowerSeries K,
        σ.series = PowerSeries.X +
          PowerSeries.C (firstCorrection σ p) * PowerSeries.X ^ p +
          PowerSeries.X ^ (p + 1) * r) ∧
      gradedBinomialClass p hp K (firstCorrection σ p) ≠ 0 := by
  have hord : (σ.series - PowerSeries.X).order = (p : ℕ∞) :=
    ((order_p_finite_height p hp hodd F σ hσp hσne (p - 1) hheight).2 rfl).1
  have hc : firstCorrection σ p ≠ 0 := (PowerSeries.order_eq_nat.mp hord).1
  refine ⟨hc, ?_, gradedBinomialClass_ne_zero p hp K (firstCorrection σ p) hc⟩
  obtain ⟨c, _, r, hr⟩ := expansion_of_order hord
  have hcoeff : firstCorrection σ p = c := by
    dsimp only [firstCorrection]
    have hd : σ.series - PowerSeries.X =
        PowerSeries.C c * PowerSeries.X ^ p + PowerSeries.X ^ (p + 1) * r := by
      rw [hr]
      ring
    rw [hd, map_add]
    simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X_pow_mul']
  exact ⟨r, hcoeff ▸ hr⟩

end LowerCoefficientIntegration

end

end OAI
