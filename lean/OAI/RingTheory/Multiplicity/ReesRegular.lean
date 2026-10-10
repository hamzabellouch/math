import Mathlib
import OAI.RingTheory.Multiplicity.HomogeneousZeroPiece
import OAI.RingTheory.Multiplicity.ReesRootBundle

namespace OAI

noncomputable section
namespace Lech.FilteredFraction
open HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)
attribute [local instance] Homogeneous.awayAddCommGroup

 
def chartFraction : Away (reesGrade I) (reesDenominator I hw) →ₗ[R] Localization.Away w :=
  (piece I w d 0).subtype.comp ((reesEquiv I hw 0).toLinearMap.comp
    (Homogeneous.zeroPieceEquiv (reesGrade I) (reesDenominator_mem I hw)).toLinearMap)
lemma chartFraction_apply (x : Away (reesGrade I) (reesDenominator I hw)) :
    chartFraction I hw x = reesAmbient I hw x.val := rfl
lemma chartFraction_injective : Function.Injective (chartFraction I hw) :=
  (piece I w d 0).injective_subtype.comp ((reesEquiv I hw 0).injective.comp
    (Homogeneous.zeroPieceEquiv (reesGrade I) (reesDenominator_mem I hw)).injective)

 

lemma chart_smul_injective (a : R) (ha : a ∣ w) :
    Function.Injective (fun x : Away (reesGrade I) (reesDenominator I hw) => a • x) := by
  have hu : IsUnit (algebraMap R (Localization.Away w) a) :=
    isUnit_of_dvd_unit (map_dvd _ ha) (IsLocalization.Away.algebraMap_isUnit w)
  intro x y hxy
  apply chartFraction_injective I hw
  have hh := congrArg (chartFraction I hw) hxy
  rw [map_smul,map_smul] at hh
  exact hu.mul_left_cancel (by simpa only [Algebra.smul_def] using hh)
end Lech.FilteredFraction

namespace Lech.ReesRoot
open HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
private local instance concreteRing (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
private local instance baseAlgebra (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (reesGrade I) (Submonoid.powers (denominator I z hz s))

include hz in
lemma product_mem (s : Finset (Fin (n+1))) : (∏ j ∈ s, z j) ∈ I^s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs,Finset.card_insert_of_notMem hjs,pow_succ']
      exact Ideal.mul_mem_mul (hz j) ih
lemma denominator_eq (s : Finset (Fin (n+1))) :
    denominator I z hz s = FilteredFraction.reesDenominator I (product_mem I z hz s) :=
  Subtype.ext (denominator_val I z hz s)

 

theorem coordinate_smul_injective (s : Finset (Fin (n+1))) (k : Fin (n+1)) (hk : k ∈ s) :
    Function.Injective (fun x : Ring I z hz s => (z k) • x) := by
  change Function.Injective (fun x : Away (reesGrade I) (denominator I z hz s) => (z k) • x)
  rw [denominator_eq]
  apply FilteredFraction.chart_smul_injective
  exact Finset.dvd_prod_of_mem z hk

end Lech.ReesRoot

end

end OAI
