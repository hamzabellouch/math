import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootBundle

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open MvPolynomial HomogeneousLocalization ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
 
def ratio (s : Finset (Fin (n+1))) (k j : Fin (n+1)) (hk : k ∈ s) : Ring R n s :=
  coefficientMap R n k s hk (UniversalCoefficientChart.coefficient R n k j)
lemma scalarMap_ratio (s : Finset (Fin (n+1))) (k j : Fin (n+1)) (hk : k ∈ s) :
    scalarMap R n s (ratio R n s k j hk) =
      (↑((targetUnit R n k)⁻¹) : GridAmbient R n) * ↑(targetUnit R n j) := by
  rw [ratio,scalarMap_coefficient,gridTarget_coefficient,targetUnit_val]
lemma ratio_mk (s : Finset (Fin (n+1))) (k j : Fin (n+1)) (hk : k ∈ s) :
    ratio R n s k j hk = Away.mk _ (product_homogeneous R n s) 1
      (X j * projectiveRemainder R n k s) (by
        have hc := Finset.card_erase_add_one hk
        have he : 1+(s.erase k).card=s.card := by omega
        simpa only [one_smul,he] using SetLike.mul_mem_graded (isHomogeneous_X R j)
          (projectiveRemainder_homogeneous R n k s)) := by
  change chartMap R n k s hk (ProjectiveCoefficientChart.forward R n k
    (UniversalCoefficientChart.coefficient R n k j)) = _
  rw [ProjectiveCoefficientChart.forward_coefficient]
  change awayMap _ _ _ (Away.mk _ _ 1 (X j) _) = _
  refine (awayMap_mk (ProjectiveCoefficientChart.grading R n)
    (projectiveRemainder_homogeneous R n k s) (product_eq R n k s hk) 1
    (show X k ∈ ProjectiveCoefficientChart.grading R n 1 from isHomogeneous_X R k)
    (X j) (show X j ∈ ProjectiveCoefficientChart.grading R n (1 • 1) from
      isHomogeneous_X R j)).trans ?_
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk,pow_one]
end Lech.ProjectiveRoot

namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
lemma generator_relation (k j : Fin (n+1)) :
    algebraMap R (reesAlgebra I) (z k) * generator I z hz j =
      algebraMap R (reesAlgebra I) (z j) * generator I z hz k := by
  apply Subtype.ext
  change Polynomial.C (z k) * Polynomial.monomial 1 (z j) =
    Polynomial.C (z j) * Polynomial.monomial 1 (z k)
  rw [Polynomial.C_mul_monomial,Polynomial.C_mul_monomial,mul_comm]

private local instance concreteRing (s : Finset (Fin (n+1))) : CommRing (ReesRoot.Ring I z hz s) := inferInstance
private local instance baseAlgebra (s : Finset (Fin (n+1))) : Algebra R (ReesRoot.Ring I z hz s) :=
  Homogeneous.algebra (reesGrade I) (Submonoid.powers (denominator I z hz s))

 

lemma ratio_relation (s : Finset (Fin (n+1))) (k j : Fin (n+1)) (hk : k ∈ s) :
    algebraMap R (ReesRoot.Ring I z hz s) (z k) *
      ReesRoot.map I z hz s (ProjectiveRoot.ratio R n s k j hk) =
        algebraMap R (ReesRoot.Ring I z hz s) (z j) := by
  rw [ProjectiveRoot.ratio_mk]
  change algebraMap R (ReesRoot.Ring I z hz s) (z k) * Away.map _ _ (Away.mk _ _ 1 _ _) = _
  rw [Away.map_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul,Homogeneous.val_algebraMap,
    Homogeneous.val_algebraMap,Away.val_mk,Localization.mk_eq_mk']
  rw [IsScalarTower.algebraMap_apply R (reesAlgebra I) (Localization.Away (denominator I z hz s))]
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul,IsLocalization.mk'_eq_iff_eq_mul]
  change algebraMap (reesAlgebra I) (Localization.Away (denominator I z hz s))
    (algebraMap R (reesAlgebra I) (z k) *
      gradedMap I z hz (X j * projectiveRemainder R n k s)) =
    algebraMap R (Localization.Away (denominator I z hz s)) (z j) *
      algebraMap (reesAlgebra I) (Localization.Away (denominator I z hz s)) ((denominator I z hz s)^1)
  rw [IsScalarTower.algebraMap_apply R (reesAlgebra I) (Localization.Away (denominator I z hz s)),←map_mul]
  congr 1
  rw [map_mul,gradedMap_X,←mul_assoc,generator_relation,pow_one]
  rw [mul_assoc]
  congr 1
  rw [denominator,ProjectiveRoot.product_eq R n k s hk,map_mul,gradedMap_X]
end Lech.ReesRoot

end

end OAI
