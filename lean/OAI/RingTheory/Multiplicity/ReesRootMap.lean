import Mathlib
import OAI.RingTheory.Multiplicity.RootTwist

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra

def generator (j : Fin (n+1)) : reesAlgebra I :=
  monomial I 1 ⟨z j,by simpa only [pow_one] using hz j⟩
lemma generator_mem (j : Fin (n+1)) : generator I z hz j ∈ reesGrade I 1 := ⟨_,rfl⟩

def gradedMap : ProjectiveCoefficientChart.grading R n →+*ᵍ reesGrade I :=
  Grading.polynomialMap (reesGrade I) (generator I z hz) (generator_mem I z hz)

@[simp] lemma gradedMap_X (j : Fin (n+1)) : gradedMap I z hz (X j) = generator I z hz j :=
  MvPolynomial.aeval_X _ _
@[simp] lemma gradedMap_C (r : R) : gradedMap I z hz (C r) = algebraMap R (reesAlgebra I) r :=
  MvPolynomial.aeval_C _ _

 
abbrev denominator (s : Finset (Fin (n+1))) : reesAlgebra I :=
  gradedMap I z hz (ProjectiveRoot.product R n s)
lemma denominator_mem (s : Finset (Fin (n+1))) : denominator I z hz s ∈ reesGrade I s.card :=
  Graded.map_mem (gradedMap I z hz) (ProjectiveRoot.product_homogeneous R n s)
lemma denominator_subsets {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    denominator I z hz t = denominator I z hz s * denominator I z hz (t \ s) := by
  simpa only [denominator,map_mul] using
    congrArg (gradedMap I z hz) (ProjectiveRoot.product_sdiff R n hst)
lemma denominator_val (s : Finset (Fin (n+1))) :
    (denominator I z hz s : Polynomial R) = Polynomial.monomial s.card (∏ j ∈ s, z j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [denominator,ProjectiveRoot.product,Finset.prod_empty,map_one,
        OneMemClass.coe_one,Finset.card_empty,Polynomial.monomial_zero_one]
  | @insert j s hjs ih =>
      change ((gradedMap I z hz) (∏ k ∈ insert j s, X k) : Polynomial R) = _
      rw [Finset.prod_insert hjs,map_mul,gradedMap_X]
      change (Polynomial.monomial 1 (z j)) * (denominator I z hz s : Polynomial R) = _
      rw [ih,Polynomial.monomial_mul_monomial,Finset.card_insert_of_notMem hjs,
        Finset.prod_insert hjs,Nat.add_comm 1]

abbrev Ring (s : Finset (Fin (n+1))) := Away (reesGrade I) (denominator I z hz s)

 
def map (s : Finset (Fin (n+1))) : ProjectiveRoot.Ring R n s →+* Ring I z hz s :=
  Away.map (gradedMap I z hz) (ProjectiveRoot.product R n s)

def restriction {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    Ring I z hz s →+* Ring I z hz t :=
  awayMap (reesGrade I) (denominator_mem I z hz (t \ s)) (denominator_subsets I z hz hst)

 

lemma map_restriction {s t : Finset (Fin (n+1))} (hst : s ⊆ t)
    (a : ProjectiveRoot.Ring R n s) :
    map I z hz t (ProjectiveRoot.ringRestriction R n hst a) =
      restriction I z hz hst (map I z hz s a) := by
  obtain ⟨j,b,hb,rfl⟩ := Away.mk_surjective _ (ProjectiveRoot.product_homogeneous R n s) a
  change Away.map _ _ (awayMap _ _ _ (Away.mk _ _ j b hb)) =
    awayMap _ _ _ (Away.map _ _ (Away.mk _ _ j b hb))
  rw [awayMap_mk,Away.map_mk,Away.map_mk,awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk,map_mul,map_pow,denominator]

lemma restriction_self (s : Finset (Fin (n+1))) (a : Ring I z hz s) :
    restriction I z hz (Finset.Subset.refl s) a = a := by
  have h1 : denominator I z hz s = denominator I z hz s * 1 := (mul_one _).symm
  exact (HomogeneousEval.awayMap_same _ _ (SetLike.one_mem_graded (reesGrade I)) _ h1 a).trans
    (HomogeneousEval.awayMap_one _ (denominator_mem I z hz s) h1 a)

lemma restriction_comp {s t v : Finset (Fin (n+1))}
    (hst : s ⊆ t) (htv : t ⊆ v) (a : Ring I z hz s) :
    restriction I z hz htv (restriction I z hz hst a) =
      restriction I z hz (hst.trans htv) a := by
  have h1 := denominator_subsets I z hz hst
  have h2 := denominator_subsets I z hz htv
  have h3 : denominator I z hz v = denominator I z hz s *
      (denominator I z hz (t \ s) * denominator I z hz (v \ t)) := by rw [h2,h1,mul_assoc]
  exact (HomogeneousEval.awayMap_comp _ (denominator_mem I z hz s)
    (denominator_mem I z hz (t \ s)) (denominator_mem I z hz (v \ t)) h1 h2 h3 a).trans
      (HomogeneousEval.awayMap_same _ _ _ _ _ _)

end Lech.ReesRoot

end

end OAI
