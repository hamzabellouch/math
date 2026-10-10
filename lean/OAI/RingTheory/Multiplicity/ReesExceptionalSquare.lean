import Mathlib
import OAI.RingTheory.Multiplicity.HomogeneousFunctor
import OAI.RingTheory.Multiplicity.ProjectiveReduction
import OAI.RingTheory.Multiplicity.ReesExceptionalRing

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

private local instance concreteRing (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
private local instance baseModule (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (reesGrade I) (Submonoid.powers (denominator I z hz s))
private local instance baseAlgebra (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (reesGrade I) (Submonoid.powers (denominator I z hz s))

lemma graded_square (a : MvPolynomial (Fin (n+1)) R) :
    FilteredFraction.quotientGraded I (gradedMap I z hz a) =
      SourceGraded.mapR I z hgen (CoefficientReduction.graded I (n+1) a) := by
  have hh : (FilteredFraction.quotientGraded I).toRingHom.comp (gradedMap I z hz).toRingHom =
      (SourceGraded.mapR I z hgen).toRingHom.comp (CoefficientReduction.graded I (n+1)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change FilteredFraction.quotientGraded I (gradedMap I z hz (C r)) = _
      rw [gradedMap_C]
      change quotientR I (algebraMap R (reesAlgebra I) r) =
        MvPolynomial.aeval (IdealGraded.generator I z hgen) (MvPolynomial.map (Ideal.Quotient.mk I) (C r))
      rw [MvPolynomial.map_C,MvPolynomial.aeval_C]
      exact IsScalarTower.algebraMap_apply R (R ⧸ I) (IdealGraded.Ring I) r
    · intro j
      change FilteredFraction.quotientGraded I (gradedMap I z hz (X j)) = _
      rw [gradedMap_X]
      change quotientR I (generator I z hz j) =
        MvPolynomial.aeval (IdealGraded.generator I z hgen) (MvPolynomial.map (Ideal.Quotient.mk I) (X j))
      rw [MvPolynomial.map_X,MvPolynomial.aeval_X]
      rfl
  exact RingHom.congr_fun hh a

abbrev exceptionalDenominator (s : Finset (Fin (n+1))) :=
  FilteredFraction.quotientGraded I (denominator I z hz s)
abbrev ExceptionalRing (s : Finset (Fin (n+1))) :=
  Away (SourceGraded.targetGrade I) (exceptionalDenominator I z hz s)

lemma exceptionalDenominator_mem (s : Finset (Fin (n+1))) :
    exceptionalDenominator I z hz s ∈ SourceGraded.targetGrade I s.card := by
  unfold exceptionalDenominator
  rw [FilteredFraction.quotientGraded_apply]
  exact ⟨denominator I z hz s,denominator_mem I z hz s,rfl⟩

def chartRename (s : Finset (Fin (n+1))) :
    Ring I z hz s ≃ₐ[R] FilteredFraction.ReesChart I (product_mem I z hz s) :=
  Homogeneous.awayCongr (reesGrade I) (denominator_eq I z hz s)

def exceptionalRename (s : Finset (Fin (n+1))) :
    ExceptionalRing I z hz s ≃ₐ[R] FilteredFraction.ExceptionalChart I (product_mem I z hz s) :=
  Homogeneous.awayCongr (SourceGraded.targetGrade I)
    (congrArg (FilteredFraction.quotientGraded I) (denominator_eq I z hz s))

 
def reduction (s : Finset (Fin (n+1))) : Ring I z hz s →ₐ[R] ExceptionalRing I z hz s :=
  (exceptionalRename I z hz s).symm.toAlgHom.comp
    ((FilteredFraction.chartReductionAlg I (product_mem I z hz s)).comp
      (chartRename I z hz s).toAlgHom)

lemma reduction_surjective (s : Finset (Fin (n+1))) : Function.Surjective (reduction I z hz s) :=
  (exceptionalRename I z hz s).symm.surjective.comp
    ((FilteredFraction.chartReduction_surjective I (product_mem I z hz s)).comp
      (chartRename I z hz s).surjective)

lemma reduction_mk (s : Finset (Fin (n+1))) (j : ℕ) (a : reesAlgebra I)
    (ha : a ∈ reesGrade I (j • s.card)) :
    reduction I z hz s (Away.mk (reesGrade I) (denominator_mem I z hz s) j a ha) =
      Away.mk (SourceGraded.targetGrade I) (exceptionalDenominator_mem I z hz s) j
        (FilteredFraction.quotientGraded I a) (Graded.map_mem (FilteredFraction.quotientGraded I) ha) := by
  change (exceptionalRename I z hz s).symm
    (FilteredFraction.chartReduction I (product_mem I z hz s)
      (chartRename I z hz s (Away.mk (reesGrade I) (denominator_mem I z hz s) j a ha))) = _
  unfold chartRename
  rw [Homogeneous.awayCongr_mk _ _ _ (FilteredFraction.reesDenominator_mem I (product_mem I z hz s)),
      FilteredFraction.chartReduction_mk]
  unfold exceptionalRename
  exact Homogeneous.awayCongr_symm_mk _ _ _ _ _ _ _

private local instance renamedModule (s : Finset (Fin (n+1))) :
    Module R (FilteredFraction.ReesChart I (product_mem I z hz s)) :=
  Homogeneous.module (reesGrade I) (Submonoid.powers (FilteredFraction.reesDenominator I (product_mem I z hz s)))

lemma reduction_eq_zero_iff (s : Finset (Fin (n+1))) (x : Ring I z hz s) :
    reduction I z hz s x=0 ↔
      FilteredFraction.chartReduction I (product_mem I z hz s) (chartRename I z hz s x)=0 := by
  change (exceptionalRename I z hz s).symm _=0 ↔ _
  exact map_eq_zero_iff _ (exceptionalRename I z hz s).symm.injective

lemma renamed_reduction_kernel (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    letI := renamedModule I z hz s
    (FilteredFraction.chartReduction I (product_mem I z hz s)).ker =
      I • (⊤ : Submodule R (FilteredFraction.ReesChart I (product_mem I z hz s))) := by
  classical
  let k := hs.choose
  have hk : k∈s := hs.choose_spec
  exact FilteredFraction.chartReduction_kernel I (product_mem I z hz s)
    (hz k) (product_mem I z hz (s.erase k)) (Finset.mul_prod_erase s z hk)
      (Finset.card_erase_add_one hk)

private lemma renamed_reduction_zero_iff (s : Finset (Fin (n+1))) (hs : s.Nonempty)
    (x : FilteredFraction.ReesChart I (product_mem I z hz s)) :
    letI := renamedModule I z hz s
    FilteredFraction.chartReduction I (product_mem I z hz s) x = 0 ↔
      x ∈ (I • ⊤ : Submodule R (FilteredFraction.ReesChart I (product_mem I z hz s))) := by
  change x ∈ (FilteredFraction.chartReduction I (product_mem I z hz s)).ker ↔ _
  rw [renamed_reduction_kernel I z hz s hs]

lemma reduction_kernel (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    (reduction I z hz s).toLinearMap.ker = I • (⊤ : Submodule R (Ring I z hz s)) := by
  let := baseModule I z hz s
  let := renamedModule I z hz s
  ext x
  change reduction I z hz s x = 0 ↔ x ∈ _
  exact (reduction_eq_zero_iff I z hz s x).trans
    ((renamed_reduction_zero_iff I z hz s hs (chartRename I z hz s x)).trans
      (linearEquiv_mem_ideal_smul_top_iff I (chartRename I z hz s).toLinearEquiv x))

end Lech.ReesRoot

end

end OAI
