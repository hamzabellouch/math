import Mathlib
import OAI.RingTheory.Multiplicity.ReesExceptionalSquare
import OAI.RingTheory.Multiplicity.TorsionChartKernel

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded CategoryTheory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
abbrev coefficientDenominator (s : Finset (Fin (n+1))) :=
  CoefficientReduction.graded I (n+1) (ProjectiveRoot.product R n s)
abbrev CoefficientRing (s : Finset (Fin (n+1))) :=
  Away (SourceGraded.sourceGrade I (n+1)) (coefficientDenominator I s)

lemma coefficientDenominator_mem (s : Finset (Fin (n+1))) :
    coefficientDenominator I s ∈ SourceGraded.sourceGrade I (n+1) s.card :=
  Graded.map_mem (CoefficientReduction.graded I (n+1)) (ProjectiveRoot.product_homogeneous R n s)

def coefficientReduction (s : Finset (Fin (n+1))) :
    ProjectiveRoot.Ring R n s →ₗ[R] CoefficientRing I s :=
  CoefficientReduction.chartMap I (n+1) (ProjectiveRoot.product R n s)

lemma coefficientReduction_one (s : Finset (Fin (n+1))) : coefficientReduction I s 1=1 :=
  Homogeneous.awayMap_one _ _ _ (CoefficientReduction.graded_smul I (n+1)) _
lemma coefficientReduction_mul (s : Finset (Fin (n+1))) (a b : ProjectiveRoot.Ring R n s) :
    coefficientReduction I s (a*b)=coefficientReduction I s a * coefficientReduction I s b :=
  Homogeneous.awayMap_mul _ _ _ (CoefficientReduction.graded_smul I (n+1)) _ _ _

def coefficientReductionAlg (s : Finset (Fin (n+1))) :
    ProjectiveRoot.Ring R n s →ₐ[R] CoefficientRing I s where
  toFun := coefficientReduction I s
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := coefficientReduction_one I s
  map_mul' := coefficientReduction_mul I s
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,coefficientReduction_one,Algebra.algebraMap_eq_smul_one]

lemma coefficientReduction_surjective (s : Finset (Fin (n+1))) :
    Function.Surjective (coefficientReduction I s) :=
  CoefficientReduction.chartMap_surjective I (n+1) (ProjectiveRoot.product_homogeneous R n s)

lemma coefficientReduction_mk (s : Finset (Fin (n+1))) (j : ℕ)
    (a : MvPolynomial (Fin (n+1)) R)
    (ha : a∈ProjectiveCoefficientChart.grading R n (j • s.card)) :
    coefficientReduction I s (Away.mk _ (ProjectiveRoot.product_homogeneous R n s) j a ha) =
      Away.mk _ (coefficientDenominator_mem I s) j (CoefficientReduction.graded I (n+1) a)
        (Graded.map_mem (CoefficientReduction.graded I (n+1)) ha) :=
  Homogeneous.awayMap_mk _ _ _ (CoefficientReduction.graded_smul I (n+1)) _ _ _ _

 

def coefficientTargetRename (s : Finset (Fin (n+1))) :
    Away (SourceGraded.targetGrade I) (SourceGraded.mapR I z hgen (coefficientDenominator I s)) ≃ₐ[R]
      ExceptionalRing I z hz s :=
  Homogeneous.awayCongr (SourceGraded.targetGrade I)
    (graded_square I z hz hgen (ProjectiveRoot.product R n s)).symm

def coefficientComparison (s : Finset (Fin (n+1))) :
    CoefficientRing I s →ₗ[R] ExceptionalRing I z hz s :=
  (coefficientTargetRename I z hz hgen s).toLinearMap.comp
    (SourceGraded.chartMapR I z hgen (coefficientDenominator I s))

lemma coefficientComparison_mk (s : Finset (Fin (n+1))) (j : ℕ)
    (a : MvPolynomial (Fin (n+1)) (R ⧸ I))
    (ha : a∈SourceGraded.sourceGrade I (n+1) (j • s.card)) :
    coefficientComparison I z hz hgen s (Away.mk _ (coefficientDenominator_mem I s) j a ha) =
      Away.mk _ (exceptionalDenominator_mem I z hz s) j (SourceGraded.mapR I z hgen a)
        (Graded.map_mem (SourceGraded.mapR I z hgen) ha) := by
  change coefficientTargetRename I z hz hgen s
    (Homogeneous.awayMap _ _ _ (SourceGraded.mapR_smul I z hgen) _ (Away.mk _ _ j a ha)) = _
  rw [Homogeneous.awayMap_mk]
  unfold coefficientTargetRename
  exact Homogeneous.awayCongr_mk _ _ _ _ _ _ _

lemma coefficientComparison_surjective (s : Finset (Fin (n+1))) :
    Function.Surjective (coefficientComparison I z hz hgen s) :=
  (coefficientTargetRename I z hz hgen s).surjective.comp
    (SourceGraded.chart_surjective I z hgen (coefficientDenominator_mem I s))

lemma coefficientComparison_kernel (s : Finset (Fin (n+1))) :
    (coefficientComparison I z hz hgen s).ker =
      (SourceGraded.chartMapR I z hgen (coefficientDenominator I s)).ker := by
  ext x
  change (coefficientTargetRename I z hz hgen s) _=0 ↔ _
  exact map_eq_zero_iff _ (coefficientTargetRename I z hz hgen s).injective

lemma coefficientComparison_kernel_zero (ell : TorsionLength I) (hds : ell.DirectSumZero)
    (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ,0<a → ell.value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
        a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
    (s : Finset (Fin (n+1))) :
    ell.value (ModuleCat.of R (coefficientComparison I z hz hgen s).ker)=0 := by
  rw [coefficientComparison_kernel]
  exact SourceGraded.chart_kernel_zero_torsion I z hgen ell hds (Nat.succ_pos _) hmu ha
    (coefficientDenominator_mem I s)

lemma local_square (s : Finset (Fin (n+1))) (a : ProjectiveRoot.Ring R n s) :
    reduction I z hz s (map I z hz s a) =
      coefficientComparison I z hz hgen s (coefficientReduction I s a) := by
  obtain ⟨j,b,hb,rfl⟩ := Away.mk_surjective _ (ProjectiveRoot.product_homogeneous R n s) a
  change reduction I z hz s (Away.map (gradedMap I z hz) _ (Away.mk _ _ j b hb))=_
  rw [Away.map_mk,reduction_mk]
  rw [coefficientReduction_mk,coefficientComparison_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk]
  congr 1
  exact graded_square I z hz hgen b

end Lech.ReesRoot

end

end OAI
