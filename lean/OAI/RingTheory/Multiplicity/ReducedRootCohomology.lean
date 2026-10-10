import Mathlib
import OAI.RingTheory.Multiplicity.CechReduction
import OAI.RingTheory.Multiplicity.RootCechCoefficients
import OAI.RingTheory.Multiplicity.RootSectionDiagram

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
  (m : Fin n → ℤ) (I : Ideal R)

abbrev reducedCech := FiniteModuleCech.complex (FiniteModuleCech.reduction (cechDiagram R n m) I)

def reductionCechIso :
    ((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℕ)).obj (targetCech R n m) ≅
      reducedCech R n m I :=
  ((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℕ)).mapIso (gridComplexIso R n m) ≪≫
    FiniteModuleCech.reductionComplexIso (cechDiagram R n m) I

def integerReductionIso :
    coefficientCech R n m (TensorIdeal.quotientFunctor I) ≅
      (reducedCech R n m I).extend ComplexShape.embeddingUpNat :=
  ComplexExtension.mapExtendIso (TensorIdeal.quotientFunctor I) (targetCech R n m) ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso
      (reductionCechIso R n m I)

def reducedHomologyIso (q : ℕ) :
    (reducedCech R n m I).homology q ≅
      (coefficientCech R n m (TensorIdeal.quotientFunctor I)).homology (q:ℤ) :=
  ((reducedCech R n m I).extendHomologyIso ComplexShape.embeddingUpNat (j:=q) rfl).symm ≪≫
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) (q:ℤ)).mapIso (integerReductionIso R n m I).symm

lemma reduced_pure (q : ℕ) (hq : q≠negativeCount m+1) :
    IsZero ((reducedCech R n m I).homology q) := by
  apply IsZero.of_iso _ (reducedHomologyIso R n m I q)
  apply coefficient_pure
  exact_mod_cast hq

def reducedHomologyEquiv :
    (reducedCech R n m I).homology (negativeCount m+1) ≃ₗ[R]
      (Fin (signedRank m) → R ⧸ I) :=
  (reducedHomologyIso R n m I (negativeCount m+1)).toLinearEquiv ≪≫ₗ
    (coefficientHomologySelfIso R n m (TensorIdeal.quotientFunctor I)).toLinearEquiv ≪≫ₗ
      (TensorProduct.tensorQuotEquivQuotSMul
        ((integerCech R n m).homology (negativeCount m+1)) I).symm ≪≫ₗ
        TensorProduct.equivFinsuppOfBasisLeft (integerHomologyBasis R n m) ≪≫ₗ
          Finsupp.linearEquivFunOnFinite R (R ⧸ I) _

variable (ell : TorsionLength I)
lemma reduced_length :
    ell.value ((reducedCech R n m I).homology (negativeCount m+1)) =
      signedRank m • ell.value (ModuleCat.of R (R ⧸ I)) :=
  (ell.value_linearEquiv (reducedHomologyEquiv R n m I)
    (powerTorsion_fin _ powerTorsion_quotient)).trans (ell.value_fin powerTorsion_quotient _)

lemma reduced_length_zero (q : ℕ) (hq : q≠negativeCount m+1) :
    ell.value ((reducedCech R n m I).homology q)=0 :=
  ell.zero (reduced_pure R n m I q hq)

lemma reduced_length_finite (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤) (q : ℕ) :
    ell.value ((reducedCech R n m I).homology q)≠⊤ := by
  by_cases hq : q=negativeCount m+1
  · rw [hq,reduced_length,nsmul_eq_mul]
    exact ENNReal.mul_ne_top (by simp) hmu
  · rw [reduced_length_zero R n m I ell q hq]
    exact ENNReal.zero_ne_top

end Lech.ProjectiveRoot

end

end OAI
