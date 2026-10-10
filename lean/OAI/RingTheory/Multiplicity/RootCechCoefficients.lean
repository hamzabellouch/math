import Mathlib
import OAI.RingTheory.Multiplicity.RootCechProjective

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
  (m : Fin n → ℤ) (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive]

abbrev coefficientCech := (F.mapHomologicalComplex (.up ℤ)).obj (integerCech R n m)

def coefficientHomologyIso (q : ℤ) :
    (coefficientCech R n m F).homology q ≅
      ((single (ModuleCat.{u} R) (.up ℤ) (negativeCount m+1)).obj
        (F.obj ((integerCech R n m).homology (negativeCount m+1)))).homology q :=
  ((F.mapHomotopyEquiv (integerCechSplitting R n m)).toHomologyIso q).symm ≪≫
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso
      ((singleMapHomologicalComplex F (.up ℤ) (negativeCount m+1)).app _)

lemma coefficient_pure (q : ℤ) (hq : q≠negativeCount m+1) :
    IsZero ((coefficientCech R n m F).homology q) :=
  (isZero_single_obj_homology (.up ℤ) (negativeCount m+1) _ q hq).of_iso
    (coefficientHomologyIso R n m F q)

def coefficientHomologySelfIso :
    (coefficientCech R n m F).homology (negativeCount m+1) ≅
      F.obj ((integerCech R n m).homology (negativeCount m+1)) :=
  coefficientHomologyIso R n m F (negativeCount m+1) ≪≫
    singleObjHomologySelfIso (.up ℤ) (negativeCount m+1) _

variable (M : ModuleCat.{u} R)
abbrev tensorCech := coefficientCech R n m ((curriedTensor (ModuleCat.{u} R)).flip.obj M)

def integerHomologyBasis : Module.Basis (Fin (signedRank m)) R
    ((integerCech R n m).homology (negativeCount m+1)) :=
  (Classical.choice (targetSigned_pure R n m).2).map
    (((targetCech R n m).extendHomologyIso
      ComplexShape.embeddingUpNat (j:=negativeCount m+1) (by simp)).toLinearEquiv).symm

 

def tensorHomologyEquiv :
    (tensorCech R n m M).homology (negativeCount m+1) ≃ₗ[R] (Fin (signedRank m) → M) :=
  ((coefficientHomologySelfIso R n m
    ((curriedTensor (ModuleCat.{u} R)).flip.obj M)).toLinearEquiv).trans
      ((TensorProduct.equivFinsuppOfBasisLeft (integerHomologyBasis R n m)).trans
        (Finsupp.linearEquivFunOnFinite R M _))

lemma tensor_pure (q : ℤ) (hq : q≠negativeCount m+1) :
    IsZero ((tensorCech R n m M).homology q) :=
  coefficient_pure R n m _ q hq
end Lech.ProjectiveRoot

end

end OAI
