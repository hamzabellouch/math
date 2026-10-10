import Mathlib
import OAI.RingTheory.Multiplicity.ExceptionalCoefficientSquare
import OAI.RingTheory.Multiplicity.FibreSquare
import OAI.RingTheory.Multiplicity.ReesRootLayers

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory IdealGraded HomogeneousLocalization
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
private local instance coefRing (s : Finset (Fin (n+1))) : CommRing (CoefficientRing I s) := inferInstance
private local instance exRing (s : Finset (Fin (n+1))) : CommRing (ExceptionalRing I z hz s) := inferInstance
private local instance reesRing (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
private local instance coefModule (s : Finset (Fin (n+1))) : Module R (CoefficientRing I s) :=
  Homogeneous.module (SourceGraded.sourceGrade I (n+1)) (Submonoid.powers (coefficientDenominator I s))
private local instance exModule (s : Finset (Fin (n+1))) : Module R (ExceptionalRing I z hz s) :=
  Homogeneous.module (SourceGraded.targetGrade I) (Submonoid.powers (exceptionalDenominator I z hz s))
private local instance reesModule (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (reesGrade I) (Submonoid.powers (denominator I z hz s))
private local instance coefBaseAlgebra (s : Finset (Fin (n+1))) : Algebra R (CoefficientRing I s) :=
  Homogeneous.algebra (SourceGraded.sourceGrade I (n+1)) (Submonoid.powers (coefficientDenominator I s))
private local instance exBaseAlgebra (s : Finset (Fin (n+1))) : Algebra R (ExceptionalRing I z hz s) :=
  Homogeneous.algebra (SourceGraded.targetGrade I) (Submonoid.powers (exceptionalDenominator I z hz s))
private local instance reesBaseAlgebra (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (reesGrade I) (Submonoid.powers (denominator I z hz s))

instance coefficientAlgebra (s : Finset (Fin (n+1))) :
    Algebra (ProjectiveRoot.Ring R n s) (CoefficientRing I s) :=
  (coefficientReductionAlg I s).toRingHom.toAlgebra
private local instance coefficientPModule (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (CoefficientRing I s) := (coefficientAlgebra I s).toModule
instance coefficientTower (s : Finset (Fin (n+1))) :
    IsScalarTower R (ProjectiveRoot.Ring R n s) (CoefficientRing I s) :=
  IsScalarTower.of_algebraMap_eq' (coefficientReductionAlg I s).comp_algebraMap.symm

def exceptionalProjectiveMap (s : Finset (Fin (n+1))) :
    ProjectiveRoot.Ring R n s →ₐ[R] ExceptionalRing I z hz s :=
  (reduction I z hz s).comp (mapAlg I z hz s)
instance exceptionalAlgebra (s : Finset (Fin (n+1))) :
    Algebra (ProjectiveRoot.Ring R n s) (ExceptionalRing I z hz s) :=
  (exceptionalProjectiveMap I z hz s).toRingHom.toAlgebra
private local instance exceptionalPSmul (s : Finset (Fin (n+1))) :
    SMul (ProjectiveRoot.Ring R n s) (ExceptionalRing I z hz s) :=
  ⟨fun a b => exceptionalProjectiveMap I z hz s a*b⟩
private local instance exceptionalPModule (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (ExceptionalRing I z hz s) := (exceptionalAlgebra I z hz s).toModule
private local instance reesPModule (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
instance exceptionalTower (s : Finset (Fin (n+1))) :
    IsScalarTower R (ProjectiveRoot.Ring R n s) (ExceptionalRing I z hz s) :=
  IsScalarTower.of_algebraMap_eq' (exceptionalProjectiveMap I z hz s).comp_algebraMap.symm

 

def coefficientReductionLinear (s : Finset (Fin (n+1))) :
    ProjectiveRoot.Ring R n s →ₗ[ProjectiveRoot.Ring R n s] CoefficientRing I s :=
  Algebra.linearMap _ _

def reductionLinear (s : Finset (Fin (n+1))) :
    Ring I z hz s →ₗ[ProjectiveRoot.Ring R n s] ExceptionalRing I z hz s where
  toFun := reduction I z hz s
  map_add' := map_add _
  map_smul' a b := by
    change reduction I z hz s (map I z hz s a * b) =
      reduction I z hz s (map I z hz s a) * reduction I z hz s b
    exact map_mul _ _ _

def coefficientComparisonLinear (s : Finset (Fin (n+1))) :
    CoefficientRing I s →ₗ[ProjectiveRoot.Ring R n s] ExceptionalRing I z hz s where
  toFun := coefficientComparison I z hz hgen s
  map_add' := map_add _
  map_smul' a b := by
    obtain ⟨c,rfl⟩ := coefficientReduction_surjective I s b
    change coefficientComparison I z hz hgen s (coefficientReduction I s a * coefficientReduction I s c)=
      reduction I z hz s (map I z hz s a) * coefficientComparison I z hz hgen s (coefficientReduction I s c)
    rw [←coefficientReduction_mul,←local_square,←local_square,map_mul,map_mul]

lemma coefficientReductionLinear_surjective (s : Finset (Fin (n+1))) :
    Function.Surjective (coefficientReductionLinear I s) := coefficientReduction_surjective I s
lemma reductionLinear_surjective (s : Finset (Fin (n+1))) :
    Function.Surjective (reductionLinear I z hz s) := reduction_surjective I z hz s
lemma coefficientComparisonLinear_surjective (s : Finset (Fin (n+1))) :
    Function.Surjective (coefficientComparisonLinear I z hz hgen s) := coefficientComparison_surjective I z hz hgen s

lemma coefficientReductionLinear_kernel (s : Finset (Fin (n+1))) :
    ((coefficientReductionLinear I s).restrictScalars R).ker =
      I • (⊤ : Submodule R (ProjectiveRoot.Ring R n s)) := by
  change (coefficientReduction I s).ker=_
  exact CoefficientReduction.chartMap_kernel I (n+1) (ProjectiveRoot.product_homogeneous R n s)

lemma reductionLinear_kernel (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    ((reductionLinear I z hz s).restrictScalars R).ker = I • (⊤ : Submodule R (Ring I z hz s)) :=
  reduction_kernel I z hz s hs

lemma coefficient_torsion (s : Finset (Fin (n+1))) :
    powerTorsion I (ModuleCat.of R (CoefficientRing I s)) := by
  refine ⟨1,?_⟩
  rw [pow_one]
  intro r hr
  rw [Module.mem_annihilator]
  exact CoefficientReduction.target_scalar_zero I (n+1) r hr

private local instance reesScalarComm (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _
private local instance sectionGroup (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
private local instance sectionModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule

abbrev RootFibreSections (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :=
  ProjectiveRoot.Sections R n s hs m ⧸ (I • (⊤ : Submodule R (ProjectiveRoot.Sections R n s hs m)))

 

def rootFibreMap (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    RootFibreSections I s hs m →ₗ[R] ExceptionalSections I z hz s hs m :=
  TensorIdeal.fibreMap I (A:=ProjectiveRoot.Ring R n s) (B:=Ring I z hz s)
    (ProjectiveRoot.Sections R n s hs m)

lemma fibre_unit_square (s : Finset (Fin (n+1))) :
    reductionLinear I z hz s 1 = coefficientComparisonLinear I z hz hgen s
      (coefficientReductionLinear I s 1) := by
  change reduction I z hz s 1 = coefficientComparison I z hz hgen s (coefficientReduction I s 1)
  rw [←local_square]
  simp only [map_one]

include hgen in
lemma rootFibreMap_surjective (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Function.Surjective (rootFibreMap I z hz s hs m) :=
  TensorIdeal.fibreMap_surjective I (coefficientReductionLinear I s) (reductionLinear I z hz s)
    (coefficientComparisonLinear I z hz hgen s) (coefficientReductionLinear_surjective I s)
    (reductionLinear_surjective I z hz s) (coefficientReductionLinear_kernel I s)
    (reductionLinear_kernel I z hz s hs) (fibre_unit_square I z hz hgen s)
    (ProjectiveRoot.Sections R n s hs m) (coefficientComparisonLinear_surjective I z hz hgen s)

lemma coefficientComparisonLinear_kernel_zero (ell : TorsionLength I) (hds : ell.DirectSumZero)
    (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ,0<a → ell.value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
        a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
    (s : Finset (Fin (n+1))) :
    ell.value (ModuleCat.of R (coefficientComparisonLinear I z hz hgen s).ker)=0 := by
  change ell.value (ModuleCat.of R (coefficientComparison I z hz hgen s).ker)=0
  exact coefficientComparison_kernel_zero I z hz hgen ell hds hmu ha s

include hgen in
lemma rootFibreMap_kernel_zero (ell : TorsionLength I) (hds : ell.DirectSumZero)
    (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ,0<a → ell.value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
        a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
    (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    ell.value (ModuleCat.of R (rootFibreMap I z hz s hs m).ker)=0 := by
  apply TensorIdeal.fibreMap_kernel_zero I (coefficientReductionLinear I s)
    (reductionLinear I z hz s) (coefficientComparisonLinear I z hz hgen s)
    (coefficientReductionLinear_surjective I s) (reductionLinear_surjective I z hz s)
    (coefficientReductionLinear_kernel I s) (reductionLinear_kernel I z hz s hs)
    (fibre_unit_square I z hz hgen s) (ProjectiveRoot.Sections R n s hs m) ell hds
  · exact coefficientComparisonLinear_surjective I z hz hgen s
  · exact coefficient_torsion I s
  · exact coefficientComparisonLinear_kernel_zero I z hz hgen ell hds hmu ha s

end Lech.ReesRoot

end

end OAI
