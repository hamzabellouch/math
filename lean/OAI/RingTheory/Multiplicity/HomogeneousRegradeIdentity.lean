import Mathlib
import OAI.RingTheory.Multiplicity.RootChartAtlasGlobalCoefficient

namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.HomogeneousRegrade
open HomogeneousLocalization Graded
universe u v w t
variable {ι : Type t} [AddCommMonoid ι] [DecidableEq ι]
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
  {τ : Type w} [SetLike τ A] [AddSubgroupClass τ A]
variable (G : ι → σ) (H : ι → τ) [GradedRing G] [GradedRing H]
variable (h : ∀ i : ι, (G i : Set A)=(H i : Set A)) (U : Submonoid A)
def identity : G →+*ᵍ H where
  toRingHom := RingHom.id A
  map_mem {i} {a} ha := by change a ∈ (H i : Set A); rw [←h i];exact ha
def map : HomogeneousLocalization G U →+* HomogeneousLocalization H U :=
  HomogeneousLocalization.map (identity G H h) (by intro x hx;exact hx)
lemma map_val (x : HomogeneousLocalization G U) : (map G H h U x).val=x.val := by
  obtain ⟨c,rfl⟩ := x.mk_surjective
  rfl
 

def equiv : HomogeneousLocalization G U ≃+* HomogeneousLocalization H U where
  __ := map G H h U
  invFun := map H G (fun i => (h i).symm) U
  left_inv x := by
    apply HomogeneousLocalization.val_injective U
    change (map H G (fun i => (h i).symm) U (map G H h U x)).val=x.val
    rw [map_val,map_val]
  right_inv x := by
    apply HomogeneousLocalization.val_injective U
    change (map G H h U (map H G (fun i => (h i).symm) U x)).val=x.val
    rw [map_val,map_val]
lemma equiv_val (x : HomogeneousLocalization G U) : (equiv G H h U x).val=x.val :=
  map_val G H h U x
end Lech.HomogeneousRegrade

namespace Lech.ExceptionalCoefficientChart
open MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (k : Fin (n+1))
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
abbrev Coefficient := UniversalCoefficientChart.Ring (R ⧸ I) n k
abbrev Projective := ProjectiveCoefficientChart.Chart (R ⧸ I) n k
abbrev Source := Away (SourceGraded.sourceGrade I (n+1)) (X k)
local instance projectiveR : Algebra R (Projective I n k) :=
  Algebra.compHom _ (Ideal.Quotient.mk I)
local instance projectiveTower : IsScalarTower R (R ⧸ I) (Projective I n k) :=
  IsScalarTower.of_algebraMap_eq (R:=R) (S:=R ⧸ I) (A:=Projective I n k) fun _ => rfl
def regrade : Projective I n k ≃+* Source I n k :=
  HomogeneousRegrade.equiv (ProjectiveCoefficientChart.grading (R ⧸ I) n)
    (SourceGraded.sourceGrade I (n+1)) (fun _ => rfl) (Submonoid.powers (X k))
lemma regrade_val (x : Projective I n k) : (regrade I n k x).val=x.val :=
  HomogeneousRegrade.equiv_val _ _ _ _ x
def regradeAlg : Projective I n k ≃ₐ[R] Source I n k where
  __ := regrade I n k
  commutes' r := by
    apply HomogeneousLocalization.val_injective (Submonoid.powers (X k))
    change (regrade I n k (algebraMap R (Projective I n k) r)).val=_
    rw [regrade_val]
    change (algebraMap (R ⧸ I) (Projective I n k) (Ideal.Quotient.mk I r)).val=_
    rw [Homogeneous.val_algebraMap,Homogeneous.val_algebraMap]
    exact (IsScalarTower.algebraMap_apply R (R ⧸ I)
      (Localization (Submonoid.powers (X (R:=R ⧸ I) k))) r).symm
 

def sourceEquiv : Coefficient I n k ≃ₐ[R] Source I n k :=
  ((ProjectiveCoefficientChart.equiv (R ⧸ I) n k).restrictScalars R).trans
    (regradeAlg I n k)
variable (z : Fin (n+1) → R) (hz : Ideal.span (Set.range z)=I)
 

def map : Coefficient I n k →ₗ[R]
    Away (SourceGraded.targetGrade I) (SourceGraded.mapR I z hz (X k)) :=
  (SourceGraded.chartMapR I z hz (X k)).comp (sourceEquiv I n k).toLinearMap
lemma map_surjective : Function.Surjective (map I n k z hz) :=
  (SourceGraded.chart_surjective I z hz (by simpa using isHomogeneous_X (R ⧸ I) k)).comp
    (sourceEquiv I n k).surjective
local instance mapKernelAdd : AddCommGroup (map I n k z hz).ker :=
  Submodule.addCommGroup (R:=R) (M:=Coefficient I n k) (map I n k z hz).ker
local instance sourceKernelAdd : AddCommGroup (SourceGraded.chartMapR I z hz (X k)).ker :=
  Submodule.addCommGroup (R:=R) (M:=Source I n k) (SourceGraded.chartMapR I z hz (X k)).ker
def kernelEquiv : (map I n k z hz).ker ≃ₗ[R]
    (SourceGraded.chartMapR I z hz (X k)).ker where
  toFun x := ⟨sourceEquiv I n k x.val,x.property⟩
  invFun y := ⟨(sourceEquiv I n k).symm y.val,by
    change SourceGraded.chartMapR I z hz (X k)
      (sourceEquiv I n k ((sourceEquiv I n k).symm y.val))=0
    rw [AlgEquiv.apply_symm_apply];exact y.property⟩
  left_inv x := by apply Subtype.ext;exact (sourceEquiv I n k).symm_apply_apply x.val
  right_inv y := by apply Subtype.ext;exact (sourceEquiv I n k).apply_symm_apply y.val
  map_add' x y := by apply Subtype.ext;exact (sourceEquiv I n k).map_add x.val y.val
  map_smul' r x := by apply Subtype.ext;exact (sourceEquiv I n k).toLinearEquiv.map_smul r x.val
variable (ell : AllModuleLength R)
 

theorem map_kernel_zero
    (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ,0<a → ell.value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
      a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I))) :
    ell.value (ModuleCat.of R (map I n k z hz).ker)=0 := by
  rw [ell.value_eq_of_linearEquiv (kernelEquiv I n k z hz)]
  exact SourceGraded.chart_kernel_zero I z hz ell (by omega) hmu ha
    (by simpa using isHomogeneous_X (R ⧸ I) k)
end Lech.ExceptionalCoefficientChart


namespace Lech.AllModuleLength
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {C A M N V : Type u} [CommRing C] [CommRing A] [Algebra C A]
  [AddCommGroup M] [Module A M] [Module C M] [IsScalarTower C A M]
  [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower C A N]
  [AddCommGroup V] [Module A V] [Module C V] [IsScalarTower C A V]
  (ell : AllModuleLength C)
omit [Module C N] [IsScalarTower C A N] in
 

lemma tensor_map_kernel_zero (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hker : ell.value (ModuleCat.of C f.ker)=0) :
    ell.value (ModuleCat.of C (f.lTensor V).ker)=0 := by
  let k := f.ker.subtype.lTensor V
  have he := _root_.lTensor_exact V f.exact_subtype_ker_map hf
  let q : V ⊗[A] f.ker →ₗ[C] (f.lTensor V).ker :=
    (k.restrictScalars C).codRestrict ((f.lTensor V).ker.restrictScalars C) (fun x => by
      change (f.lTensor V) (k x) = 0
      exact he.apply_apply_eq_zero x)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨v,hv⟩ := he x.val |>.mp x.property
    exact ⟨v,Subtype.ext hv⟩
  exact ell.zero_of_surjective q hq (ell.tensor_zero_right hker)
end Lech.AllModuleLength


namespace Lech.ExceptionalCoefficientChart
open MvPolynomial HomogeneousLocalization
open scoped TensorProduct
attribute [local instance] Homogeneous.awayAddCommGroup
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (k : Fin (n+1))
variable (z : Fin (n+1) → R) (hz : Ideal.span (Set.range z)=I)
 

def gradedHom : SourceGraded.sourceGrade I (n+1) →+*ᵍ SourceGraded.targetGrade I :=
  SourceGraded.mapR I z hz
abbrev Target := Away (SourceGraded.targetGrade I) (gradedHom I n z hz (X k))
local instance targetRing : CommRing (Target I n k z hz) :=
  HomogeneousLocalization.homogeneousLocalizationCommRing
local instance targetModule : Module R (Target I n k z hz) :=
  Homogeneous.module (SourceGraded.targetGrade I) (Submonoid.powers (gradedHom I n z hz (X k)))
local instance targetR : Algebra R (Target I n k z hz) :=
  Homogeneous.algebra (SourceGraded.targetGrade I) (Submonoid.powers (gradedHom I n z hz (X k)))
def homogeneousMap :=
  Away.map (A:=MvPolynomial (Fin (n+1)) (R ⧸ I)) (B:=IdealGraded.Ring I)
    (ι:=ℕ) (σ:=Submodule R (MvPolynomial (Fin (n+1)) (R ⧸ I)))
    (τ:=Submodule R (IdealGraded.Ring I))
    (𝒜:=SourceGraded.sourceGrade I (n+1)) (ℬ:=SourceGraded.targetGrade I)
    (gradedHom I n z hz) (X (R:=R ⧸ I) k)
def coefficientToSource : Coefficient I n k →+* Source I n k := (sourceEquiv I n k).toRingHom
def ringMap :=
  (homogeneousMap I n k z hz).comp (coefficientToSource I n k)
lemma ringMap_apply (a : Coefficient I n k) : ringMap I n k z hz a=map I n k z hz a := rfl
def algebraHom : Coefficient I n k →ₐ[R] Target I n k z hz where
  __ := ringMap I n k z hz
  commutes' r := by
    change map I n k z hz (algebraMap R (Coefficient I n k) r)=_
    rw [Algebra.algebraMap_eq_smul_one]
    exact ((map I n k z hz).map_smul r 1).trans (by
      change r • ringMap I n k z hz 1=algebraMap R (Target I n k z hz) r
      rw [_root_.map_one,Algebra.algebraMap_eq_smul_one])
instance targetAlgebra : Algebra (Coefficient I n k) (Target I n k z hz) :=
  (ringMap I n k z hz).toAlgebra
local instance targetCoefficientModule : Module (Coefficient I n k) (Target I n k z hz) :=
  (targetAlgebra I n k z hz).toModule
instance targetTower :
    @IsScalarTower R (Coefficient I n k) (Target I n k z hz)
      inferInstance (targetAlgebra I n k z hz).toSMul (targetR I n k z hz).toSMul :=
  @IsScalarTower.of_algebraMap_eq R (Coefficient I n k) (Target I n k z hz) _ _ _ _ (targetAlgebra I n k z hz) (targetR I n k z hz)
    (fun r => ((algebraHom I n k z hz).commutes r).symm)
def algebraLinear : Coefficient I n k →ₗ[Coefficient I n k] Target I n k z hz :=
  Algebra.linearMap _ _
lemma algebraLinear_apply (a : Coefficient I n k) :
    algebraLinear I n k z hz a=map I n k z hz a := rfl
lemma algebraLinear_surjective : Function.Surjective (algebraLinear I n k z hz) :=
  map_surjective I n k z hz
def linearKernelEquiv : (algebraLinear I n k z hz).ker ≃ₗ[R] (map I n k z hz).ker where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable (ell : AllModuleLength R)
variable (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
variable (ha : ∀ a : ℕ,0<a → ell.value
    (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
    a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
include hmu ha in
lemma algebraLinear_kernel_zero :
    ell.value (ModuleCat.of R (algebraLinear I n k z hz).ker)=0 := by
  rw [ell.value_eq_of_linearEquiv (linearKernelEquiv I n k z hz)]
  exact map_kernel_zero I n k z hz ell hmu ha
variable (V : Type u) [AddCommGroup V] [Module (Coefficient I n k) V]
  [Module R V] [IsScalarTower R (Coefficient I n k) V]
include hmu ha in
 

theorem tensor_kernel_zero :
    ell.value (ModuleCat.of R ((algebraLinear I n k z hz).lTensor V).ker)=0 :=
  ell.tensor_map_kernel_zero (algebraLinear I n k z hz)
    (algebraLinear_surjective I n k z hz)
    (algebraLinear_kernel_zero I n k z hz ell hmu ha)
omit [Module R V] [IsScalarTower R (Coefficient I n k) V] in
theorem tensor_surjective :
    Function.Surjective ((algebraLinear I n k z hz).lTensor V) :=
  LinearMap.lTensor_surjective V (algebraLinear_surjective I n k z hz)
end Lech.ExceptionalCoefficientChart


namespace Lech.AllModuleLength
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {C A M N V : Type u} [CommRing C] [CommRing A] [Algebra C A]
  [AddCommGroup M] [Module A M] [Module C M] [IsScalarTower C A M]
  [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower C A N]
  [AddCommGroup V] [Module A V] [Module C V] [IsScalarTower C A V]
  (ell : AllModuleLength C)
omit [Module C N] [IsScalarTower C A N] in
 

lemma tensor_right_map_kernel_zero (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hker : ell.value (ModuleCat.of C f.ker)=0) :
    ell.value (ModuleCat.of C (f.rTensor V).ker)=0 := by
  let k := f.ker.subtype.rTensor V
  have he := _root_.rTensor_exact V f.exact_subtype_ker_map hf
  let q : f.ker ⊗[A] V →ₗ[C] (f.rTensor V).ker :=
    (k.restrictScalars C).codRestrict ((f.rTensor V).ker.restrictScalars C) (fun x => by
      change (f.rTensor V) (k x) = 0
      exact he.apply_apply_eq_zero x)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨v,hv⟩ := he x.val |>.mp x.property
    exact ⟨v,Subtype.ext hv⟩
  exact ell.zero_of_surjective q hq (ell.tensor_zero_left hker)
end Lech.AllModuleLength


namespace Lech.ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable (B : Type u) [CommRing B] [Algebra (UniversalCoefficientChart.Ring R n k) B]
 

theorem sectionModule_baseChange_properties (m : Fin n → ℤ) :
    Module.FinitePresentation B (B ⊗[UniversalCoefficientChart.Ring R n k] sectionModule R n k m) ∧
    Module.Projective B (B ⊗[UniversalCoefficientChart.Ring R n k] sectionModule R n k m) ∧
    ∀ p : PrimeSpectrum B,
      Module.rankAtStalk (B ⊗[UniversalCoefficientChart.Ring R n k] sectionModule R n k m) p=n.factorial := by
  let h := sectionModule_properties R n k m
  let := h.1
  let := h.2.1
  refine ⟨inferInstance,inferInstance,fun p => ?_⟩
  rw [Module.rankAtStalk_baseChange]
  exact h.2.2 _
end Lech.ProductSourceCover


namespace Lech.ExceptionalCoefficientChart
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (k : Fin (n+1))
variable (z : Fin (n+1) → R) (hz : Ideal.span (Set.range z)=I)
local instance exceptionalRing : CommRing (Target I n k z hz) := targetRing I n k z hz
local instance exceptionalA : Algebra (Coefficient I n k) (Target I n k z hz) := targetAlgebra I n k z hz
local instance exceptionalModule : Module (Coefficient I n k) (Target I n k z hz) := (exceptionalA I n k z hz).toModule
local instance exceptionalR : Algebra R (Target I n k z hz) := targetR I n k z hz
variable (m : Fin n → ℤ)
abbrev Root := ProductSourceCover.sectionModule (R ⧸ I) n k m
local instance rootAdd : AddCommGroup (Root I n k m) := Submodule.addCommGroup _
local instance rootAModule : Module (Coefficient I n k) (Root I n k m) := Submodule.module _
local instance rootRModule : Module R (Root I n k m) :=
  Module.compHom (Root I n k m) (algebraMap R (Coefficient I n k))
local instance rootTower :
    @IsScalarTower R (Coefficient I n k) (Root I n k m) inferInstance
      (rootAModule I n k m).toSMul (rootRModule I n k m).toSMul :=
  IsScalarTower.of_compHom R (Coefficient I n k) (Root I n k m)
 
abbrev ExceptionalRoot := Target I n k z hz ⊗[Coefficient I n k] Root I n k m
 
def rootComparison : Root I n k m →ₗ[Coefficient I n k] ExceptionalRoot I n k z hz m :=
  ((algebraLinear I n k z hz).rTensor (Root I n k m)).comp
    (TensorProduct.lid (Coefficient I n k) (Root I n k m)).symm.toLinearMap
lemma rootComparison_apply (x : Root I n k m) :
    rootComparison I n k z hz m x=1 ⊗ₜ[Coefficient I n k] x := by
  simp [rootComparison,LinearMap.rTensor_tmul,algebraLinear]
lemma rootComparison_surjective : Function.Surjective (rootComparison I n k z hz m) :=
  (LinearMap.rTensor_surjective _ (algebraLinear_surjective I n k z hz)).comp
    (TensorProduct.lid (Coefficient I n k) (Root I n k m)).symm.surjective
 

theorem exceptionalRoot_properties :
    Module.FinitePresentation (Target I n k z hz) (ExceptionalRoot I n k z hz m) ∧
    Module.Projective (Target I n k z hz) (ExceptionalRoot I n k z hz m) ∧
    ∀ p : PrimeSpectrum (Target I n k z hz),
      Module.rankAtStalk (ExceptionalRoot I n k z hz m) p=n.factorial :=
  ProductSourceCover.sectionModule_baseChange_properties (R ⧸ I) n k (Target I n k z hz) m
local instance rootTensorAdd : AddCommGroup (Coefficient I n k ⊗[Coefficient I n k] Root I n k m) := TensorProduct.addCommGroup
local instance rootKernelAdd : AddCommGroup (rootComparison I n k z hz m).ker := Submodule.addCommGroup _
local instance tensorKernelAdd : AddCommGroup ((algebraLinear I n k z hz).rTensor (Root I n k m)).ker := Submodule.addCommGroup _
local instance rootTensorR : Module R (Coefficient I n k ⊗[Coefficient I n k] Root I n k m) := TensorProduct.leftModule
local instance rootKernelR : Module R (rootComparison I n k z hz m).ker := Submodule.module' _
def rootKernelEquiv : (rootComparison I n k z hz m).ker ≃ₗ[R]
    ((algebraLinear I n k z hz).rTensor (Root I n k m)).ker where
  toFun x := ⟨(TensorProduct.lid (Coefficient I n k) (Root I n k m)).symm x.val,x.property⟩
  invFun y := ⟨TensorProduct.lid (Coefficient I n k) (Root I n k m) y.val,by
    change (algebraLinear I n k z hz).rTensor (Root I n k m)
      ((TensorProduct.lid (Coefficient I n k) (Root I n k m)).symm
        (TensorProduct.lid (Coefficient I n k) (Root I n k m) y.val))=0
    rw [LinearEquiv.symm_apply_apply];exact y.property⟩
  left_inv x := by apply Subtype.ext;exact (TensorProduct.lid (Coefficient I n k) (Root I n k m)).apply_symm_apply x.val
  right_inv y := by apply Subtype.ext;exact (TensorProduct.lid (Coefficient I n k) (Root I n k m)).symm_apply_apply y.val
  map_add' x y := by apply Subtype.ext;exact (TensorProduct.lid (Coefficient I n k) (Root I n k m)).symm.map_add x.val y.val
  map_smul' r x := by
    apply Subtype.ext
    exact ((TensorProduct.lid (Coefficient I n k) (Root I n k m)).symm.restrictScalars R).map_smul r x.val
variable (ell : AllModuleLength R)
 

theorem rootComparison_kernel_zero
    (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ,0<a → ell.value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
      a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I))) :
    ell.value (ModuleCat.of R (rootComparison I n k z hz m).ker)=0 := by
  rw [ell.value_eq_of_linearEquiv (rootKernelEquiv I n k z hz m)]
  exact ell.tensor_right_map_kernel_zero (algebraLinear I n k z hz)
    (algebraLinear_surjective I n k z hz)
    (algebraLinear_kernel_zero I n k z hz ell hmu ha)
end Lech.ExceptionalCoefficientChart


namespace Lech.ExceptionalCoefficientChart
open MvPolynomial HomogeneousLocalization Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (k : Fin (n+1))
variable (z : Fin (n+1) → R) (hz : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
variable {d : ℕ} (g : MvPolynomial (Fin (n+1)) (R ⧸ I))
variable (hg : g∈SourceGraded.sourceGrade I (n+1) d)
lemma sourceEquiv_evaluate :
    sourceEquiv I n k (ProjectiveCoefficientChart.evaluate (R ⧸ I) n k g)=
    Away.isLocalizationElem (show X k∈SourceGraded.sourceGrade I (n+1) 1 from
      isHomogeneous_X (R ⧸ I) k) hg := by
  change regrade I n k (ProjectiveCoefficientChart.equiv (R ⧸ I) n k
    (ProjectiveCoefficientChart.evaluate (R ⧸ I) n k g))=_
  rw [ProjectiveCoefficientChart.equiv_evaluate_localizationElem (R ⧸ I) n k g hg]
  apply HomogeneousLocalization.val_injective
  rw [regrade_val]
  rfl
lemma ringMap_evaluate :
    ringMap I n k z hz (ProjectiveCoefficientChart.evaluate (R ⧸ I) n k g)=
    Away.isLocalizationElem (map_mem (gradedHom I n z hz)
      (show X k∈SourceGraded.sourceGrade I (n+1) 1 from isHomogeneous_X (R ⧸ I) k))
      (map_mem (gradedHom I n z hz) hg) := by
  change homogeneousMap I n k z hz
    (sourceEquiv I n k (ProjectiveCoefficientChart.evaluate (R ⧸ I) n k g))=_
  rw [sourceEquiv_evaluate I n k g hg]
  dsimp only [homogeneousMap,Away.isLocalizationElem]
  rw [Away.map_mk]
  simp only [map_pow]
abbrev ActualOverlap := Away (SourceGraded.targetGrade I)
  (gradedHom I n z hz (X k)*gradedHom I n z hz g)
def actualOverlapMap : Target I n k z hz →+* ActualOverlap I n k z hz g :=
  HomogeneousLocalization.awayMap (SourceGraded.targetGrade I)
    (map_mem (gradedHom I n z hz) hg) rfl
@[instance_reducible] def actualOverlapAlgebra :
    Algebra (Target I n k z hz) (ActualOverlap I n k z hz g) :=
  (actualOverlapMap I n k z hz g hg).toAlgebra
 

lemma actualOverlap_isLocalization :
    let := actualOverlapAlgebra I n k z hz g hg
    IsLocalization.Away
      (ringMap I n k z hz (ProjectiveCoefficientChart.evaluate (R ⧸ I) n k g))
      (ActualOverlap I n k z hz g) := by
  let := actualOverlapAlgebra I n k z hz g hg
  rw [ringMap_evaluate I n k z hz g hg]
  exact Away.isLocalization_mul
    (map_mem (gradedHom I n z hz)
      (show X k∈SourceGraded.sourceGrade I (n+1) 1 from isHomogeneous_X (R ⧸ I) k))
    (map_mem (gradedHom I n z hz) hg) rfl (by decide)
end Lech.ExceptionalCoefficientChart
end
end

end OAI
