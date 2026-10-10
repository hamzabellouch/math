import Mathlib
import OAI.RingTheory.Multiplicity.GradedLineBasisHasBasis

namespace OAI

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
namespace Lech
lemma signedUnitProduct {G : Type*} [CommGroup G] {ι : Type*} [Fintype ι]
    (a b : ι → G) (m : ι → ℤ) :
    (∏ i,a i^m i)*(∏i,b i^m i)⁻¹=∏i,(a i*(b i)⁻¹)^m i := by
  simp only [mul_zpow,inv_zpow,Finset.prod_mul_distrib,Finset.prod_inv_distrib]
end Lech


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance signedWorkAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance signedWorkTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Module.FaithfullyFlat A B]
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
lemma chartTransition_unit_value (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    Units.map (algebraMap C (commonExtension f n hn t v hv d C)).toMonoidHom
      (chartTransition f n hn t v hv d C σ τ φ ψ ms)=
        commonWeight f n hn t v hv d C σ φ ms*(commonWeight f n hn t v hv d C τ ψ ms)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Units.ext
  exact chartTransition_value f n hn t v hv d C σ τ φ ψ ms
omit [Module.FaithfullyFlat A B] in
lemma commonWeight_product (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    commonWeight f n hn t v hv d C σ φ ms=
      ∏ i : Fin n,commonWeight f n hn t v hv d C σ φ (Pi.single i (1:ℤ))^ms i := by
  let : CommRing (chartExtension f n hn t v hv d σ) := Algebra.TensorProduct.instCommRing
  simp only [commonWeight]
  simp only [chartWeight_single]
  rw [chartWeight,map_prod]
  simp only [map_zpow]
 

lemma chartTransition_product (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    chartTransition f n hn t v hv d C σ τ φ ψ ms=
      ∏ i : Fin n,chartTransition f n hn t v hv d C σ τ φ ψ (Pi.single i (1:ℤ))^ms i := by
  let := algebra_faithfullyFlat f n hn t v hv d
  apply Units.map_injective (FaithfulSMul.algebraMap_injective C (commonExtension f n hn t v hv d C))
  simp only [map_prod,map_zpow,chartTransition_unit_value]
  rw [commonWeight_product f n hn t v hv d C σ φ ms,
    commonWeight_product f n hn t v hv d C τ ψ ms]
  exact signedUnitProduct _ _ _
 

def coordinateTransition (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (i : Fin n) : Cˣ :=
  chartTransition f n hn t v hv d C σ τ φ ψ (Pi.single i (1:ℤ))
lemma coordinateTransition_val (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (i : Fin n) :
    (coordinateTransition f n hn t v hv d C σ τ φ ψ i:C)=
      ψ (chartCoordinate f n hn t v hv d τ i (σ i)) :=
  chartTransition_single f n hn t v hv d C σ τ φ ψ i
end Lech.RootInvariants


namespace Lech.LineBasisExtension
open scoped TensorProduct
universe u v w x
variable {R : Type u} [CommRing R] {L : Type v} [CommRing L] [Algebra R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable (C : Type x) [CommRing C] [Algebra R C] [Algebra L C] [IsScalarTower R L C]
def included : L ⊗[R] M →ₗ[R] C ⊗[R] M :=
  TensorProduct.map (IsScalarTower.toAlgHom R L C).toLinearMap (LinearMap.id : M →ₗ[R] M)
lemma included_tmul (l : L) (m : M) : included C (l ⊗ₜ[R] m)=algebraMap L C l ⊗ₜ[R] m := rfl
lemma included_smul (l : L) (z : L ⊗[R] M) :
    included C (l • z)=algebraMap L C l • included C z := by
  induction z using TensorProduct.inductionOn with
  | tmul a m => simp only [TensorProduct.smul_tmul',smul_eq_mul,included_tmul,map_mul]
  | add z w hz hw => simp only [smul_add,map_add,hz,hw]
lemma extend_one (e : L ≃ₗ[L] L ⊗[R] M) : extend C e 1=included C (e 1) := by
  change TensorProduct.AlgebraTensorModule.cancelBaseChange R L C C M (1 ⊗ₜ[L] e 1)=_
  generalize e 1=z
  induction z using TensorProduct.inductionOn with
  | tmul l m =>
    simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,included_tmul,Algebra.smul_def,mul_one]
  | add z w hz hw => simp only [TensorProduct.tmul_add,map_add,hz,hw]
 

lemma extend_coefficient (e : L ≃ₗ[L] L ⊗[R] M) (l : L) :
    extend C e (algebraMap L C l)=included C (e l) := by
  conv_rhs => rw [show l=l • (1:L) by simp]
  rw [e.map_smul,included_smul,←extend_one,←(extend C e).map_smul]
  simp
lemma coefficients_in_basis (e : L ≃ₗ[L] L ⊗[R] M) (z : L ⊗[R] M) :
    (extend C e).symm (included C z)=algebraMap L C (e.symm z) := by
  apply (extend C e).injective
  rw [(extend C e).apply_symm_apply,extend_coefficient,e.apply_symm_apply]
def coordinates (e : C ≃ₗ[C] C ⊗[R] M) : C ⊗[R] M →ₗ[R] C :=
  e.symm.toLinearMap.restrictScalars R
lemma coordinates_apply (e : C ≃ₗ[C] C ⊗[R] M) (z : C ⊗[R] M) : coordinates C e z=e.symm z := rfl
end Lech.LineBasisExtension


namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
local instance gridAlgebraWork : Algebra (A R n k) d.S := Algebra.compHom d.S (algebraMap (A R n k) B)
local instance gridAlgebraTower : IsScalarTower (A R n k) B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Module.FaithfullyFlat (A R n k) B]
instance gridRootAlgebra : Algebra (D R n k t v hv d) (GridAmbient R n) :=
  (algebraPoint R n k t v hv d (fun _ => false)).toRingHom.toAlgebra
lemma gridRootAlgebraMap (x : D R n k t v hv d) :
    algebraMap (D R n k t v hv d) (GridAmbient R n) x=algebraPoint R n k t v hv d (fun _ => false) x := rfl
lemma chartToGrid_from (σ : Chart n) (x : D R n k t v hv d) :
    chartToGrid R n k t v hv d σ (algebraMap (D R n k t v hv d) (L R n k t v hv d σ) x)=
      algebraMap (D R n k t v hv d) (GridAmbient R n) x := by
  change algebraPoint R n k t v hv d σ x=algebraPoint R n k t v hv d (fun _ => false) x
  rw [algebraPoint_independent]
def chartToGridD (σ : Chart n) : L R n k t v hv d σ →ₐ[D R n k t v hv d] GridAmbient R n :=
  { (chartToGrid R n k t v hv d σ).toRingHom with commutes' := chartToGrid_from R n k t v hv d σ }
lemma chartToGridD_apply (σ : Chart n) (x : L R n k t v hv d σ) :
    chartToGridD R n k t v hv d σ x=chartToGrid R n k t v hv d σ x := rfl
lemma chartToGrid_injective (σ : Chart n) : Function.Injective (chartToGrid R n k t v hv d σ) :=
  (localizedChart_injective R n σ k).comp (equiv R n k t v hv d σ).injective
lemma gridRootAlgebra_injective : Function.Injective (algebraMap (D R n k t v hv d) (GridAmbient R n)) := by
  have h : Function.Injective (algebraMap (D R n k t v hv d) (L R n k t v hv d (fun _ => false))) :=
    IsLocalization.injective (L R n k t v hv d (fun _ => false))
      (Submonoid.powers_le.mpr ((chartFunction_regular R n k t v hv d (fun _ => false)).mem_nonZeroDivisors))
  exact (chartToGrid_injective R n k t v hv d (fun _ => false)).comp h

def gridBasis (σ : Chart n) (m : Fin n → ℤ) : GridAmbient R n ≃ₗ[GridAmbient R n]
    (GridAmbient R n ⊗[D R n k t v hv d] RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) :=
  RootInvariants.commonBasis (f R n k) n (hn R n k) t v hv d (GridAmbient R n) σ (chartToGridD R n k t v hv d σ) m
lemma gridCoordinateTransition (σ : Chart n) (i : Fin n) :
    (RootInvariants.coordinateTransition (f R n k) n (hn R n k) t v hv d (GridAmbient R n)
      σ (fun _ => false) (chartToGridD R n k t v hv d σ) (chartToGridD R n k t v hv d (fun _ => false)) i:GridAmbient R n)=
      embed R n (if σ i then (ProductLaurent.variableUnit R n i:Ambient R n) else 1) := by
  rw [RootInvariants.coordinateTransition_val]
  change chartToGrid R n k t v hv d (fun _ => false) (coordinate R n k t v hv d (fun _ => false) i (σ i))=_
  rw [chartToGrid_coordinate]
  cases σ i <;> simp only [Bool.false_eq_true,↓reduceIte,chartScalar,AlgHom.comp_apply,
    ProductLaurent.chartMap_a,ProductLaurent.chartMap_b,Units.val_one,one_mul,map_one]
end Lech.RootChartAtlas


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance basisMapWorkAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance basisMapWorkTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Module.FaithfullyFlat A B]
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
def commonInclusion (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    chartModule f n hn t v hv d σ ms →ₗ[algebra f n hn t v hv d] commonModule f n hn t v hv d C ms :=
  TensorProduct.map φ.toLinearMap (LinearMap.id : overAlgebra f n hn t v hv d ms →ₗ[algebra f n hn t v hv d] _)
lemma commonBasis_from (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ)
    (l : chartRing f n hn t v hv d σ) :
    commonBasis f n hn t v hv d C σ φ ms (φ l)=
      commonInclusion f n hn t v hv d C σ φ ms (chartBasis f n hn t v hv d σ ms l) := by
  let : Algebra (chartRing f n hn t v hv d σ) C := φ.toRingHom.toAlgebra
  let : IsScalarTower (algebra f n hn t v hv d) (chartRing f n hn t v hv d σ) C :=
    IsScalarTower.of_algebraMap_eq (R := algebra f n hn t v hv d)
      (S := chartRing f n hn t v hv d σ) (A := C) fun a => (φ.commutes a).symm
  exact LineBasisExtension.extend_coefficient C (chartBasis f n hn t v hv d σ ms) l
lemma commonInclusion_coordinate (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ)
    (z : chartModule f n hn t v hv d σ ms) :
    (commonBasis f n hn t v hv d C τ ψ ms).symm (commonInclusion f n hn t v hv d C σ φ ms z)=
      φ ((chartBasis f n hn t v hv d σ ms).symm z)*
        (chartTransition f n hn t v hv d C σ τ φ ψ ms:C) := by
  apply (commonBasis f n hn t v hv d C τ ψ ms).injective
  rw [LinearEquiv.apply_symm_apply]
  change _=commonBasis f n hn t v hv d C τ ψ ms
    (_*(LineBasisExtension.transition (commonBasis f n hn t v hv d C τ ψ ms)
      (commonBasis f n hn t v hv d C σ φ ms):C))
  rw [LineBasisExtension.transition_apply,commonBasis_from,LinearEquiv.apply_symm_apply]
end Lech.RootInvariants


namespace Lech.ProductLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def monomialHom : Multiplicative (Exponent n) →* (Ring R n)ˣ where
  toFun e := monomialUnit R n e.toAdd
  map_one' := by apply Units.ext;exact (one_def).symm
  map_mul' := monomialUnit_add R n
lemma monomialUnit_zsmul (e : Exponent n) (m : ℤ) :
    monomialUnit R n (m • e)=(monomialUnit R n e)^m :=
  (monomialHom R n).map_zpow (Multiplicative.ofAdd e) m
lemma monomialUnit_sum {ι : Type*} (s : Finset ι) (e : ι → Exponent n) :
    monomialUnit R n (∑ i∈s,e i)=∏ i∈s,monomialUnit R n (e i) := by
  induction s using Finset.cons_induction with
  | empty => exact (monomialHom R n).map_one
  | cons a s ha ih => rw [Finset.sum_cons,Finset.prod_cons,monomialUnit_add,ih]
lemma signedProduct (m : Fin n → ℤ) (σ : Fin n → Bool) :
    (∏ i,(if σ i then variableUnit R n i else 1)^m i)=
      monomialUnit R n (ProductSourceCover.twistExponent n m σ) := by
  have he : ProductSourceCover.twistExponent n m σ=∑ i : Fin n, (if σ i then m i else 0) • Finsupp.single i 1 := by
    ext j
    simp only [ProductSourceCover.twistExponent_apply,Finset.sum_apply']
    rw [Finset.sum_eq_single j]
    · cases σ j <;> simp
    · intro b _ hb
      cases σ b <;> simp [Finsupp.single_eq_of_ne hb.symm]
    · simp
  rw [he,monomialUnit_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [monomialUnit_zsmul]
  cases σ i <;> simp only [Bool.false_eq_true,↓reduceIte,zpow_zero,one_zpow]
end Lech.ProductLaurent


namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
local instance gridLineWork : Algebra (A R n k) d.S := Algebra.compHom d.S (algebraMap (A R n k) B)
local instance gridLineTower : IsScalarTower (A R n k) B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Module.FaithfullyFlat (A R n k) B]
local instance gridLineRoot : Algebra (D R n k t v hv d) (GridAmbient R n) := gridRootAlgebra R n k t v hv d
local instance gridLineModule (m : Fin n → ℤ) : Module (D R n k t v hv d) (RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) :=
  Submodule.module _
lemma gridTransition (σ : Chart n) (m : Fin n → ℤ) :
    RootInvariants.chartTransition (f R n k) n (hn R n k) t v hv d (GridAmbient R n)
      σ (fun _ => false) (chartToGridD R n k t v hv d σ) (chartToGridD R n k t v hv d (fun _ => false)) m=
      Units.map (embed R n).toMonoidHom (ProductLaurent.monomialUnit R n (twistExponent n m σ)) := by
  rw [RootInvariants.chartTransition_product,←ProductLaurent.signedProduct,map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_zpow]
  congr 1
  apply Units.ext
  change (RootInvariants.coordinateTransition (f R n k) n (hn R n k) t v hv d (GridAmbient R n)
    σ (fun _ => false) (chartToGridD R n k t v hv d σ) (chartToGridD R n k t v hv d (fun _ => false)) i:GridAmbient R n)=_
  rw [gridCoordinateTransition]
  cases σ i <;> rfl

def gridInclusion (σ : Chart n) (m : Fin n → ℤ) :=
  RootInvariants.commonInclusion (f R n k) n (hn R n k) t v hv d (GridAmbient R n) σ (chartToGridD R n k t v hv d σ) m

def gridCoefficient (σ : Chart n) (m : Fin n → ℤ) :
    RootInvariants.chartModule (f R n k) n (hn R n k) t v hv d σ m →ₗ[D R n k t v hv d] GridAmbient R n :=
  (LineBasisExtension.coordinates (GridAmbient R n) (gridBasis R n k t v hv d (fun _ => false) m)).comp
    (gridInclusion R n k t v hv d σ m)
lemma gridCoefficient_apply (σ : Chart n) (m : Fin n → ℤ)
    (z : RootInvariants.chartModule (f R n k) n (hn R n k) t v hv d σ m) :
    gridCoefficient R n k t v hv d σ m z=
      localizedLine R n m σ k (toH R n k t v hv d σ ((RootInvariants.chartBasis (f R n k) n (hn R n k) t v hv d σ m).symm z)) := by
  change (RootInvariants.commonBasis (f R n k) n (hn R n k) t v hv d (GridAmbient R n) (fun _ => false) (chartToGridD R n k t v hv d (fun _ => false)) m).symm
    (RootInvariants.commonInclusion (f R n k) n (hn R n k) t v hv d (GridAmbient R n) σ (chartToGridD R n k t v hv d σ) m z)=_
  rw [RootInvariants.commonInclusion_coordinate,gridTransition,localizedLine_apply]
  change chartToGrid R n k t v hv d σ _ * embed R n (ProductLaurent.monomialUnit R n (twistExponent n m σ):Ambient R n)=_
  rw [mul_comm]
  rfl
 

theorem gridCoefficient_range (σ : Chart n) (m : Fin n → ℤ) (x : GridAmbient R n) :
    (∃ z,gridCoefficient R n k t v hv d σ m z=x) ↔ x∈grid R n m {k} {σ} := by
  rw [←localizedLine_range]
  constructor
  · rintro ⟨z,rfl⟩
    rw [gridCoefficient_apply]
    exact ⟨_,rfl⟩
  · rintro ⟨h,rfl⟩
    obtain ⟨a,ha⟩ := (equiv R n k t v hv d σ).surjective h
    refine ⟨RootInvariants.chartBasis (f R n k) n (hn R n k) t v hv d σ m a,?_⟩
    rw [gridCoefficient_apply,LinearEquiv.symm_apply_apply]
    exact congrArg (localizedLine R n m σ k) ha
end Lech.RootChartAtlas


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance propertiesWorkAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance propertiesWorkTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma line_finitePresentation [Module.FaithfullyFlat A B] (ms : Fin n → ℤ) :
    Module.FinitePresentation (algebra f n hn t v hv d) (overAlgebra f n hn t v hv d ms) := by
  let := algebra_faithfullyFlat f n hn t v hv d
  let : Module.FinitePresentation d.S (d.S ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ms) :=
    Module.FinitePresentation.of_equiv (lineTensorEquiv f n hn t v hv d ms).symm
  exact ModuleDescent.finitePresentation (B := d.S)

lemma line_flat [Module.FaithfullyFlat A B] (ms : Fin n → ℤ) :
    Module.Flat (algebra f n hn t v hv d) (overAlgebra f n hn t v hv d ms) := by
  let := algebra_faithfullyFlat f n hn t v hv d
  let : Module.Flat d.S (d.S ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ms) :=
    Module.Flat.of_linearEquiv (lineTensorEquiv f n hn t v hv d ms)
  exact Module.Flat.of_flat_tensorProduct _ _ d.S

lemma line_projective [Module.FaithfullyFlat A B] (ms : Fin n → ℤ) :
    Module.Projective (algebra f n hn t v hv d) (overAlgebra f n hn t v hv d ms) := by
  let := line_finitePresentation f n hn t v hv d ms
  let := line_flat f n hn t v hv d ms
  exact Module.Flat.projective_of_finitePresentation

lemma line_rankAtStalk [Module.FaithfullyFlat A B] (ms : Fin n → ℤ)
    (p : PrimeSpectrum (algebra f n hn t v hv d)) :
    Module.rankAtStalk (overAlgebra f n hn t v hv d ms) p=1 := by
  let := algebra_faithfullyFlat f n hn t v hv d
  obtain ⟨q,hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := algebra f n hn t v hv d) (B := d.S) p
  let : Nontrivial d.S := q.nontrivial
  let := line_finitePresentation f n hn t v hv d ms
  let := line_flat f n hn t v hv d ms
  have he := congrFun (Module.rankAtStalk_eq_of_equiv (lineTensorEquiv f n hn t v hv d ms)) q
  rw [Module.rankAtStalk_baseChange,hq,Module.rankAtStalk_eq_finrank_of_free (R := d.S) (M := d.S)] at he
  exact he.trans (by simp)
end Lech.RootInvariants


namespace Lech.LocalizationImageCover
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {C : Type w} [CommRing C] [Algebra R C]
variable {ι : Type*} [Fintype ι] (q : ι → R)
def localMap (i : ι) (φ : Localization.Away (q i) →ₐ[R] C) :
    Localization.Away (q i) ⊗[R] M →ₗ[R] C ⊗[R] M :=
  TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[R] M)
omit [Fintype ι] in
lemma localMap_from (i : ι) (φ : Localization.Away (q i) →ₐ[R] C) (m : M) :
    localMap q i φ (1 ⊗ₜ[R] m)=1 ⊗ₜ[R] m := by
  change φ 1 ⊗ₜ[R] m=1 ⊗ₜ[R] m
  rw [map_one]
omit [Fintype ι] in
lemma localMap_clear (i : ι) (φ : Localization.Away (q i) →ₐ[R] C)
    (z : Localization.Away (q i) ⊗[R] M) :
    ∃ N : ℕ,∃ m : M,1 ⊗ₜ[R] m=(q i)^N • localMap q i φ z := by
  obtain ⟨⟨m,s⟩,h⟩ := IsLocalizedModule.surj (Submonoid.powers (q i))
    (TensorProduct.mk R (Localization.Away (q i)) M 1) z
  obtain ⟨N,hN⟩ := s.property
  refine ⟨N,m,?_⟩
  have hh := congrArg (localMap q i φ) h.symm
  change localMap q i φ (1 ⊗ₜ[R] m)=localMap q i φ ((s:R) • z) at hh
  rw [localMap_from,map_smul,←hN] at hh
  exact hh
 

theorem globalImage_iff (hq : Ideal.span (Set.range q)=⊤)
    (φ : ∀ i,Localization.Away (q i) →ₐ[R] C) (x : C ⊗[R] M) :
    (∃ m : M,1 ⊗ₜ[R] m=x) ↔ ∀ i,∃ z,localMap q i (φ i) z=x := by
  constructor
  · rintro ⟨m,rfl⟩ i;exact ⟨1 ⊗ₜ[R] m,localMap_from q i (φ i) m⟩
  · intro hx
    choose z hz using hx
    choose e a ha using fun i => localMap_clear q i (φ i) (z i)
    have hax (i : ι) : 1 ⊗ₜ[R] a i=q i^e i • x := by rw [ha i,hz i]
    let N := Finset.univ.sup e
    have he (i : ι) : e i≤N := Finset.le_sup (Finset.mem_univ i)
    let b (i : ι) : M := q i^(N-e i) • a i
    have hb (i : ι) : 1 ⊗ₜ[R] b i=q i^N • x := by
      rw [show b i=q i^(N-e i) • a i from rfl,TensorProduct.tmul_smul,hax,smul_smul,←pow_add,Nat.sub_add_cancel (he i)]
    obtain ⟨c,hc⟩ := FiniteCoverCech.partition R q hq N
    refine ⟨∑ i,c i • b i,?_⟩
    rw [TensorProduct.tmul_sum]
    simp only [TensorProduct.tmul_smul,hb,smul_smul,←Finset.sum_smul,hc,one_smul]
omit [Fintype ι] in
lemma global_injective [Module.Flat R M] (h : Function.Injective (algebraMap R C)) :
    Function.Injective (TensorProduct.mk R C M 1) := by
  have hi := Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap R C) h
  have he := hi.comp (TensorProduct.lid R M).symm.injective
  intro x y hxy
  apply he
  change algebraMap R C 1 ⊗ₜ[R] x=algebraMap R C 1 ⊗ₜ[R] y
  rw [map_one]
  exact hxy
end Lech.LocalizationImageCover


namespace Lech.AlternatingCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι] [Nonempty ι]
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
 

lemma empty_mem_of_singletons (h : (sortedComplex R M F hF).ExactAt 1)
    (x : M) (hx : ∀ i,x∈F {i}) : x∈F ∅ := by
  let f : sorted R M F 1 := fun s => ⟨x,by
    obtain ⟨i,hi⟩ := Finset.card_eq_one.mp s.property
    rw [hi];exact hx i⟩
  have hf : sortedDelta R M F hF 1 f=0 := by
    funext s
    apply Subtype.ext
    change (∑ i : Fin 2,(-1:ℤ)^i.val • x)=0
    simp [Fin.sum_univ_two]
  have he := ((sortedComplex R M F hF).exactAt_iff' (i:=0) (j:=1) (k:=2) (by simp) (by simp)).mp h
  rw [ShortComplex.moduleCat_exact_iff] at he
  obtain ⟨g,hg⟩ := he f (by
    change ((sortedComplex R M F hF).d 1 2).hom f=0
    rw [sortedComplex_d];exact hf)
  change ((sortedComplex R M F hF).d 0 1).hom g=f at hg
  rw [sortedComplex_d] at hg
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  let s : powersetCard ι 1 := ⟨{i},Finset.card_singleton _⟩
  have hv := congrArg (fun z : sorted R M F 1 => (z s:M)) hg
  change (∑ j : Fin 1,(-1:ℤ)^j.val • (g (delete s j):M))=x at hv
  simp only [Fin.sum_univ_one,Fin.val_zero,pow_zero,one_zsmul] at hv
  rw [DoubleCech.zeroIndex_eq (delete s 0)] at hv
  exact hv ▸ (g DoubleCech.emptyIndex).property
end Lech.AlternatingCech
end

end OAI
