import Mathlib
import OAI.RingTheory.Multiplicity.LechSignedUnit

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
namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
local instance gridGlobalWork : Algebra (A R n k) d.S := Algebra.compHom d.S (algebraMap (A R n k) B)
local instance gridGlobalTower : IsScalarTower (A R n k) B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Module.FaithfullyFlat (A R n k) B]
local instance gridGlobalRoot : Algebra (D R n k t v hv d) (GridAmbient R n) := gridRootAlgebra R n k t v hv d
local instance gridGlobalModule (m : Fin n → ℤ) : Module (D R n k t v hv d) (RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) :=
  Submodule.module _
def globalCoefficient (m : Fin n → ℤ) :
    RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m →ₗ[D R n k t v hv d] GridAmbient R n :=
  (LineBasisExtension.coordinates (GridAmbient R n) (gridBasis R n k t v hv d (fun _ => false) m)).comp
    (TensorProduct.mk (D R n k t v hv d) (GridAmbient R n) _ 1)
lemma gridCoefficient_from (σ : Chart n) (m : Fin n → ℤ)
    (z : RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) :
    gridCoefficient R n k t v hv d σ m (1 ⊗ₜ[D R n k t v hv d] z)=globalCoefficient R n k t v hv d m z := by
  change (gridBasis R n k t v hv d (fun _ => false) m).symm
    (chartToGridD R n k t v hv d σ 1 ⊗ₜ[D R n k t v hv d] z)=_
  rw [map_one]
  rfl
lemma globalCoefficient_local (m : Fin n → ℤ) (x : GridAmbient R n) :
    (∃ z,globalCoefficient R n k t v hv d m z=x) ↔ ∀ σ,x∈grid R n m {k} {σ} := by
  constructor
  · rintro ⟨z,rfl⟩ σ
    exact (gridCoefficient_range R n k t v hv d σ m _).mp ⟨_,gridCoefficient_from R n k t v hv d σ m z⟩
  · intro hx
    have hloc (σ : Chart n) : ∃ z,LocalizationImageCover.localMap (q R n k t v hv d) σ
        (chartToGridD R n k t v hv d σ) z=gridBasis R n k t v hv d (fun _ => false) m x := by
      obtain ⟨z,hz⟩ := (gridCoefficient_range R n k t v hv d σ m x).mpr (hx σ)
      refine ⟨z,?_⟩
      apply (gridBasis R n k t v hv d (fun _ => false) m).symm.injective
      rw [LinearEquiv.symm_apply_apply]
      exact hz
    obtain ⟨z,hz⟩ := (LocalizationImageCover.globalImage_iff (q R n k t v hv d)
      (RootInvariants.chartFunctions_span (f R n k) n (hn R n k) t v hv d)
      (chartToGridD R n k t v hv d) (gridBasis R n k t v hv d (fun _ => false) m x)).mpr hloc
    refine ⟨z,?_⟩
    change (gridBasis R n k t v hv d (fun _ => false) m).symm (1 ⊗ₜ[D R n k t v hv d] z)=x
    rw [hz,LinearEquiv.symm_apply_apply]
 

theorem globalCoefficient_range (m : Fin n → ℤ) (x : GridAmbient R n) :
    (∃ z,globalCoefficient R n k t v hv d m z=x) ↔ x∈grid R n m {k} ∅ := by
  rw [globalCoefficient_local]
  constructor
  · intro hx
    let : LinearOrder (Chart n) := LinearOrder.lift' (Fintype.equivFin (Chart n)) (Fintype.equivFin (Chart n)).injective
    exact AlternatingCech.empty_mem_of_singletons R (GridAmbient R n) (grid R n m {k})
      (grid_source_mono R n m {k}) (grid_source_acyclic R n m {k} (Finset.singleton_nonempty _) 1) x hx
  · intro hx σ
    exact grid_source_mono R n m {k} (Finset.empty_subset {σ}) hx
lemma globalCoefficient_injective (m : Fin n → ℤ) :
    Function.Injective (globalCoefficient R n k t v hv d m) := by
  let := RootInvariants.line_flat (f R n k) n (hn R n k) t v hv d m
  exact (gridBasis R n k t v hv d (fun _ => false) m).symm.injective.comp
    (LocalizationImageCover.global_injective (gridRootAlgebra_injective R n k t v hv d))
end Lech.RootChartAtlas


namespace Lech.PrimitiveRootModule
open Polynomial
open scoped TensorProduct
universe u
variable {A : Type u} [CommRing A]

abbrev chart (f : A[X]) := Localization.Away f

def coordinate (f : A[X]) : chart f := algebraMap A[X] (chart f) X

lemma eval_coordinate (f : A[X]) : (f.map (algebraMap A (chart f))).eval (coordinate f)=
    algebraMap A[X] (chart f) f := by
  rw [Polynomial.eval_map]
  have he : eval₂RingHom (algebraMap A (chart f)) (coordinate f)=algebraMap A[X] (chart f) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [coe_eval₂RingHom,eval₂_C]
      exact IsScalarTower.algebraMap_apply A A[X] (chart f) a
    · simp [coordinate]
  exact DFunLike.congr_fun he f

def valueUnit (f : A[X]) : (chart f)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := chart f) f).unit

lemma valueUnit_val (f : A[X]) : ((valueUnit f):chart f)=algebraMap A[X] (chart f) f :=
  (IsLocalization.Away.algebraMap_isUnit (S := chart f) f).unit_spec

lemma eval_valueUnit (f : A[X]) : (f.map (algebraMap A (chart f))).eval (coordinate f)=(valueUnit f:chart f) :=
  (eval_coordinate f).trans (valueUnit_val f).symm

def splitting (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) : UniversalSplitting.Data (chart f) n
    (BinaryChange.normalized (f.map (algebraMap A (chart f))) n (coordinate f) (valueUnit f)) := by
  let g := BinaryChange.normalized (f.map (algebraMap A (chart f))) n (coordinate f) (valueUnit f)
  have hdeg : (f.map (algebraMap A (chart f))).natDegree≤n := natDegree_map_le.trans hn
  have hgn : g.natDegree≤n :=
    (natDegree_C_mul_le _ _).trans (BinaryChange.transform_degree _ n (coordinate f))
  have hgt : g.coeff n=1 := BinaryChange.normalized_top _ (coordinate f) (valueUnit f)
    hdeg (eval_valueUnit f)
  exact Classical.choice (BinaryCover.ordered_splitting_of_top (chart f) n g hgn hgt)

 

abbrev module (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (ms : Fin n → ℤ) :=
  RootInvariants.module f n hn (coordinate f) (valueUnit f) (eval_valueUnit f) (splitting f n hn) ms

lemma finite_projective (f : A[X]) (n : ℕ) (hn : f.natDegree≤n)
    (hf : Ideal.span (Set.range f.coeff)=⊤) (ms : Fin n → ℤ) :
    Module.FinitePresentation A (module f n hn ms) ∧ Module.Projective A (module f n hn ms) := by
  let : Module.FaithfullyFlat A (chart f) := PrimitiveChart.faithfullyFlat_away f hf
  exact ⟨RootInvariants.finitePresentation f n hn _ _ _ _ ms,
    RootInvariants.projective f n hn _ _ _ _ ms⟩

lemma rankAtStalk (f : A[X]) (n : ℕ) (hn : f.natDegree≤n)
    (hf : Ideal.span (Set.range f.coeff)=⊤) (ms : Fin n → ℤ) (p : PrimeSpectrum A) :
    Module.rankAtStalk (module f n hn ms) p=n.factorial := by
  let : Module.FaithfullyFlat A (chart f) := PrimitiveChart.faithfullyFlat_away f hf
  exact RootInvariants.rankAtStalk f n hn _ _ _ _ ms p

 

def tensorEquiv (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (ms : Fin n → ℤ) :
    chart f ⊗[A] module f n hn ms ≃ₗ[chart f] (splitting f n hn).S :=
  RootInvariants.tensorEquiv f n hn _ _ _ _ ms
end Lech.PrimitiveRootModule


namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
local instance moduleWork : Algebra (A R n k) d.S := Algebra.compHom d.S (algebraMap (A R n k) B)
local instance moduleTower : IsScalarTower (A R n k) B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Module.FaithfullyFlat (A R n k) B]
local instance moduleTarget : Algebra (A R n k) (GridAmbient R n) := gridTargetAlgebra R n k
local instance moduleTargetModule : Module (A R n k) (GridAmbient R n) := Algebra.toModule
local instance moduleRoot : Algebra (D R n k t v hv d) (GridAmbient R n) := gridRootAlgebra R n k t v hv d
local instance moduleLine (m : Fin n → ℤ) : Module (D R n k t v hv d) (RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) :=
  Submodule.module _
local instance gridRootTower : IsScalarTower (A R n k) (D R n k t v hv d) (GridAmbient R n) :=
  IsScalarTower.of_algebraMap_eq fun a => ((algebraPoint R n k t v hv d (fun _ => false)).commutes a).symm
 
def globalCoefficientA (m : Fin n → ℤ) :
    RootInvariants.module (f R n k) n (hn R n k) t v hv d m →ₗ[A R n k] GridAmbient R n :=
  ((globalCoefficient R n k t v hv d m).restrictScalars (A R n k)).comp
    (RootInvariants.overAlgebraEquiv (f R n k) n (hn R n k) t v hv d m).symm.toLinearMap
lemma globalCoefficientA_range (m : Fin n → ℤ) (x : GridAmbient R n) :
    (∃ z,globalCoefficientA R n k t v hv d m z=x) ↔ x∈grid R n m {k} ∅ :=
  globalCoefficient_range R n k t v hv d m x
lemma globalCoefficientA_injective (m : Fin n → ℤ) :
    Function.Injective (globalCoefficientA R n k t v hv d m) :=
  globalCoefficient_injective R n k t v hv d m
include t v hv d in
lemma grid_smul_mem (m : Fin n → ℤ) (a : A R n k) (x : GridAmbient R n)
    (hx : x∈grid R n m {k} ∅) : a • x∈grid R n m {k} ∅ := by
  obtain ⟨z,rfl⟩ := (globalCoefficientA_range R n k t v hv d m x).mpr hx
  exact (globalCoefficientA_range R n k t v hv d m _).mp ⟨a • z, map_smul _ _ _⟩
end Lech.RootChartAtlas


namespace Lech.ProductSourceCover
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
local instance sectionAlgebra : Algebra (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := gridTargetAlgebra R n k
local instance sectionModuleBase : Module (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := Algebra.toModule
 

def sectionModule (m : Fin n → ℤ) : Submodule (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) where
  carrier := grid R n m {k} ∅
  zero_mem' := (grid R n m {k} ∅).zero_mem
  add_mem' := (grid R n m {k} ∅).add_mem
  smul_mem' a x hx := by
    let f := UniversalCoefficientChart.form R n k
    let : Module.FaithfullyFlat (UniversalCoefficientChart.Ring R n k) (PrimitiveRootModule.chart f) :=
      PrimitiveChart.faithfullyFlat_away f (UniversalCoefficientChart.form_primitive R n k)
    exact RootChartAtlas.grid_smul_mem R n k (PrimitiveRootModule.coordinate f)
      (PrimitiveRootModule.valueUnit f) (PrimitiveRootModule.eval_valueUnit f)
      (PrimitiveRootModule.splitting f n (UniversalCoefficientChart.form_degree R n k)) m a x hx
lemma sectionModule_mem (m : Fin n → ℤ) (x : GridAmbient R n) :
    x∈sectionModule R n k m ↔ x∈grid R n m {k} ∅ := Iff.rfl
end Lech.ProductSourceCover


namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
local instance projWork : Algebra (A R n k) d.S := Algebra.compHom d.S (algebraMap (A R n k) B)
local instance projTower : IsScalarTower (A R n k) B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
local instance projTarget : Algebra (A R n k) (GridAmbient R n) := gridTargetAlgebra R n k
local instance projTargetModule : Module (A R n k) (GridAmbient R n) := Algebra.toModule
variable [Module.FaithfullyFlat (A R n k) B]
def globalSectionMap (m : Fin n → ℤ) :
    RootInvariants.module (f R n k) n (hn R n k) t v hv d m →ₗ[A R n k] sectionModule R n k m :=
  (globalCoefficientA R n k t v hv d m).codRestrict _
    (fun z => (globalCoefficientA_range R n k t v hv d m _).mp ⟨z,rfl⟩)
 

def globalSectionEquiv (m : Fin n → ℤ) :
    RootInvariants.module (f R n k) n (hn R n k) t v hv d m ≃ₗ[A R n k] sectionModule R n k m :=
  LinearEquiv.ofBijective (globalSectionMap R n k t v hv d m) ⟨by
    intro x y h
    exact globalCoefficientA_injective R n k t v hv d m (congrArg Subtype.val h), by
    intro x
    obtain ⟨z,hz⟩ := (globalCoefficientA_range R n k t v hv d m x).mpr x.property
    exact ⟨z,Subtype.ext hz⟩⟩
include t v hv d in
lemma section_finitePresentation (m : Fin n → ℤ) :
    Module.FinitePresentation (A R n k) (sectionModule R n k m) := by
  let := RootInvariants.finitePresentation (f R n k) n (hn R n k) t v hv d m
  exact Module.FinitePresentation.of_equiv (globalSectionEquiv R n k t v hv d m)
include t v hv d in
lemma section_projective (m : Fin n → ℤ) :
    Module.Projective (A R n k) (sectionModule R n k m) := by
  let := RootInvariants.projective (f R n k) n (hn R n k) t v hv d m
  exact Module.Projective.of_equiv (globalSectionEquiv R n k t v hv d m)
include t v hv d in
lemma section_rank (m : Fin n → ℤ) (p : PrimeSpectrum (A R n k)) :
    Module.rankAtStalk (sectionModule R n k m) p=n.factorial := by
  rw [←congrFun (Module.rankAtStalk_eq_of_equiv (globalSectionEquiv R n k t v hv d m)) p]
  exact RootInvariants.rankAtStalk (f R n k) n (hn R n k) t v hv d m p
end Lech.RootChartAtlas


namespace Lech.ProductSourceCover
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
 

theorem sectionModule_properties (m : Fin n → ℤ) :
    Module.FinitePresentation (UniversalCoefficientChart.Ring R n k) (sectionModule R n k m) ∧
    Module.Projective (UniversalCoefficientChart.Ring R n k) (sectionModule R n k m) ∧
    ∀ p : PrimeSpectrum (UniversalCoefficientChart.Ring R n k),
      Module.rankAtStalk (sectionModule R n k m) p=n.factorial := by
  let f := UniversalCoefficientChart.form R n k
  let : Module.FaithfullyFlat (UniversalCoefficientChart.Ring R n k) (PrimitiveRootModule.chart f) :=
    PrimitiveChart.faithfullyFlat_away f (UniversalCoefficientChart.form_primitive R n k)
  exact ⟨RootChartAtlas.section_finitePresentation R n k (PrimitiveRootModule.coordinate f)
      (PrimitiveRootModule.valueUnit f) (PrimitiveRootModule.eval_valueUnit f)
      (PrimitiveRootModule.splitting f n (UniversalCoefficientChart.form_degree R n k)) m,
    RootChartAtlas.section_projective R n k (PrimitiveRootModule.coordinate f)
      (PrimitiveRootModule.valueUnit f) (PrimitiveRootModule.eval_valueUnit f)
      (PrimitiveRootModule.splitting f n (UniversalCoefficientChart.form_degree R n k)) m,
    RootChartAtlas.section_rank R n k (PrimitiveRootModule.coordinate f)
      (PrimitiveRootModule.valueUnit f) (PrimitiveRootModule.eval_valueUnit f)
      (PrimitiveRootModule.splitting f n (UniversalCoefficientChart.form_degree R n k)) m⟩
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
local instance locTarget : Algebra (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := gridTargetAlgebra R n k
local instance locTargetModule : Module (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := Algebra.toModule
lemma grid_clear_target (m : Fin n → ℤ) (s : Finset (Fin (n+1)))
    (x : GridAmbient R n) (hx : x∈grid R n m s ∅) :
    ∃ N : ℕ,(targetProduct R n k s)^N • x∈grid R n m {k} ∅ := by
  obtain ⟨N,h,hh,he⟩ := hx
  refine ⟨N,s.card*N,h,?_,?_⟩
  · have ht : levelTwist n m (Finset.card {k}) (s.card*N)=levelTwist n m s.card N := by
      ext i
      simp only [levelTwist,Finset.card_singleton,Nat.cast_mul,Nat.cast_one,mul_one]
      ring
    rw [ht]
    exact hh
  · change embed R n (denominator R n {k})^(s.card*N)*
      (gridTarget R n k ((targetProduct R n k s)^N)*x)=embed R n h
    rw [map_pow,show embed R n (denominator R n {k})=(targetUnit R n k:GridAmbient R n) by
      rw [targetUnit_val];simp only [denominator,AwayCover.denominator,Finset.prod_singleton]]
    calc
      _ = ((targetUnit R n k:GridAmbient R n)^s.card*gridTarget R n k (targetProduct R n k s))^N*x := by
        rw [mul_pow,pow_mul,mul_assoc]
      _ = _ := by rw [targetProduct_relation,he]
 

theorem grid_localization_iff (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s)
    (x : GridAmbient R n) : x∈grid R n m s ∅ ↔
      ∃ N : ℕ,(targetProduct R n k s)^N • x∈sectionModule R n k m := by
  constructor
  · exact grid_clear_target R n k m s x
  · rintro ⟨N,hN⟩
    have hloc : (targetProduct R n k s)^N • x∈grid R n m s ∅ :=
      grid_target_mono R n m ∅ (Finset.singleton_subset_iff.mpr hk) hN
    have hi := grid_zero_pow_mem R n s ∅ (↑((targetProductUnit R n k s)⁻¹):GridAmbient R n)
      (targetProductUnit_inv_mem R n k s) N
    have hm := grid_mul_mem R n 0 m s ∅ _ _ hi hloc
    have he : (↑((targetProductUnit R n k s)⁻¹):GridAmbient R n)^N*((targetProduct R n k s)^N • x)=x := by
      change (↑((targetProductUnit R n k s)⁻¹):GridAmbient R n)^N*
        (gridTarget R n k ((targetProduct R n k s)^N)*x)=x
      rw [map_pow,←targetProductUnit_val,←mul_assoc,←mul_pow,Units.inv_mul,one_pow,one_mul]
    simpa only [he,zero_add] using hm
 

def overlapModule (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s) :
    Submodule (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) where
  carrier := grid R n m s ∅
  zero_mem' := (grid R n m s ∅).zero_mem
  add_mem' := (grid R n m s ∅).add_mem
  smul_mem' a x hx := by
    obtain ⟨N,hN⟩ := (grid_localization_iff R n k m s hk x).mp hx
    apply (grid_localization_iff R n k m s hk (a • x)).mpr
    refine ⟨N,?_⟩
    have hh := (sectionModule R n k m).smul_mem a hN
    convert hh using 1
    change gridTarget R n k ((targetProduct R n k s)^N)*(gridTarget R n k a*x)=
      gridTarget R n k a*(gridTarget R n k ((targetProduct R n k s)^N)*x)
    ring

def restriction (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s) :
    sectionModule R n k m →ₗ[UniversalCoefficientChart.Ring R n k] overlapModule R n k m s hk :=
  Submodule.inclusion (grid_target_mono R n m ∅ (Finset.singleton_subset_iff.mpr hk))
lemma restriction_injective (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s) :
    Function.Injective (restriction R n k m s hk) := Submodule.inclusion_injective _
lemma inverse_mem_overlap (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s)
    (x : overlapModule R n k m s hk) (N : ℕ) :
    (↑((targetProductUnit R n k s)⁻¹):GridAmbient R n)^N*(x:GridAmbient R n)∈overlapModule R n k m s hk := by
  have h := grid_mul_mem R n 0 m s ∅ _ _
    (grid_zero_pow_mem R n s ∅ _ (targetProductUnit_inv_mem R n k s) N) x.property
  change _∈grid R n m s ∅
  simpa only [zero_add] using h
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
local instance localizedTarget : Algebra (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := gridTargetAlgebra R n k
local instance localizedTargetModule : Module (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := Algebra.toModule
 

instance restriction_localized (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s) :
    IsLocalizedModule (Submonoid.powers (targetProduct R n k s)) (restriction R n k m s hk) where
  map_units c := by
    obtain ⟨N,hN⟩ := c.property
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y h
      apply Subtype.ext
      have he := congrArg Subtype.val h
      change gridTarget R n k (c:UniversalCoefficientChart.Ring R n k)*(x:GridAmbient R n)=
        gridTarget R n k (c:UniversalCoefficientChart.Ring R n k)*(y:GridAmbient R n) at he
      rw [←hN,map_pow,←targetProductUnit_val] at he
      exact (IsUnit.pow N (targetProductUnit R n k s).isUnit).mul_left_cancel he
    · intro x
      refine ⟨⟨_,inverse_mem_overlap R n k m s hk x N⟩,Subtype.ext ?_⟩
      change gridTarget R n k (c:UniversalCoefficientChart.Ring R n k)*
        ((↑((targetProductUnit R n k s)⁻¹):GridAmbient R n)^N*(x:GridAmbient R n))=(x:GridAmbient R n)
      rw [←hN,map_pow,←targetProductUnit_val,←mul_assoc,←mul_pow,Units.mul_inv,one_pow,one_mul]
  surj x := by
    obtain ⟨N,hN⟩ := (grid_localization_iff R n k m s hk x).mp x.property
    refine ⟨(⟨(targetProduct R n k s)^N • (x:GridAmbient R n),hN⟩,
      ⟨(targetProduct R n k s)^N,N,rfl⟩),Subtype.ext rfl⟩
  exists_of_eq h := by
    refine ⟨1,?_⟩
    simpa only [OneMemClass.coe_one,one_smul] using restriction_injective R n k m s hk h
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
local instance overlapTarget : Algebra (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := gridTargetAlgebra R n k
local instance overlapTargetModule : Module (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := Algebra.toModule
abbrev OverlapRing (s : Finset (Fin (n+1))) := Localization.Away (targetProduct R n k s)
local instance overlapScalar (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s) :
    Module (OverlapRing R n k s) (overlapModule R n k m s hk) :=
  IsLocalizedModule.module (Submonoid.powers (targetProduct R n k s)) (restriction R n k m s hk)
local instance overlapTower (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s) :
    IsScalarTower (UniversalCoefficientChart.Ring R n k) (OverlapRing R n k s) (overlapModule R n k m s hk) :=
  IsLocalizedModule.isScalarTower_module (Submonoid.powers (targetProduct R n k s)) (restriction R n k m s hk)
 

def overlapBaseChange (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s) :
    OverlapRing R n k s ⊗[UniversalCoefficientChart.Ring R n k] sectionModule R n k m ≃ₗ[OverlapRing R n k s]
      overlapModule R n k m s hk :=
  (IsLocalizedModule.isBaseChange (Submonoid.powers (targetProduct R n k s)) (OverlapRing R n k s)
    (restriction R n k m s hk)).equiv
lemma overlapBaseChange_one (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s)
    (x : sectionModule R n k m) :
    overlapBaseChange R n k m s hk (1 ⊗ₜ[UniversalCoefficientChart.Ring R n k] x)=restriction R n k m s hk x := by
  exact (IsBaseChange.equiv_tmul _ _ _).trans (one_smul _ _)
 

theorem overlapModule_properties (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s) :
    Module.FinitePresentation (OverlapRing R n k s) (overlapModule R n k m s hk) ∧
    Module.Projective (OverlapRing R n k s) (overlapModule R n k m s hk) ∧
    ∀ p : PrimeSpectrum (OverlapRing R n k s),Module.rankAtStalk (overlapModule R n k m s hk) p=n.factorial := by
  obtain ⟨hfp,hpr,hr⟩ := sectionModule_properties R n k m
  let := hfp
  let := hpr
  refine ⟨Module.FinitePresentation.of_equiv (overlapBaseChange R n k m s hk),
    Module.Projective.of_equiv (overlapBaseChange R n k m s hk),?_⟩
  intro p
  rw [←Module.rankAtStalk_eq_of_equiv (overlapBaseChange R n k m s hk),Module.rankAtStalk_baseChange]
  exact hr _
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open MvPolynomial HomogeneousLocalization
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1)) (s : Finset (Fin (n+1)))
attribute [local instance] MvPolynomial.gradedAlgebra
def projectiveRemainder : MvPolynomial (Fin (n+1)) R := ∏ j∈s.erase k,X j
lemma projectiveRemainder_homogeneous :
    projectiveRemainder R n k s∈ProjectiveCoefficientChart.grading R n (s.erase k).card := by
  simpa [projectiveRemainder] using IsHomogeneous.prod (s.erase k) (fun j => X (R:=R) j)
    (fun _ => 1) (fun j _ => isHomogeneous_X R j)
lemma projectiveRemainder_product (hk : k∈s) :
    X k*projectiveRemainder R n k s=∏ j∈s,X (R:=R) j := by
  exact Finset.mul_prod_erase s (fun j => X (R:=R) j) hk
lemma projectiveRemainder_evaluate (hk : k∈s) :
    ProjectiveCoefficientChart.evaluate R n k (projectiveRemainder R n k s)=targetProduct R n k s := by
  simp only [projectiveRemainder,map_prod,ProjectiveCoefficientChart.evaluate,MvPolynomial.aeval_X]
  rw [targetProduct,←Finset.mul_prod_erase s (UniversalCoefficientChart.coefficient R n k) hk,
    UniversalCoefficientChart.coefficient_self,one_mul]
 

abbrev HomogeneousOverlapRing := ProjectiveCoefficientChart.Overlap R n k (projectiveRemainder R n k s)
local instance homogeneousRing : CommRing (HomogeneousOverlapRing R n k s) := inferInstance
instance homogeneousOverlapAlgebra : Algebra (UniversalCoefficientChart.Ring R n k) (HomogeneousOverlapRing R n k s) :=
  ProjectiveCoefficientChart.overlapCoefficientAlgebra R n k (projectiveRemainder R n k s)
    (projectiveRemainder_homogeneous R n k s)
lemma homogeneousOverlap_isLocalization (hk : k∈s) :
    IsLocalization.Away (targetProduct R n k s) (HomogeneousOverlapRing R n k s) := by
  rw [←projectiveRemainder_evaluate R n k s hk]
  exact ProjectiveCoefficientChart.overlap_isLocalization R n k (projectiveRemainder R n k s)
    (projectiveRemainder_homogeneous R n k s)
local instance homogeneousTarget : Algebra (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := gridTargetAlgebra R n k
local instance homogeneousTargetModule : Module (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := Algebra.toModule
variable (m : Fin n → ℤ) (hk : k∈s)
local instance homogeneousTensorAdd : AddCommGroup
    (HomogeneousOverlapRing R n k s ⊗[UniversalCoefficientChart.Ring R n k] sectionModule R n k m) := TensorProduct.addCommGroup
local instance homogeneousOverlapScalar : Module (HomogeneousOverlapRing R n k s) (overlapModule R n k m s hk) :=
  letI := homogeneousOverlap_isLocalization R n k s hk
  IsLocalizedModule.module (Submonoid.powers (targetProduct R n k s)) (restriction R n k m s hk)
local instance homogeneousOverlapTower : IsScalarTower (UniversalCoefficientChart.Ring R n k)
    (HomogeneousOverlapRing R n k s) (overlapModule R n k m s hk) := by
  let := homogeneousOverlap_isLocalization R n k s hk
  exact IsLocalizedModule.isScalarTower_module (Submonoid.powers (targetProduct R n k s)) (restriction R n k m s hk)
 

def homogeneousOverlapBaseChange :
    HomogeneousOverlapRing R n k s ⊗[UniversalCoefficientChart.Ring R n k] sectionModule R n k m
      ≃ₗ[HomogeneousOverlapRing R n k s] overlapModule R n k m s hk :=
  letI := homogeneousOverlap_isLocalization R n k s hk
  (IsLocalizedModule.isBaseChange (Submonoid.powers (targetProduct R n k s)) (HomogeneousOverlapRing R n k s)
    (restriction R n k m s hk)).equiv
lemma homogeneousOverlapBaseChange_one (x : sectionModule R n k m) :
    homogeneousOverlapBaseChange R n k s m hk (1 ⊗ₜ[UniversalCoefficientChart.Ring R n k] x)=
      restriction R n k m s hk x := by
  let := homogeneousOverlap_isLocalization R n k s hk
  exact (IsBaseChange.equiv_tmul _ _ _).trans (one_smul _ _)
theorem homogeneousOverlapModule_properties :
    Module.FinitePresentation (HomogeneousOverlapRing R n k s) (overlapModule R n k m s hk) ∧
    Module.Projective (HomogeneousOverlapRing R n k s) (overlapModule R n k m s hk) ∧
    ∀ p : PrimeSpectrum (HomogeneousOverlapRing R n k s),
      Module.rankAtStalk (overlapModule R n k m s hk) p=n.factorial := by
  obtain ⟨hfp,hpr,hr⟩ := sectionModule_properties R n k m
  let := hfp
  let := hpr
  refine ⟨Module.FinitePresentation.of_equiv (homogeneousOverlapBaseChange R n k s m hk),
    Module.Projective.of_equiv (homogeneousOverlapBaseChange R n k s m hk),?_⟩
  intro p
  rw [←Module.rankAtStalk_eq_of_equiv (homogeneousOverlapBaseChange R n k s m hk),Module.rankAtStalk_baseChange]
  exact hr _
end Lech.ProductSourceCover
end
end

end OAI
