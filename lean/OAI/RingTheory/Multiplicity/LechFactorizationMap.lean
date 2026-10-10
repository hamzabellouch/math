import Mathlib
import OAI.RingTheory.Multiplicity.UniversalFactorMapMapChart

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
open Polynomial
universe u
lemma factorization_map {A T U : Type u} [CommRing A] [CommRing T] [CommRing U]
    [Algebra A T] [Algebra A U] (φ : T →ₐ[A] U) (f : A[X]) (n : ℕ)
    (w : Tˣ) (a b : Fin n → T)
    (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
      (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1)) :
    (f.map (algebraMap A U)).homogenize n=MvPolynomial.C (φ (w:T))*∏ i,
      (MvPolynomial.C (φ (a i))*MvPolynomial.X 0+MvPolynomial.C (φ (b i))*MvPolynomial.X 1) := by
  rw [←φ.comp_algebraMap,←Polynomial.map_map,Polynomial.homogenize_map,hf]
  simp only [map_mul,map_prod,map_add,MvPolynomial.map_C,MvPolynomial.map_X]
  rfl
end Lech


namespace Lech.RootChartAtlas

section
open Polynomial ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
local instance gridWorkAlgebra : Algebra (A R n k) d.S := Algebra.compHom d.S (algebraMap (A R n k) B)
local instance gridWorkTower : IsScalarTower (A R n k) B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Module.FaithfullyFlat (A R n k) B]
abbrev GridD := RootInvariants.algebra (f R n k) n (hn R n k) t v hv d

def chartToGrid (σ : Chart n) : L R n k t v hv d σ →ₐ[A R n k] GridAmbient R n :=
  (localizedChartA R n σ k).comp (toH R n k t v hv d σ)
lemma chartToGrid_coordinate (σ : Chart n) (i : Fin n) (b : Bool) :
    chartToGrid R n k t v hv d σ (coordinate R n k t v hv d σ i b)=
      if b then chartScalar R n σ (ProductLinearChart.a R n σ i)
      else chartScalar R n σ (ProductLinearChart.b R n σ i) := by
  change localizedChart R n σ k (toH R n k t v hv d σ _)=_
  rw [toH_coordinate]
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte,localizedChart_algebraMap]
def factorUnit (σ : Chart n) : (GridAmbient R n)ˣ :=
  Units.map (localizedChart R n σ k).toMonoidHom (ProductLinearChart.denominator R n σ k)⁻¹
lemma factorization_grid (σ : Chart n) :
    ((f R n k).map (algebraMap (A R n k) (GridAmbient R n))).homogenize n=
      MvPolynomial.C (factorUnit R n k σ:GridAmbient R n)*∏ i,
        (MvPolynomial.C (chartScalar R n σ (ProductLinearChart.a R n σ i))*MvPolynomial.X 0+
          MvPolynomial.C (chartScalar R n σ (ProductLinearChart.b R n σ i))*MvPolynomial.X 1) := by
  have h := factorization_map (localizedChartA R n σ k) (f R n k) n
    ((ProductLinearChart.denominator R n σ k)⁻¹)
    (fun i => algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.a R n σ i))
    (fun i => algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.b R n σ i))
    (ProductLinearChart.target_factorization R n σ k)
  have hc (z : ProductLinearChart.Ring R n) :
      localizedChartA R n σ k (algebraMap (ProductLinearChart.Ring R n) (H R n k σ) z)=chartScalar R n σ z :=
    localizedChart_algebraMap R n σ k z
  simp only [hc] at h
  exact h
lemma factor_selected (σ : Chart n) (i : Fin n) :
    (if σ i then chartScalar R n σ (ProductLinearChart.a R n σ i)
      else chartScalar R n σ (ProductLinearChart.b R n σ i))=1 := by
  have h := congrArg (chartScalar R n σ) (ProductLinearChart.selected R n σ i)
  cases hs : σ i <;> simpa only [hs,Bool.false_eq_true,↓reduceIte,map_one] using h

def algebraPoint (σ : Chart n) : GridD R n k t v hv d →ₐ[A R n k] GridAmbient R n :=
  (chartToGrid R n k t v hv d σ).comp (IsScalarTower.toAlgHom (A R n k) _ _)
lemma algebraPoint_eq_factor (σ : Chart n) :
    algebraPoint R n k t v hv d σ=UniversalFactorMap.map (f R n k) n (hn R n k) t v hv d
      (factorUnit R n k σ) (fun i => chartScalar R n σ (ProductLinearChart.a R n σ i))
      (fun i => chartScalar R n σ (ProductLinearChart.b R n σ i)) (factorization_grid R n k σ) := by
  have h := UniversalFactorMap.chartMap_unique (f R n k) n (hn R n k) t v hv d σ
    (factorUnit R n k σ) _ _ (factorization_grid R n k σ) (factor_selected R n σ)
    (chartToGrid R n k t v hv d σ)
    (fun i => chartToGrid_coordinate R n k t v hv d σ i true)
    (fun i => chartToGrid_coordinate R n k t v hv d σ i false)
  ext x
  change chartToGrid R n k t v hv d σ (algebraMap (GridD R n k t v hv d) (L R n k t v hv d σ) x)=_
  rw [h,UniversalFactorMap.chartMap_from]

def rescaleUnit (σ : Chart n) (i : Fin n) : (GridAmbient R n)ˣ :=
  Units.map (embed R n).toMonoidHom (if σ i then (ProductLaurent.variableUnit R n i)⁻¹ else 1)
lemma gridFactor_a (σ : Chart n) (i : Fin n) :
    chartScalar R n σ (ProductLinearChart.a R n σ i)=
      (rescaleUnit R n σ i:GridAmbient R n)*chartScalar R n (fun _ => false) (ProductLinearChart.a R n (fun _ => false) i) := by
  change embed R n (ProductLaurent.chartMap R n σ _)=
    embed R n (↑(if σ i then (ProductLaurent.variableUnit R n i)⁻¹ else 1):Ambient R n)*
      embed R n (ProductLaurent.chartMap R n (fun _ => false) _)
  rw [ProductLaurent.chartMap_a,ProductLaurent.chartMap_a]
  simp only [Bool.false_eq_true,↓reduceIte,Units.val_one,one_mul,map_mul]
lemma gridFactor_b (σ : Chart n) (i : Fin n) :
    chartScalar R n σ (ProductLinearChart.b R n σ i)=
      (rescaleUnit R n σ i:GridAmbient R n)*chartScalar R n (fun _ => false) (ProductLinearChart.b R n (fun _ => false) i) := by
  change embed R n (ProductLaurent.chartMap R n σ _)=
    embed R n (↑(if σ i then (ProductLaurent.variableUnit R n i)⁻¹ else 1):Ambient R n)*
      embed R n (ProductLaurent.chartMap R n (fun _ => false) _)
  rw [ProductLaurent.chartMap_b,ProductLaurent.chartMap_b]
  simp only [Bool.false_eq_true,↓reduceIte,Units.val_one,map_one,mul_one]
 

theorem algebraPoint_independent (σ : Chart n) :
    algebraPoint R n k t v hv d σ=algebraPoint R n k t v hv d (fun _ => false) := by
  rw [algebraPoint_eq_factor,algebraPoint_eq_factor]
  exact UniversalFactorMap.map_rescale (f R n k) n (hn R n k) t v hv d
    _ _ _ _ _ _ _ _ (rescaleUnit R n σ) (gridFactor_a R n σ) (gridFactor_b R n σ)
end


open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
local instance regularWorkAlgebra : Algebra (A R n k) d.S := Algebra.compHom d.S (algebraMap (A R n k) B)
local instance regularWorkTower : IsScalarTower (A R n k) B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Module.FaithfullyFlat (A R n k) B]
abbrev D := RootInvariants.algebra (f R n k) n (hn R n k) t v hv d
abbrev q := RootInvariants.chartFunction (f R n k) n (hn R n k) t v hv d
lemma toH_chartFunction (σ τ : Fin n → Bool) :
    toH R n k t v hv d τ (algebraMap (D R n k t v hv d) (L R n k t v hv d τ) (q R n k t v hv d σ))=
      (↑((ProductLinearChart.denominator R n τ k)⁻¹):H R n k τ)*∏ i,
        (if σ i then algebraMap (ProductLinearChart.Ring R n) (H R n k τ) (ProductLinearChart.a R n τ i)
          else algebraMap (ProductLinearChart.Ring R n) (H R n k τ) (ProductLinearChart.b R n τ i)) := by
  rw [toH,UniversalFactorMap.chartMap_from,UniversalFactorMap.map_chartFunction]
lemma coordinate_regular (τ : Fin n → Bool) (i : Fin n) (b : Bool) :
    IsRegular (if b then ProductLinearChart.a R n τ i else ProductLinearChart.b R n τ i) := by
  cases b <;> cases ht : τ i <;> simp [ProductLinearChart.a,ProductLinearChart.b,ht, isRegular_one]
lemma localized_function_regular (σ τ : Fin n → Bool) :
    IsRegular (algebraMap (D R n k t v hv d) (L R n k t v hv d τ) (q R n k t v hv d σ)) := by
  have h : IsRegular (toH R n k t v hv d τ
      (algebraMap (D R n k t v hv d) (L R n k t v hv d τ) (q R n k t v hv d σ))) := by
    rw [toH_chartFunction]
    apply ((ProductLinearChart.denominator R n τ k)⁻¹).isUnit.isRegular.mul
    apply IsRegular.prod
    intro i _
    have h := PrincipalCoverRegular.regular_map
      (S := H R n k τ) (M := Submonoid.powers ((ProductLinearChart.product R n τ).coeff k))
      (coordinate_regular R n τ i (σ i))
    simpa only [apply_ite] using h
  constructor
  · intro x y hxy
    apply (equiv R n k t v hv d τ).injective
    change toH R n k t v hv d τ x = toH R n k t v hv d τ y
    exact h.left (by simpa only [map_mul] using congrArg (toH R n k t v hv d τ) hxy)
  · intro x y hxy
    apply (equiv R n k t v hv d τ).injective
    change toH R n k t v hv d τ x = toH R n k t v hv d τ y
    exact h.right (by simpa only [map_mul] using congrArg (toH R n k t v hv d τ) hxy)
 

theorem chartFunction_regular (σ : Fin n → Bool) : IsRegular (q R n k t v hv d σ) :=
  PrincipalCoverRegular.regular_of_cover (q R n k t v hv d)
    (RootInvariants.chartFunctions_span (f R n k) n (hn R n k) t v hv d) _
    (localized_function_regular R n k t v hv d σ)
end Lech.RootChartAtlas


namespace Lech.StandardFactorCharts
open Polynomial
universe u z
variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
variable (D : Subalgebra A S) (n : ℕ) (P : Fin n → Bool → S)
  (v : Sˣ) (c : (Fin n → Bool) → D)
  (hc : ∀ σ,(c σ:S)=(v:S)*∏ i,P i (σ i))
variable {T : Type z} [CommRing T]
include hc in
lemma coordinate_relation_ring (σ : Fin n → Bool) (ψ : L D n c σ →+* T) (φ : S →+* T)
    (hcompat : ∀ x : D,ψ (algebraMap D (L D n c σ) x)=φ (x:S)) (i : Fin n) (b : Bool) :
    ψ (coordinate D n c σ i b)*φ (P i (σ i))=φ (P i b) := by
  have h := congrArg φ (cross_identity D n P v c hc σ i b)
  simp only [map_mul] at h
  have hu := congrArg ψ (Units.mul_inv (chartUnit D n c σ))
  rw [map_mul,chartUnit_val,hcompat,map_one] at hu
  rw [coordinate,map_mul,hcompat]
  calc
    φ (c (Function.update σ i b):S)*ψ ((chartUnit D n c σ)⁻¹).val*φ (P i (σ i))=
      (φ (c (Function.update σ i b):S)*φ (P i (σ i)))*ψ ((chartUnit D n c σ)⁻¹).val := by ring
    _ = (φ (c σ:S)*φ (P i b))*ψ ((chartUnit D n c σ)⁻¹).val := by rw [h]
    _ = φ (P i b)*(φ (c σ:S)*ψ ((chartUnit D n c σ)⁻¹).val) := by ring
    _ = φ (P i b) := by rw [hu,mul_one]

include hc in
lemma selected_unit (σ : Fin n → Bool) (ψ : L D n c σ →+* T) (φ : S →+* T)
    (hcompat : ∀ x : D,ψ (algebraMap D (L D n c σ) x)=φ (x:S)) (i : Fin n) :
    IsUnit (φ (P i (σ i))) := by
  have hu : IsUnit (φ (c σ:S)) := by
    rw [← hcompat]
    exact (IsLocalization.Away.algebraMap_isUnit (c σ)).map ψ
  rw [hc,map_mul,map_prod] at hu
  have hp := isUnit_of_mul_isUnit_right hu
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => φ (P j (σ j))) (Finset.mem_univ i)) hp
end Lech.StandardFactorCharts


namespace Lech.UnitSection
open scoped TensorProduct
universe u v w
variable {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  [Module.FaithfullyFlat R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

def map (m : M) : R →ₗ[R] M := (LinearMap.id : R →ₗ[R] R).smulRight m

omit [Module.FaithfullyFlat R S] in
lemma compat (m : M) (e : S ⊗[R] M ≃ₗ[S] S) (u : Sˣ)
    (he : e (1 ⊗ₜ[R] m)=(u:S)) :
    e.toLinearMap.comp ((map m).baseChange S)=
      ((TensorProduct.AlgebraTensorModule.rid R S S) ≪≫ₗ LinearEquiv.smulOfUnit u).toLinearMap := by
  ext
  change e (1 ⊗ₜ[R] ((1:R) • m))=(u:S)*((1:R) • (1:S))
  simp only [one_smul, mul_one, he]

def equiv (m : M) (e : S ⊗[R] M ≃ₗ[S] S) (u : Sˣ)
    (he : e (1 ⊗ₜ[R] m)=(u:S)) : R ≃ₗ[R] M := by
  apply LinearEquiv.ofBijective (map m)
  apply FFTensorMaps.bijective (R := R) (M := R) (N := M) (Q := S) S
    (map m) ((TensorProduct.AlgebraTensorModule.rid R S S) ≪≫ₗ LinearEquiv.smulOfUnit u) e
  exact compat S m e u he
end Lech.UnitSection


namespace Lech.LocalLine
open scoped TensorProduct
universe u v w z
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  [Module.FaithfullyFlat R S]
variable (L : Type z) [CommRing L] [Algebra R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
local instance : Algebra S (L ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
local instance : IsScalarTower R S (L ⊗[R] S) := Algebra.TensorProduct.right_isScalarTower

 
def trivial (e : S ⊗[R] M ≃ₗ[S] S) :
    (L ⊗[R] S) ⊗[L] (L ⊗[R] M) ≃ₗ[L ⊗[R] S] L ⊗[R] S :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R L (L ⊗[R] S) (L ⊗[R] S) M ≪≫ₗ
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R S (L ⊗[R] S) (L ⊗[R] S) M).symm ≪≫ₗ
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (L ⊗[R] S) _) e ≪≫ₗ
  TensorProduct.AlgebraTensorModule.rid S (L ⊗[R] S) (L ⊗[R] S)

omit [Module.FaithfullyFlat R S] in
lemma trivial_tmul (e : S ⊗[R] M ≃ₗ[S] S) (m : M) :
    trivial L e (1 ⊗ₜ[L] (1 ⊗ₜ[R] m))=1 ⊗ₜ[R] e (1 ⊗ₜ[R] m) := by
  simp only [trivial,LinearEquiv.trans_apply,TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    one_smul,TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  rw [Algebra.smul_def,mul_one]
  rfl


def basisEquiv (e : S ⊗[R] M ≃ₗ[S] S) (m : M)
    (hu : IsUnit (1 ⊗ₜ[R] e (1 ⊗ₜ[R] m) : L ⊗[R] S)) :
    L ≃ₗ[L] L ⊗[R] M :=
  UnitSection.equiv (L ⊗[R] S) (1 ⊗ₜ[R] m) (trivial L e) hu.unit
    ((trivial_tmul L e m).trans hu.unit_spec.symm)

lemma basisEquiv_apply (e : S ⊗[R] M ≃ₗ[S] S) (m : M)
    (hu : IsUnit (1 ⊗ₜ[R] e (1 ⊗ₜ[R] m) : L ⊗[R] S)) (x : L) :
    basisEquiv L e m hu x=x ⊗ₜ[R] m := by
  change x • ((1:L) ⊗ₜ[R] m)=_
  rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]

lemma section_relation (e : S ⊗[R] M ≃ₗ[S] S) (m y : M) (r : L)
    (h : (algebraMap L (L ⊗[R] S) r)*(1 ⊗ₜ[R] e (1 ⊗ₜ[R] m))=
      1 ⊗ₜ[R] e (1 ⊗ₜ[R] y)) :
    r ⊗ₜ[R] m=(1:L) ⊗ₜ[R] y := by
  have hinj := Module.FaithfullyFlat.tensorProduct_mk_injective (A := L) (B := L ⊗[R] S) (L ⊗[R] M)
  apply hinj
  apply (trivial L e).injective
  have ht : (1:L ⊗[R] S) ⊗ₜ[L] (r ⊗ₜ[R] m)=
      r • ((1:L ⊗[R] S) ⊗ₜ[L] ((1:L) ⊗ₜ[R] m)) := by
    rw [← TensorProduct.tmul_smul,TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  change trivial L e (1 ⊗ₜ[L] (r ⊗ₜ[R] m))=trivial L e (1 ⊗ₜ[L] ((1:L) ⊗ₜ[R] y))
  have hh : trivial L e (r • ((1:L ⊗[R] S) ⊗ₜ[L] ((1:L) ⊗ₜ[R] m)))=
      r • trivial L e ((1:L ⊗[R] S) ⊗ₜ[L] ((1:L) ⊗ₜ[R] m)) :=
    ((trivial L e).restrictScalars L).map_smul r _
  rw [ht,hh,trivial_tmul,trivial_tmul,Algebra.smul_def]
  exact h
end Lech.LocalLine


namespace Lech.RootInvariants

section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

abbrev chartModule (σ : Fin n → Bool) (ms : Fin n → ℤ) :=
  chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ms

lemma chart_tensor_compat (σ : Fin n → Bool) (x : algebra f n hn t v hv d) :
    @algebraMap (chartRing f n hn t v hv d σ)
      (chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S)
      inferInstance inferInstance inferInstance
      (algebraMap (algebra f n hn t v hv d) (chartRing f n hn t v hv d σ) x)=
    (Algebra.TensorProduct.includeRight : d.S →ₐ[algebra f n hn t v hv d]
      chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S) (x:d.S) := by
  exact (IsScalarTower.algebraMap_apply (algebra f n hn t v hv d)
    (chartRing f n hn t v hv d σ)
    (chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S) x).symm.trans
      ((Algebra.TensorProduct.includeRight : d.S →ₐ[algebra f n hn t v hv d]
        chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S).commutes x).symm

lemma selected_tensor_unit (σ : Fin n → Bool) (i : Fin n) :
    IsUnit ((1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d]
      (selected f n hn t v hv d σ i:d.S)) := by
  have h := StandardFactorCharts.selected_unit (algebra f n hn t v hv d) n
    (pair f n hn t v hv d) (Units.map (algebraMap B d.S).toMonoidHom v)
    (chartFunction f n hn t v hv d) (pair_product f n hn t v hv d) σ
    (algebraMap (chartRing f n hn t v hv d σ)
      (chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S))
    (Algebra.TensorProduct.includeRight : d.S →ₐ[algebra f n hn t v hv d]
      chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S).toRingHom
    (chart_tensor_compat f n hn t v hv d σ) i
  change IsUnit ((1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d]
    pair f n hn t v hv d i (σ i)) at h
  cases hs : σ i <;> simpa only [pair,selected,hs,Bool.false_eq_true,↓reduceIte] using h

lemma lineTensorEquiv_one [Module.Flat A B] (ms : Fin n → ℤ)
    (x : overAlgebra f n hn t v hv d ms) :
    lineTensorEquiv f n hn t v hv d ms (1 ⊗ₜ[algebra f n hn t v hv d] x)=(x:d.S) := by
  change (1:d.S)*(x:d.S)=(x:d.S)
  exact one_mul _


def chartLineEquiv [Module.FaithfullyFlat A B] (σ : Fin n → Bool) (i : Fin n) :
    chartRing f n hn t v hv d σ ≃ₗ[chartRing f n hn t v hv d σ]
      chartModule f n hn t v hv d σ (Pi.single i (1:ℤ)) := by
  let := algebra_faithfullyFlat f n hn t v hv d
  exact LocalLine.basisEquiv (chartRing f n hn t v hv d σ)
    (lineTensorEquiv f n hn t v hv d (Pi.single i (1:ℤ)))
    (selected f n hn t v hv d σ i) (by
      rw [lineTensorEquiv_one]
      exact selected_tensor_unit f n hn t v hv d σ i)

lemma chartLineEquiv_apply [Module.FaithfullyFlat A B] (σ : Fin n → Bool) (i : Fin n)
    (x : chartRing f n hn t v hv d σ) :
    chartLineEquiv f n hn t v hv d σ i x=
      x ⊗ₜ[algebra f n hn t v hv d] selected f n hn t v hv d σ i := by
  let := algebra_faithfullyFlat f n hn t v hv d
  exact LocalLine.basisEquiv_apply _ _ _ _ _


lemma chart_section_relation [Module.FaithfullyFlat A B] (σ : Fin n → Bool) (i : Fin n) (b : Bool) :
    chartLineEquiv f n hn t v hv d σ i (chartCoordinate f n hn t v hv d σ i b)=
      (1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d]
        (if b then sectionX f n hn t v hv d i else sectionY f n hn t v hv d i) := by
  let := algebra_faithfullyFlat f n hn t v hv d
  rw [chartLineEquiv_apply]
  apply LocalLine.section_relation (chartRing f n hn t v hv d σ)
    (lineTensorEquiv f n hn t v hv d (Pi.single i (1:ℤ)))
  rw [lineTensorEquiv_one,lineTensorEquiv_one]
  have h := StandardFactorCharts.coordinate_relation_ring (algebra f n hn t v hv d) n
    (pair f n hn t v hv d) (Units.map (algebraMap B d.S).toMonoidHom v)
    (chartFunction f n hn t v hv d) (pair_product f n hn t v hv d) σ
    (algebraMap (chartRing f n hn t v hv d σ)
      (chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S))
    (Algebra.TensorProduct.includeRight : d.S →ₐ[algebra f n hn t v hv d]
      chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S).toRingHom
    (chart_tensor_compat f n hn t v hv d σ) i b
  change algebraMap (chartRing f n hn t v hv d σ)
      (chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S)
      (chartCoordinate f n hn t v hv d σ i b)*
      ((1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d] pair f n hn t v hv d i (σ i))=
    (1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d] pair f n hn t v hv d i b at h
  have hx : ((if b then sectionX f n hn t v hv d i else sectionY f n hn t v hv d i :
      overAlgebra f n hn t v hv d (Pi.single i (1:ℤ))):d.S)=
      pair f n hn t v hv d i b := by cases b <;> rfl
  have hm : ((selected f n hn t v hv d σ i):d.S)=pair f n hn t v hv d i (σ i) := by
    cases hs : σ i <;> simp only [selected,pair,hs,Bool.false_eq_true,↓reduceIte]
  rw [hx,hm]
  exact h
end


open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance tensorWorkAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance tensorWorkTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma weight_add (ms ns : Fin n → ℤ) : RootCoaction.weight f n hn t v hv d (ms+ns)=
    RootCoaction.weight f n hn t v hv d ms*RootCoaction.weight f n hn t v hv d ns := by
  simp only [RootCoaction.weight_eq,Pi.add_apply,zpow_add,Finset.prod_mul_distrib]

lemma mul_mem (ms ns : Fin n → ℤ) (x : overAlgebra f n hn t v hv d ms)
    (y : overAlgebra f n hn t v hv d ns) : (x:d.S)*(y:d.S) ∈ overAlgebra f n hn t v hv d (ms+ns) := by
  change (RootCoaction.weight f n hn t v hv d (ms+ns) : RootCoaction.T f n t v d)*
    RootCoaction.hom f n hn t v hv d ((x:d.S)*(y:d.S))=
      RootCoaction.right f n t v d ((x:d.S)*(y:d.S))
  rw [weight_add,Units.val_mul,map_mul,map_mul]
  have hx := member_eq f n hn t v hv d ms ((overAlgebraEquiv f n hn t v hv d ms) x)
  have hy := member_eq f n hn t v hv d ns ((overAlgebraEquiv f n hn t v hv d ns) y)
  change (RootCoaction.weight f n hn t v hv d ms : RootCoaction.T f n t v d)*
    RootCoaction.hom f n hn t v hv d (x:d.S)=RootCoaction.right f n t v d (x:d.S) at hx
  change (RootCoaction.weight f n hn t v hv d ns : RootCoaction.T f n t v d)*
    RootCoaction.hom f n hn t v hv d (y:d.S)=RootCoaction.right f n t v d (y:d.S) at hy
  calc
    _ = ((RootCoaction.weight f n hn t v hv d ms : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (x:d.S))*
        ((RootCoaction.weight f n hn t v hv d ns : RootCoaction.T f n t v d)*
          RootCoaction.hom f n hn t v hv d (y:d.S)) := by ring
    _ = _ := by rw [hx,hy]

def mulLinear (ms ns : Fin n → ℤ) :
    overAlgebra f n hn t v hv d ms →ₗ[algebra f n hn t v hv d]
      overAlgebra f n hn t v hv d ns →ₗ[algebra f n hn t v hv d]
        overAlgebra f n hn t v hv d (ms+ns) where
  toFun x := {
    toFun y := ⟨(x:d.S)*(y:d.S),mul_mem f n hn t v hv d ms ns x y⟩
    map_add' y z := Subtype.ext (mul_add _ _ _)
    map_smul' r y := Subtype.ext (by change (x:d.S)*((r:d.S)*(y:d.S))=(r:d.S)*((x:d.S)*(y:d.S));ring) }
  map_add' x y := by ext z;exact add_mul _ _ _
  map_smul' r x := by ext z;exact mul_assoc _ _ _

def mulTensor (ms ns : Fin n → ℤ) :
    overAlgebra f n hn t v hv d ms ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ns
      →ₗ[algebra f n hn t v hv d] overAlgebra f n hn t v hv d (ms+ns) :=
  TensorProduct.lift (mulLinear f n hn t v hv d ms ns)

def mulBaseSourceEquiv [Module.Flat A B] (ms ns : Fin n → ℤ) :
    d.S ⊗[algebra f n hn t v hv d]
      (overAlgebra f n hn t v hv d ms ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ns)
        ≃ₗ[d.S] d.S :=
  TensorProduct.AlgebraTensorModule.distribBaseChange _ _ _ _ ≪≫ₗ
    TensorProduct.congr (lineTensorEquiv f n hn t v hv d ms) (lineTensorEquiv f n hn t v hv d ns) ≪≫ₗ
      TensorProduct.lid d.S d.S

lemma mulBase_compat [Module.Flat A B] (ms ns : Fin n → ℤ) :
    (lineTensorEquiv f n hn t v hv d (ms+ns)).toLinearMap.comp
      ((mulTensor f n hn t v hv d ms ns).baseChange d.S)=
        (mulBaseSourceEquiv f n hn t v hv d ms ns).toLinearMap := by
  ext x y
  simp [mulTensor,mulLinear,mulBaseSourceEquiv,lineTensorEquiv,lineBaseMap]

lemma mulTensor_bijective [Module.FaithfullyFlat A B] (ms ns : Fin n → ℤ) :
    Function.Bijective (mulTensor f n hn t v hv d ms ns) := by
  let inst : Module.FaithfullyFlat (algebra f n hn t v hv d) d.S :=
    algebra_faithfullyFlat f n hn t v hv d
  apply FFTensorMaps.bijective (R := algebra f n hn t v hv d)
    (M := overAlgebra f n hn t v hv d ms ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ns)
    (N := overAlgebra f n hn t v hv d (ms+ns)) (Q := d.S) d.S
    (mulTensor f n hn t v hv d ms ns)
    (mulBaseSourceEquiv f n hn t v hv d ms ns)
    (lineTensorEquiv f n hn t v hv d (ms+ns))
  exact mulBase_compat f n hn t v hv d ms ns


def lineMulEquiv [Module.FaithfullyFlat A B] (ms ns : Fin n → ℤ) :
    overAlgebra f n hn t v hv d ms ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ns
      ≃ₗ[algebra f n hn t v hv d] overAlgebra f n hn t v hv d (ms+ns) :=
  LinearEquiv.ofBijective (mulTensor f n hn t v hv d ms ns)
    (mulTensor_bijective f n hn t v hv d ms ns)
end Lech.RootInvariants

end

end OAI
