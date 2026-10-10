import Mathlib
import OAI.RingTheory.Multiplicity.NativeDescentCanonicalAlg

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
namespace Lech.UniversalFactorMap
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Module.FaithfullyFlat A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance mapChartAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance mapChartScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable (σ : Fin n → Bool) (w : Tˣ) (a b : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))
  (hs : ∀ i,(if σ i then a i else b i)=1)

include hs in
lemma map_chart_selected : map f n hn t v hv d w a b hf (RootInvariants.chartFunction f n hn t v hv d σ)=(w:T) := by
  rw [map_chartFunction]
  simp only [hs,Finset.prod_const_one,mul_one]

 

def chartMap : RootInvariants.chartRing f n hn t v hv d σ →ₐ[A] T :=
  IsLocalization.Away.liftAlgHom (RootInvariants.chartFunction f n hn t v hv d σ)
    (f := map f n hn t v hv d w a b hf)
    (by rw [map_chart_selected f n hn t v hv d σ w a b hf hs];exact w.isUnit)

lemma chartMap_from (x : RootInvariants.algebra f n hn t v hv d) :
    chartMap f n hn t v hv d σ w a b hf hs
      (algebraMap (RootInvariants.algebra f n hn t v hv d) (RootInvariants.chartRing f n hn t v hv d σ) x)=
        map f n hn t v hv d w a b hf x := by
  exact IsLocalization.Away.lift_eq (S := RootInvariants.chartRing f n hn t v hv d σ)
    (g := (map f n hn t v hv d w a b hf).toRingHom)
    (RootInvariants.chartFunction f n hn t v hv d σ)
    (by change IsUnit (map f n hn t v hv d w a b hf (RootInvariants.chartFunction f n hn t v hv d σ))
        rw [map_chart_selected f n hn t v hv d σ w a b hf hs]
        exact w.isUnit) x

lemma chartMap_unit : Units.map (chartMap f n hn t v hv d σ w a b hf hs).toMonoidHom
    (RootInvariants.chartUnit f n hn t v hv d σ)=w := by
  apply Units.ext
  change chartMap f n hn t v hv d σ w a b hf hs
    (StandardFactorCharts.chartUnit (RootInvariants.algebra f n hn t v hv d) n
      (RootInvariants.chartFunction f n hn t v hv d) σ:RootInvariants.chartRing f n hn t v hv d σ)=(w:T)
  rw [StandardFactorCharts.chartUnit_val,chartMap_from,map_chart_selected f n hn t v hv d σ w a b hf hs]

include hs in
lemma update_product (i : Fin n) (κ : Bool) :
    (∏ j : Fin n,if Function.update σ i κ j then a j else b j)=if κ then a i else b i := by
  classical
  rw [Finset.prod_eq_single i]
  · rw [Function.update_self]
  · intro j _ hji
    rw [Function.update_of_ne hji]
    exact hs j
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

 

lemma chartMap_coordinate (i : Fin n) (κ : Bool) :
    chartMap f n hn t v hv d σ w a b hf hs (RootInvariants.chartCoordinate f n hn t v hv d σ i κ)=
      if κ then a i else b i := by
  have hinv : chartMap f n hn t v hv d σ w a b hf hs
      ((RootInvariants.chartUnit f n hn t v hv d σ)⁻¹).val=(w⁻¹).val := by
    have h := congrArg (fun u : Tˣ => (u⁻¹).val) (chartMap_unit f n hn t v hv d σ w a b hf hs)
    exact h
  change chartMap f n hn t v hv d σ w a b hf hs
    (algebraMap (RootInvariants.algebra f n hn t v hv d) (RootInvariants.chartRing f n hn t v hv d σ)
      (RootInvariants.chartFunction f n hn t v hv d (Function.update σ i κ))*
        ((RootInvariants.chartUnit f n hn t v hv d σ)⁻¹).val)=_
  rw [map_mul,chartMap_from,map_chartFunction,update_product n σ a b hs,hinv]
  rw [mul_right_comm,Units.mul_inv,one_mul]
end Lech.UniversalFactorMap


namespace Lech.UniversalFactorMap
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Module.FaithfullyFlat A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance mapChartUniqueAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance mapChartUniqueScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable (σ : Fin n → Bool) (w : Tˣ) (a b : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))
  (hs : ∀ i,(if σ i then a i else b i)=1)

lemma extend_map : extend f n hn t v hv d (map f n hn t v hv d w a b hf)=
    splittingMap f n hn t v hv d w a b hf :=
  extend_descended f n hn t v hv d _ _ _ _ _ _

 

lemma chartMap_unique (h : RootInvariants.chartRing f n hn t v hv d σ →ₐ[A] T)
    (ha : ∀ i,h (RootInvariants.chartCoordinate f n hn t v hv d σ i true)=a i)
    (hb : ∀ i,h (RootInvariants.chartCoordinate f n hn t v hv d σ i false)=b i) :
    h=chartMap f n hn t v hv d σ w a b hf hs := by
  let D := RootInvariants.algebra f n hn t v hv d
  let L := RootInvariants.chartRing f n hn t v hv d σ
  let g : D →ₐ[A] T := h.comp (IsScalarTower.toAlgHom A D L)
  let φ : d.S →ₐ[B] R (A := A) (B := B) (T := T) := extend f n hn t v hv d g
  let ψ : L →ₐ[A] R (A := A) (B := B) (T := T) := (includeT (A := A) (B := B)).comp h
  have hc (x : D) : ψ (algebraMap D L x)=φ (x:d.S) := by
    change includeT (h (algebraMap D L x))=extend f n hn t v hv d g (x:d.S)
    rw [extend_subtype]
    rfl
  have hr (i : Fin n) : φ (d.roots i)=
      -includeT (a i)*((denominator f n hn t v hv w a b hf i)⁻¹).val := by
    have hq (κ : Bool) := StandardFactorCharts.map_coordinate_relation D n
      (RootInvariants.pair f n hn t v hv d) (Units.map (algebraMap B d.S).toMonoidHom v)
      (RootInvariants.chartFunction f n hn t v hv d) (RootInvariants.pair_product f n hn t v hv d)
      σ ψ (φ.restrictScalars A) hc i κ
    have hx := hq true
    change includeT (h (RootInvariants.chartCoordinate f n hn t v hv d σ i true))*
      φ (RootInvariants.pair f n hn t v hv d i (σ i))=φ (-d.roots i) at hx
    rw [ha,map_neg] at hx
    have hy := hq false
    change includeT (h (RootInvariants.chartCoordinate f n hn t v hv d σ i false))*
      φ (RootInvariants.pair f n hn t v hv d i (σ i))=φ (1+algebraMap B d.S t*d.roots i) at hy
    rw [hb,map_add,map_one,map_mul,AlgHom.commutes] at hy
    exact StandardFactorCharts.normalized_root (φ (d.roots i)) (algebraMap B _ t)
      (includeT (a i)) (includeT (b i)) (φ (RootInvariants.pair f n hn t v hv d i (σ i)))
      (denominator f n hn t v hv w a b hf i) (denominator_val f n hn t v hv w a b hf i) hx hy
  have hg : g=map f n hn t v hv d w a b hf := by
    apply point_ext f n hn t v hv d
    intro i
    rw [extend_map,splittingMap_root]
    exact hr i
  have hh : h.toRingHom=(chartMap f n hn t v hv d σ w a b hf hs).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (RootInvariants.chartFunction f n hn t v hv d σ))
    ext x
    change g x=chartMap f n hn t v hv d σ w a b hf hs (algebraMap D L x)
    rw [chartMap_from,hg]
  exact AlgHom.ext (RingHom.congr_fun hh)

include hf hs in
 
theorem chart_universal : ∃! h : RootInvariants.chartRing f n hn t v hv d σ →ₐ[A] T,
    (∀ i,h (RootInvariants.chartCoordinate f n hn t v hv d σ i true)=a i) ∧
    (∀ i,h (RootInvariants.chartCoordinate f n hn t v hv d σ i false)=b i) := by
  refine ⟨chartMap f n hn t v hv d σ w a b hf hs,⟨?_,?_⟩,?_⟩
  · intro i
    exact chartMap_coordinate f n hn t v hv d σ w a b hf hs i true
  · intro i
    exact chartMap_coordinate f n hn t v hv d σ w a b hf hs i false
  · intro h hh
    exact chartMap_unique f n hn t v hv d σ w a b hf hs h hh.1 hh.2
end Lech.UniversalFactorMap


namespace Lech.UniversalFactorMap
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
lemma normalizedRatio_rescale {T : Type u} [CommRing T] (a : T) (c μ : Tˣ) :
    -((c:T)*a)*(↑((c*μ)⁻¹):T)= -a*(↑(μ⁻¹):T) := by
  simp only [mul_inv_rev,Units.val_mul]
  calc
    _ = (-a*↑(μ⁻¹))*((c:T)*↑(c⁻¹)) := by ring
    _ = _ := by rw [Units.mul_inv,mul_one]
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Module.FaithfullyFlat A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance rescaleAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance rescaleTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable (w w' : Tˣ) (a b a' b' : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))
  (hf' : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w':T)*∏ i,
    (MvPolynomial.C (a' i)*MvPolynomial.X 0+MvPolynomial.C (b' i)*MvPolynomial.X 1))
variable (c : Fin n → Tˣ) (ha : ∀ i,a' i=(c i:T)*a i) (hb : ∀ i,b' i=(c i:T)*b i)
include ha hb in
omit [Module.FaithfullyFlat A B] in
lemma denominator_rescale (i : Fin n) :
    denominator f n hn t v hv w' a' b' hf' i=
      Units.map (includeT (A:=A) (B:=B)).toMonoidHom (c i)*denominator f n hn t v hv w a b hf i := by
  apply Units.ext
  rw [Units.val_mul,denominator_val,denominator_val,ha,hb]
  change algebraMap B (R (A:=A) (B:=B) (T:=T)) t*includeT ((c i:T)*a i)+includeT ((c i:T)*b i)=
    includeT (A:=A) (B:=B) (c i:T)*(algebraMap B _ t*includeT (a i)+includeT (b i))
  simp only [map_mul]
  ring
include ha hb in
 

theorem map_rescale : map f n hn t v hv d w' a' b' hf'=map f n hn t v hv d w a b hf := by
  apply point_ext f n hn t v hv d
  intro i
  rw [extend_map,extend_map,splittingMap_root,splittingMap_root,
    denominator_rescale f n hn t v hv w w' a b a' b' hf hf' c ha hb i,ha,map_mul]
  exact normalizedRatio_rescale (includeT (a i))
    (Units.map (includeT (A:=A) (B:=B)).toMonoidHom (c i)) (denominator f n hn t v hv w a b hf i)
end Lech.UniversalFactorMap


namespace Lech.ProductLinearChart
open Polynomial
universe u v
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Fin n → Bool) (k : Fin (n+1))
variable {T : Type v} [CommRing T] [Algebra R T]

lemma dehomogenize_factorization (f : T[X]) (hf : f.natDegree≤n) (w : T)
    (x y : Fin n → T)
    (h : f.homogenize n=MvPolynomial.C w*∏ i,
      (MvPolynomial.C (x i)*MvPolynomial.X 0+MvPolynomial.C (y i)*MvPolynomial.X 1)) :
    f=C w*∏ i,(C (x i)*Polynomial.X+C (y i)) := by
  have hh := congrArg (MvPolynomial.aeval ![Polynomial.X, (1:T[X])]) h
  rw [Polynomial.aeval_homogenize_X_one f hf] at hh
  simpa only [map_mul,map_add,map_prod,MvPolynomial.aeval_C,MvPolynomial.aeval_X,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,mul_one,algebraMap_eq] using hh

variable (x y : Fin n → T) (hs : ∀ i,(if σ i then x i else y i)=1)
def eval : Ring R n →ₐ[R] T := MvPolynomial.aeval fun i => if σ i then y i else x i

include hs in
lemma eval_a (i : Fin n) : eval R n σ x y (a R n σ i)=x i := by
  have h := hs i
  cases hi : σ i <;> simp [a,eval,hi] at h ⊢
  exact h.symm
include hs in
lemma eval_b (i : Fin n) : eval R n σ x y (b R n σ i)=y i := by
  have h := hs i
  cases hi : σ i <;> simp [b,eval,hi] at h ⊢
  exact h.symm
include hs in
lemma eval_product : (product R n σ).map (eval R n σ x y).toRingHom=
    ∏ i,(C (x i)*Polynomial.X+C (y i)) := by
  simp only [product,Polynomial.map_prod,Polynomial.map_add,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_X,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
    eval_a R n σ x y hs,eval_b R n σ x y hs]

variable (c : UniversalCoefficientChart.Ring R n k →ₐ[R] T) (w : Tˣ)
variable (hf : ((UniversalCoefficientChart.form R n k).map c.toRingHom).homogenize n=
  MvPolynomial.C (w:T)*∏ i,(MvPolynomial.C (x i)*MvPolynomial.X 0+MvPolynomial.C (y i)*MvPolynomial.X 1))

include hs hf in
lemma eval_coeff : ∀ j : Fin (n+1),
    c (UniversalCoefficientChart.coefficient R n k j)=
      (w:T)*eval R n σ x y ((product R n σ).coeff j) := by
  have h := dehomogenize_factorization n _
    (natDegree_map_le.trans (UniversalCoefficientChart.form_degree R n k)) (w:T) x y hf
  rw [←eval_product R n σ x y hs] at h
  intro j
  have hh := congrArg (fun p : T[X] => p.coeff j) h
  simpa only [coeff_map,UniversalCoefficientChart.form_coeff,coeff_C_mul,
    AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hh

include hs hf in
lemma eval_self : eval R n σ x y ((product R n σ).coeff k)=(w⁻¹).val := by
  have h := eval_coeff R n σ k x y hs c w hf k
  rw [UniversalCoefficientChart.coefficient_self,map_one] at h
  calc
    eval R n σ x y ((product R n σ).coeff k)=(w⁻¹).val*((w:T)*eval R n σ x y ((product R n σ).coeff k)) := by simp
    _ = (w⁻¹).val := by rw [←h,mul_one]

def lift : chart R n σ k →ₐ[R] T :=
  IsLocalization.Away.liftAlgHom ((product R n σ).coeff k)
    (f := eval R n σ x y)
    (by rw [eval_self R n σ k x y hs c w hf];exact (w⁻¹).isUnit)

lemma lift_from (z : Ring R n) :
    lift R n σ k x y hs c w hf (algebraMap (Ring R n) (chart R n σ k) z)=eval R n σ x y z := by
  exact IsLocalization.Away.lift_eq (S := chart R n σ k)
    (g := (eval R n σ x y).toRingHom) ((product R n σ).coeff k)
    (by change IsUnit (eval R n σ x y ((product R n σ).coeff k));rw [eval_self R n σ k x y hs c w hf];exact (w⁻¹).isUnit) z

lemma lift_denominator : Units.map (lift R n σ k x y hs c w hf).toMonoidHom (denominator R n σ k)=w⁻¹ := by
  apply Units.ext
  change lift R n σ k x y hs c w hf (denominator R n σ k:chart R n σ k)=(w⁻¹).val
  rw [denominator_val,lift_from,eval_self R n σ k x y hs c w hf]

lemma lift_target : (lift R n σ k x y hs c w hf).comp (target R n σ k)=c := by
  apply UniversalCoefficientChart.ext
  intro j
  rw [AlgHom.comp_apply]
  change lift R n σ k x y hs c w hf
    (UniversalCoefficientChart.eval R n k (fun j => (normalized R n σ k).coeff j)
      (UniversalCoefficientChart.coefficient R n k j))=_
  rw [UniversalCoefficientChart.eval_coefficient R n k _ (normalized_self R n σ k) j,
    normalized,coeff_C_mul,coeff_map,map_mul,lift_from]
  have hinv := congrArg (fun u : Tˣ => (u⁻¹).val) (lift_denominator R n σ k x y hs c w hf)
  change lift R n σ k x y hs c w hf ((denominator R n σ k)⁻¹).val=(w⁻¹)⁻¹.val at hinv
  rw [hinv,inv_inv]
  exact (eval_coeff R n σ k x y hs c w hf j).symm

lemma lift_X (i : Fin n) :
    lift R n σ k x y hs c w hf
      (algebraMap (Ring R n) (chart R n σ k) (MvPolynomial.X i))=
        if σ i then y i else x i := by
  rw [lift_from]
  exact MvPolynomial.aeval_X _ _

lemma hom_ext {φ ψ : chart R n σ k →ₐ[R] T}
    (h : ∀ i,φ (algebraMap (Ring R n) (chart R n σ k) (MvPolynomial.X i))=
      ψ (algebraMap (Ring R n) (chart R n σ k) (MvPolynomial.X i))) : φ=ψ := by
  have hh : φ.comp (IsScalarTower.toAlgHom R (Ring R n) (chart R n σ k))=
      ψ.comp (IsScalarTower.toAlgHom R (Ring R n) (chart R n σ k)) :=
    MvPolynomial.algHom_ext h
  apply AlgHom.ext
  have hr : φ.toRingHom=ψ.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers ((product R n σ).coeff k))
    apply RingHom.ext
    intro z
    exact AlgHom.congr_fun hh z
  exact RingHom.congr_fun hr

end Lech.ProductLinearChart


namespace Lech.RootChartAtlas
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
abbrev A := UniversalCoefficientChart.Ring R n k
abbrev f := UniversalCoefficientChart.form R n k
abbrev hn : (f R n k).natDegree≤n := UniversalCoefficientChart.form_degree R n k
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
local instance mapChartAtlasAlgebra : Algebra (A R n k) d.S := Algebra.compHom d.S (algebraMap (A R n k) B)
local instance mapChartAtlasScalarTower : IsScalarTower (A R n k) B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable (σ : Fin n → Bool)
abbrev L := RootInvariants.chartRing (f R n k) n (hn R n k) t v hv d σ
abbrev H := ProductLinearChart.chart R n σ k
abbrev coordinate := RootInvariants.chartCoordinate (f R n k) n (hn R n k) t v hv d σ
abbrev w := RootInvariants.chartUnit (f R n k) n (hn R n k) t v hv d σ

local instance chartRAlgebra : Algebra R (L R n k t v hv d σ) :=
  Algebra.compHom (L R n k t v hv d σ) (algebraMap R (A R n k))
local instance chartRTower : IsScalarTower R (A R n k) (L R n k t v hv d σ) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := A R n k) (A := L R n k t v hv d σ)
    fun _ => rfl

lemma coord_selected (i : Fin n) :
    (if σ i then coordinate R n k t v hv d σ i true else coordinate R n k t v hv d σ i false)=1 := by
  have h := RootInvariants.chartCoordinate_selected (f R n k) n (hn R n k) t v hv d σ i
  cases hi : σ i <;> simpa only [hi,Bool.false_eq_true,↓reduceIte] using h

abbrev fromH_R : H R n k σ →ₐ[R] L R n k t v hv d σ :=
  ProductLinearChart.lift R n σ k
    (fun i => coordinate R n k t v hv d σ i true)
    (fun i => coordinate R n k t v hv d σ i false)
    (coord_selected R n k t v hv d σ)
    (IsScalarTower.toAlgHom R (A R n k) (L R n k t v hv d σ))
    (w R n k t v hv d σ)
    (RootInvariants.chart_factorization (f R n k) n (hn R n k) t v hv d σ)

def fromH : H R n k σ →ₐ[A R n k] L R n k t v hv d σ where
  toRingHom := (fromH_R R n k t v hv d σ).toRingHom
  commutes' a := AlgHom.congr_fun
    (ProductLinearChart.lift_target R n σ k _ _ (coord_selected R n k t v hv d σ)
      (IsScalarTower.toAlgHom R (A R n k) (L R n k t v hv d σ))
      (w R n k t v hv d σ)
      (RootInvariants.chart_factorization (f R n k) n (hn R n k) t v hv d σ)) a

lemma fromH_source (z : ProductLinearChart.Ring R n) :
    fromH R n k t v hv d σ (algebraMap (ProductLinearChart.Ring R n) (H R n k σ) z)=
      ProductLinearChart.eval R n σ
        (fun i => coordinate R n k t v hv d σ i true)
        (fun i => coordinate R n k t v hv d σ i false) z :=
  ProductLinearChart.lift_from R n σ k _ _ (coord_selected R n k t v hv d σ)
    (IsScalarTower.toAlgHom R (A R n k) (L R n k t v hv d σ))
    (w R n k t v hv d σ)
    (RootInvariants.chart_factorization (f R n k) n (hn R n k) t v hv d σ) z

lemma fromH_a (i : Fin n) :
    fromH R n k t v hv d σ (algebraMap (ProductLinearChart.Ring R n) (H R n k σ)
      (ProductLinearChart.a R n σ i))=coordinate R n k t v hv d σ i true := by
  rw [fromH_source,ProductLinearChart.eval_a R n σ _ _ (coord_selected R n k t v hv d σ)]
lemma fromH_b (i : Fin n) :
    fromH R n k t v hv d σ (algebraMap (ProductLinearChart.Ring R n) (H R n k σ)
      (ProductLinearChart.b R n σ i))=coordinate R n k t v hv d σ i false := by
  rw [fromH_source,ProductLinearChart.eval_b R n σ _ _ (coord_selected R n k t v hv d σ)]

lemma source_selected (i : Fin n) :
    (if σ i then algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.a R n σ i)
      else algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.b R n σ i))=1 := by
  have h := congrArg (algebraMap (ProductLinearChart.Ring R n) (H R n k σ)) (ProductLinearChart.selected R n σ i)
  cases hi : σ i <;> simpa only [hi,Bool.false_eq_true,↓reduceIte,map_one] using h

variable [Module.FaithfullyFlat (A R n k) B]

def toH : L R n k t v hv d σ →ₐ[A R n k] H R n k σ :=
  UniversalFactorMap.chartMap (f R n k) n (hn R n k) t v hv d σ
    ((ProductLinearChart.denominator R n σ k)⁻¹)
    (fun i => algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.a R n σ i))
    (fun i => algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.b R n σ i))
    (ProductLinearChart.target_factorization R n σ k)
    (source_selected R n k σ)

lemma toH_coordinate (i : Fin n) (b : Bool) :
    toH R n k t v hv d σ (coordinate R n k t v hv d σ i b)=
      if b then algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.a R n σ i)
        else algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.b R n σ i) :=
  UniversalFactorMap.chartMap_coordinate (f R n k) n (hn R n k) t v hv d σ _ _ _ _ _ i b

lemma fromH_toH : (fromH R n k t v hv d σ).comp (toH R n k t v hv d σ)=AlgHom.id (A R n k) _ := by
  have he (g : L R n k t v hv d σ →ₐ[A R n k] L R n k t v hv d σ)
      (ha : ∀ i,g (coordinate R n k t v hv d σ i true)=coordinate R n k t v hv d σ i true)
      (hb : ∀ i,g (coordinate R n k t v hv d σ i false)=coordinate R n k t v hv d σ i false) :=
    UniversalFactorMap.chartMap_unique (f R n k) n (hn R n k) t v hv d σ
      (w R n k t v hv d σ) _ _
      (RootInvariants.chart_factorization (f R n k) n (hn R n k) t v hv d σ)
      (coord_selected R n k t v hv d σ) g ha hb
  apply (he _ ?_ ?_).trans (he (AlgHom.id (A R n k) _) (fun _ => rfl) (fun _ => rfl)).symm
  · intro i
    rw [AlgHom.comp_apply,toH_coordinate]
    exact fromH_a R n k t v hv d σ i
  · intro i
    rw [AlgHom.comp_apply,toH_coordinate]
    exact fromH_b R n k t v hv d σ i

omit [Module.FaithfullyFlat (A R n k) B] in
lemma fromH_X (i : Fin n) :
    fromH R n k t v hv d σ (algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (MvPolynomial.X i))=
      if σ i then coordinate R n k t v hv d σ i false else coordinate R n k t v hv d σ i true :=
  ProductLinearChart.lift_X R n σ k _ _ (coord_selected R n k t v hv d σ)
    (IsScalarTower.toAlgHom R (A R n k) (L R n k t v hv d σ))
    (w R n k t v hv d σ)
    (RootInvariants.chart_factorization (f R n k) n (hn R n k) t v hv d σ) i

lemma toH_fromH : (toH R n k t v hv d σ).comp (fromH R n k t v hv d σ)=AlgHom.id (A R n k) _ := by
  have h : ((toH R n k t v hv d σ).comp (fromH R n k t v hv d σ)).restrictScalars R=
      (AlgHom.id (A R n k) (H R n k σ)).restrictScalars R := by
    apply ProductLinearChart.hom_ext
    intro i
    change toH R n k t v hv d σ (fromH R n k t v hv d σ
      (algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (MvPolynomial.X i)))=
      algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (MvPolynomial.X i)
    rw [fromH_X]
    cases hi : σ i <;>
      simp only [hi,Bool.false_eq_true,↓reduceIte,toH_coordinate,ProductLinearChart.a,ProductLinearChart.b]
  apply AlgHom.ext
  intro x
  have hh := AlgHom.congr_fun h x
  exact hh

 

def equiv : L R n k t v hv d σ ≃ₐ[A R n k] H R n k σ :=
  AlgEquiv.ofAlgHom (toH R n k t v hv d σ) (fromH R n k t v hv d σ)
    (toH_fromH R n k t v hv d σ) (fromH_toH R n k t v hv d σ)

end Lech.RootChartAtlas
end
end

end OAI
