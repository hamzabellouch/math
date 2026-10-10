import Mathlib
import OAI.RingTheory.Multiplicity.RootCoactionT

namespace OAI

noncomputable section

namespace Lech.RootInvariants

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance weightZeroBaseAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance weightZeroBaseScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma weight_zero : RootCoaction.weight f n hn t v hv d (0 : Fin n → ℤ)=1 := by
  rw [RootCoaction.weight_eq]
  simp

lemma linear_zero : RootCoaction.linear f n hn t v hv d (0 : Fin n → ℤ)=
    (RootCoaction.hom f n hn t v hv d).toLinearMap := by
  ext x
  rw [RootCoaction.linear_apply,weight_zero]
  simp


def algebra : Subalgebra A d.S :=
  AlgHom.equalizer ((RootCoaction.hom f n hn t v hv d).restrictScalars A)
    (RootCoaction.right f n t v d)

lemma algebra_toSubmodule : (algebra f n hn t v hv d).toSubmodule=
    module f n hn t v hv d (0 : Fin n → ℤ) := by
  ext x
  change (RootCoaction.hom f n hn t v hv d x=RootCoaction.right f n t v d x) ↔
    RootCoaction.linear f n hn t v hv d 0 x=(1:B) ⊗ₜ[A] x
  rw [linear_zero]
  rfl

def algebraModuleEquiv : algebra f n hn t v hv d ≃ₗ[A] module f n hn t v hv d (0 : Fin n → ℤ) :=
  LinearEquiv.ofEq _ _ (algebra_toSubmodule f n hn t v hv d)

lemma algebra_finitePresentation [Module.FaithfullyFlat A B] :
    Module.FinitePresentation A (algebra f n hn t v hv d) := by
  let := finitePresentation f n hn t v hv d (0 : Fin n → ℤ)
  exact Module.FinitePresentation.of_equiv (algebraModuleEquiv f n hn t v hv d).symm

lemma algebra_flat [Module.FaithfullyFlat A B] :
    Module.Flat A (algebra f n hn t v hv d) := by
  let := flat f n hn t v hv d (0 : Fin n → ℤ)
  exact Module.Flat.of_linearEquiv (algebraModuleEquiv f n hn t v hv d)

lemma algebra_rankAtStalk [Module.FaithfullyFlat A B] (p : PrimeSpectrum A) :
    Module.rankAtStalk (algebra f n hn t v hv d) p=n.factorial := by
  rw [Module.rankAtStalk_eq_of_equiv (algebraModuleEquiv f n hn t v hv d)]
  exact rankAtStalk f n hn t v hv d 0 p

 
def algebraBaseMap : B ⊗[A] algebra f n hn t v hv d →ₐ[B] d.S :=
  Algebra.TensorProduct.lift (Algebra.ofId B d.S) (algebra f n hn t v hv d).val
    (fun _ _ => Commute.all _ _)

lemma algebraBaseMap_linear [Module.Flat A B] :
    (algebraBaseMap f n hn t v hv d).toLinearMap=
      (tensorEquiv f n hn t v hv d (0 : Fin n → ℤ)).toLinearMap.comp
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
          (algebraModuleEquiv f n hn t v hv d)).toLinearMap := by
  ext x
  change algebraMap B d.S 1*(x:d.S)=(1:B) • (x:d.S)
  rw [map_one,one_mul,one_smul]


def algebraTensorEquiv [Module.Flat A B] :
    B ⊗[A] algebra f n hn t v hv d ≃ₐ[B] d.S :=
  AlgEquiv.ofBijective (algebraBaseMap f n hn t v hv d) (by
    change Function.Bijective (algebraBaseMap f n hn t v hv d).toLinearMap
    rw [algebraBaseMap_linear]
    exact (tensorEquiv f n hn t v hv d 0).bijective.comp
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
        (algebraModuleEquiv f n hn t v hv d)).bijective)
end


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance weightZeroRightBaseAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance weightZeroRightBaseScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

def algebraBaseMapRight : algebra f n hn t v hv d ⊗[A] B →ₐ[algebra f n hn t v hv d] d.S :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom A B d.S)
    (fun _ _ => Commute.all _ _)

lemma algebraBaseMapRight_eq : (algebraBaseMapRight f n hn t v hv d).restrictScalars A=
    ((algebraBaseMap f n hn t v hv d).restrictScalars A).comp
      (Algebra.TensorProduct.comm A (algebra f n hn t v hv d) B).toAlgHom := by
  ext x <;> simp [algebraBaseMapRight,algebraBaseMap]

def algebraTensorEquivRight [Module.Flat A B] :
    algebra f n hn t v hv d ⊗[A] B ≃ₐ[algebra f n hn t v hv d] d.S :=
  AlgEquiv.ofBijective (algebraBaseMapRight f n hn t v hv d) (by
    change Function.Bijective ((algebraBaseMapRight f n hn t v hv d).restrictScalars A)
    rw [algebraBaseMapRight_eq]
    exact (algebraTensorEquiv f n hn t v hv d).bijective.comp
      (Algebra.TensorProduct.comm A (algebra f n hn t v hv d) B).bijective)

lemma algebra_faithfullyFlat [Module.FaithfullyFlat A B] :
    Module.FaithfullyFlat (algebra f n hn t v hv d) d.S := by
  let : Module.FaithfullyFlat (algebra f n hn t v hv d) (algebra f n hn t v hv d ⊗[A] B) := inferInstance
  exact Module.FaithfullyFlat.of_linearEquiv _ _ (algebraTensorEquivRight f n hn t v hv d).symm.toLinearEquiv
end


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance weightZeroOverAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance weightZeroOverScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

def overAlgebra (ms : Fin n → ℤ) : Submodule (algebra f n hn t v hv d) d.S where
  carrier := module f n hn t v hv d ms
  zero_mem' := (module f n hn t v hv d ms).zero_mem
  add_mem' := (module f n hn t v hv d ms).add_mem
  smul_mem' a x hx := by
    change (RootCoaction.weight f n hn t v hv d ms : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d ((a:d.S)*x)=RootCoaction.right f n t v d ((a:d.S)*x)
    have ha : RootCoaction.hom f n hn t v hv d (a:d.S)=RootCoaction.right f n t v d (a:d.S) := a.property
    change (RootCoaction.weight f n hn t v hv d ms : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d x=RootCoaction.right f n t v d x at hx
    rw [map_mul,map_mul,ha,← mul_assoc,mul_comm _ (RootCoaction.right f n t v d (a:d.S)),mul_assoc,hx]

def overAlgebraEquiv (ms : Fin n → ℤ) :
    overAlgebra f n hn t v hv d ms ≃ₗ[A] module f n hn t v hv d ms :=
  LinearEquiv.refl A _

 
def lineBaseMap (ms : Fin n → ℤ) :
    d.S ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ms →ₗ[d.S] d.S :=
  (overAlgebra f n hn t v hv d ms).subtype.liftBaseChange d.S


def lineBaseSourceEquiv [Module.Flat A B] (ms : Fin n → ℤ) :
    d.S ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ms ≃ₗ[A]
      B ⊗[A] module f n hn t v hv d ms :=
  (((TensorProduct.congr (algebraTensorEquivRight f n hn t v hv d).symm.toLinearEquiv
      (LinearEquiv.refl _ _)) ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.rightComm A (algebra f n hn t v hv d)
      (algebra f n hn t v hv d) (algebra f n hn t v hv d) (overAlgebra f n hn t v hv d ms) B).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (TensorProduct.lid _ _) (LinearEquiv.refl A B)).restrictScalars A) ≪≫ₗ
    TensorProduct.comm A _ B ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl A B) (overAlgebraEquiv f n hn t v hv d ms)

lemma lineBaseSourceEquiv_symm_tmul [Module.Flat A B] (ms : Fin n → ℤ)
    (b : B) (x : module f n hn t v hv d ms) :
    (lineBaseSourceEquiv f n hn t v hv d ms).symm (b ⊗ₜ[A] x)=
      algebraMap B d.S b ⊗ₜ[algebra f n hn t v hv d]
        (overAlgebraEquiv f n hn t v hv d ms).symm x := by
  simp [lineBaseSourceEquiv,algebraTensorEquivRight,algebraBaseMapRight]

lemma lineBaseMap_comp [Module.Flat A B] (ms : Fin n → ℤ) :
    ((lineBaseMap f n hn t v hv d ms).restrictScalars A).comp
      (lineBaseSourceEquiv f n hn t v hv d ms).symm.toLinearMap=
        (tensorEquiv f n hn t v hv d ms).toLinearMap.restrictScalars A := by
  ext b x
  change (lineBaseMap f n hn t v hv d ms)
    ((lineBaseSourceEquiv f n hn t v hv d ms).symm (b ⊗ₜ[A] x))=
      (tensorEquiv f n hn t v hv d ms) (b ⊗ₜ[A] x)
  rw [lineBaseSourceEquiv_symm_tmul]
  change algebraMap B d.S b*(x:d.S)=b • (x:d.S)
  exact (Algebra.smul_def b (x:d.S)).symm

def lineTensorEquiv [Module.Flat A B] (ms : Fin n → ℤ) :
    d.S ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ms ≃ₗ[d.S] d.S :=
  LinearEquiv.ofBijective (lineBaseMap f n hn t v hv d ms) (by
    have h : (lineBaseMap f n hn t v hv d ms).restrictScalars A=
        ((tensorEquiv f n hn t v hv d ms).toLinearMap.restrictScalars A).comp
          (lineBaseSourceEquiv f n hn t v hv d ms).toLinearMap := by
      have h := congrArg (fun l => l.comp (lineBaseSourceEquiv f n hn t v hv d ms).toLinearMap)
        (lineBaseMap_comp f n hn t v hv d ms)
      simpa only [LinearMap.comp_assoc,LinearEquiv.comp_coe,LinearEquiv.self_trans_symm,
        LinearEquiv.refl_toLinearMap,LinearMap.comp_id] using h
    change Function.Bijective ((lineBaseMap f n hn t v hv d ms).restrictScalars A)
    rw [h]
    exact (tensorEquiv f n hn t v hv d ms).bijective.comp
      (lineBaseSourceEquiv f n hn t v hv d ms).bijective)
end


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance weightZeroSectionsAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance weightZeroSectionsScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma weight_single (i : Fin n) : RootCoaction.weight f n hn t v hv d (Pi.single i (1:ℤ))=
    RootCoaction.denominator f n hn t v hv d i := by
  classical
  rw [RootCoaction.weight_eq]
  simp [Pi.single_apply]

lemma denominator_hom_root (i : Fin n) :
    (RootCoaction.denominator f n hn t v hv d i : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (d.roots i)=RootCoaction.roots f n t v d i := by
  rw [RootCoaction.hom_root,RootGluing.rootShift,
    ← RootCoaction.denominator_val f n hn t v hv d i,Ring.inverse_unit]
  rw [mul_comm _ (RootCoaction.roots f n t v d i*_),mul_assoc,Units.inv_mul,mul_one]


def sectionX (i : Fin n) : overAlgebra f n hn t v hv d (Pi.single i (1:ℤ)) :=
  ⟨-d.roots i, by
    change (RootCoaction.weight f n hn t v hv d (Pi.single i (1:ℤ)) : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (-d.roots i)=RootCoaction.right f n t v d (-d.roots i)
    rw [weight_single,map_neg,map_neg,mul_neg,denominator_hom_root]
    rfl⟩

 
def sectionY (i : Fin n) : overAlgebra f n hn t v hv d (Pi.single i (1:ℤ)) :=
  ⟨1+algebraMap B d.S t*d.roots i, by
    change (RootCoaction.weight f n hn t v hv d (Pi.single i (1:ℤ)) : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (1+algebraMap B d.S t*d.roots i)=
        RootCoaction.right f n t v d (1+algebraMap B d.S t*d.roots i)
    simp only [weight_single,map_add,map_one,map_mul,AlgHom.commutes]
    change (RootCoaction.denominator f n hn t v hv d i : RootCoaction.T f n t v d)*
      (1+algebraMap B (RootCoaction.T f n t v d) t*RootCoaction.hom f n hn t v hv d (d.roots i))=
        1+RootCoaction.coord f n t v d*RootCoaction.roots f n t v d i
    calc
      _ = (RootCoaction.denominator f n hn t v hv d i : RootCoaction.T f n t v d)+
          algebraMap B (RootCoaction.T f n t v d) t*
            ((RootCoaction.denominator f n hn t v hv d i : RootCoaction.T f n t v d)*
              RootCoaction.hom f n hn t v hv d (d.roots i)) := by ring
      _ = _ := by rw [denominator_hom_root,RootCoaction.denominator_val];ring⟩

lemma section_chart_generator (i : Fin n) :
    (sectionY f n hn t v hv d i:d.S)+algebraMap B d.S t*(sectionX f n hn t v hv d i:d.S)=1 := by
  change (1+algebraMap B d.S t*d.roots i)+algebraMap B d.S t*(-d.roots i)=1
  ring
end


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance weightZeroDiagonalAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance weightZeroDiagonalScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma leftUnit_eq : Units.map (algebraMap B (RootCoaction.T f n t v d)).toMonoidHom v=
    RootCoaction.unit f n t v d*RootCoaction.weight f n hn t v hv d (fun _ => (1:ℤ)) := by
  apply Units.ext
  simp only [Units.coe_map,Units.val_mul,RootCoaction.weight_eq,zpow_one,Units.coe_prod]
  have h := RootTransitions.value_product
    ((f.map (algebraMap A B)).map (algebraMap B (RootCoaction.T f n t v d)))
    ((natDegree_map_le.trans natDegree_map_le).trans hn)
    (RootCoaction.coord f n t v d) (algebraMap B (RootCoaction.T f n t v d) t)
    (RootCoaction.unit f n t v d) (RootCoaction.roots f n t v d) (RootCoaction.factorization f n t v d)
  have he := RootTransport.mapped_eval (f.map (algebraMap A B)) t v hv
    (C := RootCoaction.T f n t v d)
  rw [he] at h
  simpa only [RootCoaction.denominator_val, Units.coe_map] using h


def diagonalSection : overAlgebra f n hn t v hv d (fun _ => (1:ℤ)) :=
  ⟨algebraMap B d.S (v⁻¹:Bˣ),by
    change (RootCoaction.weight f n hn t v hv d (fun _ => (1:ℤ)) : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (algebraMap B d.S (v⁻¹:Bˣ))=
        RootCoaction.right f n t v d (algebraMap B d.S (v⁻¹:Bˣ))
    rw [AlgHom.commutes]
    have hu := leftUnit_eq f n hn t v hv d
    have he : RootCoaction.weight f n hn t v hv d (fun _ => (1:ℤ))*
        (Units.map (algebraMap B (RootCoaction.T f n t v d)).toMonoidHom v)⁻¹=
          (RootCoaction.unit f n t v d)⁻¹ := by
      rw [hu,mul_inv_rev,← mul_assoc,mul_inv_cancel,one_mul]
    have hc := congrArg (fun u : (RootCoaction.T f n t v d)ˣ => (u:RootCoaction.T f n t v d)) he
    exact hc⟩

lemma diagonalSection_isUnit : IsUnit (diagonalSection f n hn t v hv d:d.S) :=
  Units.isUnit (Units.map (algebraMap B d.S).toMonoidHom v⁻¹)
end


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance weightZeroBinaryFormAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance weightZeroBinaryFormScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl


lemma sections_binary_form :
    MvPolynomial.C (diagonalSection f n hn t v hv d:d.S)*
      MvPolynomial.map (algebraMap A d.S) (f.homogenize n)=
        ∏ i : Fin n, (MvPolynomial.C (sectionX f n hn t v hv d i:d.S)*MvPolynomial.X 0+
          MvPolynomial.C (sectionY f n hn t v hv d i:d.S)*MvPolynomial.X 1) := by
  have hs : BinaryChange.normalized (f.map (algebraMap A d.S)) n
      (algebraMap B d.S t) (Units.map (algebraMap B d.S).toMonoidHom v)=
        ∏ i, (Polynomial.X-C (d.roots i)) := by
    have hh := RootGluing.mapped_factorization (f.map (algebraMap A B)) n t v d
    have hp : (f.map (algebraMap A B)).map (algebraMap B d.S)=f.map (algebraMap A d.S) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq A B d.S]
    have he := congrArg (fun p : d.S[X] => BinaryChange.normalized p n
      (algebraMap B d.S t) (Units.map (algebraMap B d.S).toMonoidHom v)) hp
    exact he.symm.trans hh
  have he := BinaryChange.binary_factorization (f.map (algebraMap A d.S)) n
    (algebraMap B d.S t) (Units.map (algebraMap B d.S).toMonoidHom v) d.roots hs
  rw [Polynomial.homogenize_map] at he
  rw [he]
  change MvPolynomial.C (algebraMap B d.S (v⁻¹:Bˣ))*
    (MvPolynomial.C (algebraMap B d.S (v:B))*_)=_
  rw [← mul_assoc,← MvPolynomial.C_mul,← map_mul,Units.inv_mul,map_one,map_one,one_mul]
  rfl
end


open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance weightZeroProductSectionAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance weightZeroProductSectionScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

 
def selected (σ : Fin n → Bool) (i : Fin n) :
    overAlgebra f n hn t v hv d (Pi.single i (1:ℤ)) :=
  if σ i then sectionX f n hn t v hv d i else sectionY f n hn t v hv d i


def productSection (σ : Fin n → Bool) :
    overAlgebra f n hn t v hv d (fun _ => (1:ℤ)) :=
  ⟨∏ i,(selected f n hn t v hv d σ i:d.S),by
    change (RootCoaction.weight f n hn t v hv d (fun _ => (1:ℤ)):RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (∏ i,(selected f n hn t v hv d σ i:d.S))=
        RootCoaction.right f n t v d (∏ i,(selected f n hn t v hv d σ i:d.S))
    simp only [RootCoaction.weight_eq,zpow_one,Units.coe_prod,map_prod,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hx := (selected f n hn t v hv d σ i).property
    change (RootCoaction.weight f n hn t v hv d (Pi.single i (1:ℤ)):RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (selected f n hn t v hv d σ i:d.S)=
        RootCoaction.right f n t v d (selected f n hn t v hv d σ i:d.S) at hx
    rw [weight_single] at hx
    exact hx⟩


def chartFunction (σ : Fin n → Bool) : algebra f n hn t v hv d :=
  ⟨algebraMap B d.S (v:B)*(productSection f n hn t v hv d σ:d.S),by
    change RootCoaction.hom f n hn t v hv d _=RootCoaction.right f n t v d _
    rw [map_mul,map_mul,AlgHom.commutes]
    have hu := congrArg (fun u : (RootCoaction.T f n t v d)ˣ => (u:RootCoaction.T f n t v d))
      (leftUnit_eq f n hn t v hv d)
    change algebraMap B (RootCoaction.T f n t v d) (v:B)=
      RootCoaction.right f n t v d (algebraMap B d.S (v:B))*
        (RootCoaction.weight f n hn t v hv d (fun _ => (1:ℤ)):RootCoaction.T f n t v d) at hu
    rw [hu,mul_assoc]
    exact congrArg (_ * ·) (member_eq f n hn t v hv d _
      (overAlgebraEquiv f n hn t v hv d _ (productSection f n hn t v hv d σ)))⟩

lemma chartFunction_val (σ : Fin n → Bool) :
    (chartFunction f n hn t v hv d σ:d.S)=
      algebraMap B d.S (v:B)*∏ i,(selected f n hn t v hv d σ i:d.S) := rfl


lemma chartFunctions_span [Module.FaithfullyFlat A B] :
    Ideal.span (Set.range (chartFunction f n hn t v hv d))=⊤ := by
  classical
  let R := algebra f n hn t v hv d
  let I : Ideal R := Ideal.span (Set.range (chartFunction f n hn t v hv d))
  let J := I.map (algebraMap R d.S)
  let : Module.FaithfullyFlat R d.S := algebra_faithfullyFlat f n hn t v hv d
  have hp (σ : Fin n → Bool) : (∏ i,(selected f n hn t v hv d σ i:d.S))∈J := by
    have hq : (chartFunction f n hn t v hv d σ:d.S)∈J :=
      Ideal.mem_map_of_mem (algebraMap R d.S) (show chartFunction f n hn t v hv d σ∈I from
        Ideal.subset_span (Set.mem_range_self σ))
    have hm := J.mul_mem_left (algebraMap B d.S (v⁻¹:Bˣ)) hq
    simpa only [chartFunction_val,← mul_assoc,← map_mul,Units.inv_mul,map_one,one_mul] using hm
  have he : (∏ i : Fin n,∑ b : Bool,
      (if b then algebraMap B d.S t else 1)*(selected f n hn t v hv d (fun _ => b) i:d.S))=1 := by
    apply Finset.prod_eq_one
    intro i _
    simpa only [Fintype.sum_bool,selected,Bool.false_eq_true,↓reduceIte,one_mul,add_comm]
      using section_chart_generator f n hn t v hv d i
  rw [Fintype.prod_sum] at he
  have h1 : (1:d.S)∈J := by
    rw [← he]
    apply J.sum_mem
    intro σ _
    simp only [selected] at hp ⊢
    rw [Finset.prod_mul_distrib]
    exact J.mul_mem_left _ (hp σ)
  have hJ : J=⊤ := (Ideal.eq_top_iff_one J).mpr h1
  have hc := I.comap_map_eq_self_of_faithfullyFlat (B := d.S)
  change J.comap (algebraMap R d.S)=I at hc
  rw [hJ,Ideal.comap_top] at hc
  exact hc.symm

end Lech.RootInvariants

end

end OAI
