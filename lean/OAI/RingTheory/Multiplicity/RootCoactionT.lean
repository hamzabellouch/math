import Mathlib
import OAI.RingTheory.Multiplicity.RootBundleChartsDenominator

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
namespace Lech.RootCoaction

section

section

section
open Polynomial Lech.RootGluing
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

local instance : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

abbrev T := B ⊗[A] d.S

def right : d.S →ₐ[A] T f n t v d := Algebra.TensorProduct.includeRight

def coord : T f n t v d := right f n t v d (algebraMap B d.S t)
def unit : (T f n t v d)ˣ := Units.map (right f n t v d).toMonoidHom
    (Units.map (algebraMap B d.S).toMonoidHom v)
def roots (i : Fin n) : T f n t v d := right f n t v d (d.roots i)

lemma coeff_poly :
    (f.map (algebraMap A B)).map (algebraMap B (T f n t v d)) =
      ((f.map (algebraMap A B)).map (algebraMap B d.S)).map (right f n t v d).toRingHom := by
  simp only [Polynomial.map_map]
  congr 1
  rw [← IsScalarTower.algebraMap_eq A B (T f n t v d),
    ← IsScalarTower.algebraMap_eq A B d.S]
  exact (AlgHom.comp_algebraMap (right f n t v d)).symm

lemma factorization :
    BinaryChange.normalized ((f.map (algebraMap A B)).map (algebraMap B (T f n t v d))) n
      (coord f n t v d) (unit f n t v d)=∏ i,(Polynomial.X-Polynomial.C (roots f n t v d i)) := by
  rw [coeff_poly]
  have h := congrArg (Polynomial.map (right f n t v d).toRingHom)
    (RootGluing.mapped_factorization (f.map (algebraMap A B)) n t v d)
  simp only [BinaryCover.map_normalized,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,
    Polynomial.map_C,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] at h
  simp only [coord,unit,roots,AlgHom.toRingHom_eq_coe]
  exact h


def hom : d.S →ₐ[B] T f n t v d :=
  RootTransport.hom (f.map (algebraMap A B)) n (natDegree_map_le.trans hn) t v hv d
    (coord f n t v d) (unit f n t v d) (roots f n t v d) (factorization f n t v d)

lemma hom_root (i : Fin n) : hom f n hn t v hv d (d.roots i)=
    rootShift (coord f n t v d-algebraMap B (T f n t v d) t) (roots f n t v d i) :=
  RootTransport.hom_root _ _ _ _ _ _ _ _ _ _ _ i

include hn hv in
lemma denominator_unit (i : Fin n) :
    IsUnit (1+(coord f n t v d-algebraMap B (T f n t v d) t)*roots f n t v d i) :=
  RootTransport.denominator_unit _ _ (natDegree_map_le.trans hn) _ _ hv _ _ _
    (factorization f n t v d) i

def weight (ms : Fin n → ℤ) : (T f n t v d)ˣ :=
  RootTransport.weight (f.map (algebraMap A B)) n (natDegree_map_le.trans hn) t v hv
    (coord f n t v d) (unit f n t v d) (roots f n t v d) (factorization f n t v d) ms

def linear (ms : Fin n → ℤ) : d.S →ₗ[B] T f n t v d :=
  RootTransport.linear (f.map (algebraMap A B)) n (natDegree_map_le.trans hn) t v hv d
    (coord f n t v d) (unit f n t v d) (roots f n t v d) (factorization f n t v d) ms

lemma linear_apply (ms : Fin n → ℤ) (x : d.S) :
    linear f n hn t v hv d ms x=(weight f n hn t v hv d ms:T f n t v d)*hom f n hn t v hv d x := rfl

 
def counit : T f n t v d →ₐ[B] d.S :=
  Algebra.TensorProduct.lift (Algebra.ofId B d.S) (AlgHom.id A d.S) (fun _ _ => Commute.all _ _)

lemma counit_right (x : d.S) : counit f n t v d (right f n t v d x)=x := by
  simp [counit,right]

lemma counit_hom : (counit f n t v d).comp (hom f n hn t v hv d)=AlgHom.id B d.S := by
  apply d.hom_ext
  intro i
  rw [AlgHom.comp_apply,hom_root]
  change (counit f n t v d).toRingHom (rootShift _ _)=_
  rw [map_rootShift _ _ _ (denominator_unit f n hn t v hv d i)]
  change rootShift ((counit f n t v d) (coord f n t v d-algebraMap B (T f n t v d) t))
    ((counit f n t v d) (roots f n t v d i))=_
  simp only [map_sub,coord,roots,counit_right,AlgHom.commutes,sub_self,rootShift,zero_mul,
    add_zero,Ring.inverse_one,mul_one,AlgHom.id_apply]
end


open Polynomial Lech.RootGluing
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

abbrev U := B ⊗[A] T f n t v d

def right₂ : T f n t v d →ₐ[A] U f n t v d := Algebra.TensorProduct.includeRight

def delta : T f n t v d →ₐ[B] U f n t v d :=
  Algebra.TensorProduct.map (AlgHom.id B B) (right f n t v d)

def psi : T f n t v d →ₐ[B] U f n t v d :=
  Algebra.TensorProduct.map (AlgHom.id B B) ((hom f n hn t v hv d).restrictScalars A)

lemma delta_right (x : d.S) : delta f n t v d (right f n t v d x)=
    right₂ f n t v d (right f n t v d x) := by
  simp [delta,right,right₂]

lemma psi_right (x : d.S) : psi f n hn t v hv d (right f n t v d x)=
    right₂ f n t v d (hom f n hn t v hv d x) := by
  simp [psi,right,right₂]

lemma psi_coord : psi f n hn t v hv d (coord f n t v d)=
    right₂ f n t v d (algebraMap B (T f n t v d) t) := by
  rw [coord,psi_right,AlgHom.commutes]

lemma psi_roots (i : Fin n) : psi f n hn t v hv d (roots f n t v d i)=
    rootShift (right₂ f n t v d (coord f n t v d)-right₂ f n t v d (algebraMap B (T f n t v d) t))
      (right₂ f n t v d (roots f n t v d i)) := by
  rw [roots,psi_right,hom_root]
  change (right₂ f n t v d).toRingHom (rootShift _ _)=_
  rw [map_rootShift _ _ _ (denominator_unit f n hn t v hv d i)]
  rw [map_sub]
  rfl

lemma delta_hom : (delta f n t v d).comp (hom f n hn t v hv d)=
    (psi f n hn t v hv d).comp (hom f n hn t v hv d) := by
  apply d.hom_ext
  intro i
  simp only [AlgHom.comp_apply,hom_root]
  change (delta f n t v d).toRingHom (rootShift _ _) =
    (psi f n hn t v hv d).toRingHom (rootShift _ _)
  rw [map_rootShift _ _ _ (denominator_unit f n hn t v hv d i),
    map_rootShift _ _ _ (denominator_unit f n hn t v hv d i)]
  change rootShift ((delta f n t v d) (_-_)) ((delta f n t v d) (roots f n t v d i))=
    rootShift ((psi f n hn t v hv d) (_-_)) ((psi f n hn t v hv d) (roots f n t v d i))
  rw [map_sub,map_sub,AlgHom.commutes,AlgHom.commutes,psi_coord,psi_roots]
  have ha : IsUnit (1+(right₂ f n t v d (coord f n t v d)-
      right₂ f n t v d (algebraMap B (T f n t v d) t))*right₂ f n t v d (roots f n t v d i)) := by
    have h := (denominator_unit f n hn t v hv d i).map (right₂ f n t v d).toMonoidHom
    change IsUnit (right₂ f n t v d (1+_ * _)) at h
    simpa only [map_add,map_one,map_mul,map_sub] using h
  have hab : IsUnit (1+(right₂ f n t v d (coord f n t v d)-
      algebraMap B (U f n t v d) t)*right₂ f n t v d (roots f n t v d i)) := by
    have h := (denominator_unit f n hn t v hv d i).map (delta f n t v d).toMonoidHom
    change IsUnit (delta f n t v d (1+_ * _)) at h
    simpa only [map_add,map_one,map_mul,map_sub,coord,roots,delta_right,AlgHom.commutes] using h
  have he : right₂ f n t v d (coord f n t v d)-right₂ f n t v d (algebraMap B (T f n t v d) t) +
      (right₂ f n t v d (algebraMap B (T f n t v d) t)-algebraMap B (U f n t v d) t)=
      right₂ f n t v d (coord f n t v d)-algebraMap B (U f n t v d) t := by ring
  rw [rootShift_comp _ _ _ ha (by rw [he];exact hab),he]
  simp only [coord,roots,delta_right]

end


lemma unit_zpow_cancel {R : Type*} [CommRing R] (a b : Rˣ) (z : ℤ) :
    a^z*(b*a⁻¹)^z=b^z := by
  rw [mul_zpow,inv_zpow,mul_left_comm,mul_inv_cancel,mul_one]

open Polynomial Lech.RootGluing
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

def denominator (i : Fin n) : (T f n t v d)ˣ :=
  RootTransport.denominator (f.map (algebraMap A B)) n (natDegree_map_le.trans hn) t v hv
    (coord f n t v d) (unit f n t v d) (roots f n t v d) (factorization f n t v d) i

lemma denominator_val (i : Fin n) : (denominator f n hn t v hv d i:T f n t v d)=
    1+(coord f n t v d-algebraMap B (T f n t v d) t)*roots f n t v d i :=
  RootTransport.denominator_val _ _ _ _ _ _ _ _ _ _ _

lemma weight_eq (ms : Fin n → ℤ) : weight f n hn t v hv d ms=∏ i,denominator f n hn t v hv d i ^ ms i := rfl

lemma counit_denominator (i : Fin n) :
    Units.map (counit f n t v d).toMonoidHom (denominator f n hn t v hv d i)=1 := by
  apply Units.ext
  change counit f n t v d (denominator f n hn t v hv d i:T f n t v d)=1
  rw [denominator_val,map_add,map_one,map_mul,map_sub,coord,roots,counit_right,counit_right,AlgHom.commutes]
  simp

lemma counit_weight (ms : Fin n → ℤ) :
    Units.map (counit f n t v d).toMonoidHom (weight f n hn t v hv d ms)=1 := by
  rw [weight_eq,map_prod]
  simp only [map_zpow,counit_denominator,one_zpow,Finset.prod_const_one]

lemma counit_linear (ms : Fin n → ℤ) :
    (counit f n t v d).toLinearMap.comp (linear f n hn t v hv d ms)=LinearMap.id := by
  ext x
  have h := congrArg (fun w : d.Sˣ => (w:d.S)) (counit_weight f n hn t v hv d ms)
  have hx := congrArg (fun φ : d.S →ₐ[B] d.S => φ x) (counit_hom f n hn t v hv d)
  change counit f n t v d (weight f n hn t v hv d ms:T f n t v d)=1 at h
  change counit f n t v d (hom f n hn t v hv d x)=x at hx
  change counit f n t v d (linear f n hn t v hv d ms x)=x
  rw [linear_apply,map_mul,h,hx,one_mul]

lemma psi_denominator (i : Fin n) :
    Units.map (psi f n hn t v hv d).toMonoidHom (denominator f n hn t v hv d i)=
      Units.map (delta f n t v d).toMonoidHom (denominator f n hn t v hv d i) *
      (Units.map (right₂ f n t v d).toMonoidHom (denominator f n hn t v hv d i))⁻¹ := by
  apply Units.ext
  let a := right₂ f n t v d (coord f n t v d)-right₂ f n t v d (algebraMap B (T f n t v d) t)
  let b := right₂ f n t v d (algebraMap B (T f n t v d) t)-algebraMap B (U f n t v d) t
  let r := right₂ f n t v d (roots f n t v d i)
  let e := Units.map (right₂ f n t v d).toMonoidHom (denominator f n hn t v hv d i)
  have he : (e:U f n t v d)=1+a*r := by
    change right₂ f n t v d (denominator f n hn t v hv d i:T f n t v d)=1+a*r
    rw [denominator_val,map_add,map_one,map_mul,map_sub]
  have heab : a+b=right₂ f n t v d (coord f n t v d)-algebraMap B (U f n t v d) t := by dsimp [a,b];ring
  change psi f n hn t v hv d (denominator f n hn t v hv d i:T f n t v d)=_
  rw [denominator_val,map_add,map_one,map_mul,map_sub,AlgHom.commutes,psi_coord,psi_roots]
  change 1+b*rootShift a r=delta f n t v d (denominator f n hn t v hv d i:T f n t v d)*(e⁻¹:Units (U f n t v d))
  rw [rootShift,← he,Ring.inverse_unit,denominator_comp a b r e he,heab]
  congr 1
  rw [denominator_val,map_add,map_one,map_mul,map_sub,AlgHom.commutes,coord,roots,delta_right,delta_right]
  rfl

lemma weight_coassoc (ms : Fin n → ℤ) :
    Units.map (right₂ f n t v d).toMonoidHom (weight f n hn t v hv d ms) *
      Units.map (psi f n hn t v hv d).toMonoidHom (weight f n hn t v hv d ms)=
    Units.map (delta f n t v d).toMonoidHom (weight f n hn t v hv d ms) := by
  simp only [weight_eq,map_prod,map_zpow,psi_denominator]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact unit_zpow_cancel _ _ _

end


open Polynomial Lech.RootGluing
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

def liftLinear (ms : Fin n → ℤ) : T f n t v d →ₗ[B] U f n t v d :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : B →ₗ[B] B)
    ((linear f n hn t v hv d ms).restrictScalars A)

lemma liftLinear_apply (ms : Fin n → ℤ) (z : T f n t v d) :
    liftLinear f n hn t v hv d ms z =
      right₂ f n t v d (weight f n hn t v hv d ms:T f n t v d)*psi f n hn t v hv d z := by
  induction z using TensorProduct.inductionOn with
  | tmul b x =>
    simp only [liftLinear,TensorProduct.AlgebraTensorModule.map_tmul,LinearMap.id_apply,
      LinearMap.restrictScalars_apply,linear_apply,psi,Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply,AlgHom.restrictScalars_apply,right₂,Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul,one_mul]
  | add x y hx hy => rw [map_add,map_add,mul_add,hx,hy]

lemma linear_coassoc (ms : Fin n → ℤ) :
    (delta f n t v d).toLinearMap.comp (linear f n hn t v hv d ms)=
      (liftLinear f n hn t v hv d ms).comp (linear f n hn t v hv d ms) := by
  ext x
  have hw := congrArg (fun w : (U f n t v d)ˣ => (w:U f n t v d))
    (weight_coassoc f n hn t v hv d ms)
  change right₂ f n t v d (weight f n hn t v hv d ms:T f n t v d) *
    psi f n hn t v hv d (weight f n hn t v hv d ms:T f n t v d)=
    delta f n t v d (weight f n hn t v hv d ms:T f n t v d) at hw
  have hh := congrArg (fun φ : d.S →ₐ[B] U f n t v d => φ x) (delta_hom f n hn t v hv d)
  change delta f n t v d (hom f n hn t v hv d x)=psi f n hn t v hv d (hom f n hn t v hv d x) at hh
  change delta f n t v d (linear f n hn t v hv d ms x)=liftLinear f n hn t v hv d ms (linear f n hn t v hv d ms x)
  rw [liftLinear_apply,linear_apply,map_mul,map_mul,← mul_assoc,hw,hh]
end Lech.RootCoaction


namespace Lech.NativeDescent
open scoped TensorProduct
open TensorProduct
universe u v w
variable {A : Type u} {B : Type v} {M : Type w}
  [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

 
def inclusion : M →ₗ[A] B ⊗[A] M := TensorProduct.mk A B M 1
 
def evaluation : B ⊗[A] M →ₗ[B] M := (LinearMap.id : M →ₗ[A] M).liftBaseChange B

variable (l : M →ₗ[B] B ⊗[A] M)
 
def invariants : Submodule A M := LinearMap.eqLocus (l.restrictScalars A) inclusion

lemma invariant_eq (x : invariants l) : l (x:M)=(1:B) ⊗ₜ[A] (x:M) := x.property

 
def baseMap : B ⊗[A] invariants l →ₗ[B] M := (invariants l).subtype.liftBaseChange B

def baseInclusion : B ⊗[A] invariants l →ₗ[B] B ⊗[A] M :=
  AlgebraTensorModule.lTensor B B (invariants l).subtype

lemma evaluation_baseInclusion : (evaluation (A := A) (B := B) (M := M)).comp (baseInclusion l)=baseMap l := by
  ext x
  simp [evaluation,baseInclusion,baseMap]

lemma coaction_baseMap : l.comp (baseMap l)=baseInclusion l := by
  ext x
  change l ((1:B) • (x:M))=(1:B) ⊗ₜ[A] (x:M)
  simpa only [one_smul] using invariant_eq l x

variable [Module.Flat A B]
variable (hε : (evaluation (A := A) (B := B) (M := M)).comp l=LinearMap.id)
variable (hδ : (AlgebraTensorModule.lTensor B B inclusion).comp l=
  (AlgebraTensorModule.lTensor B B (l.restrictScalars A)).comp l)

 
def coactionToEqualizer : M →ₗ[B]
    LinearMap.eqLocus (AlgebraTensorModule.lTensor B B (l.restrictScalars A))
      (AlgebraTensorModule.lTensor B B inclusion) :=
  l.codRestrict _ (fun x => (LinearMap.congr_fun hδ x).symm)

def inverse : M →ₗ[B] B ⊗[A] invariants l :=
  (LinearMap.tensorEqLocusEquiv B B (l.restrictScalars A) inclusion).symm.toLinearMap.comp
    (coactionToEqualizer l hδ)

lemma baseInclusion_inverse : (baseInclusion l).comp (inverse l hδ)=l := by
  ext x
  change (LinearMap.lTensor B (invariants l).subtype)
    ((LinearMap.tensorEqLocusEquiv B B (l.restrictScalars A) inclusion).symm
      (coactionToEqualizer l hδ x))=l x
  exact LinearMap.lTensor_eqLocus_subtype_tensoreqLocusEquiv_symm B B
    (l.restrictScalars A) inclusion (coactionToEqualizer l hδ x)


def tensorEquiv : B ⊗[A] invariants l ≃ₗ[B] M :=
  LinearEquiv.ofLinearMap (baseMap l) (inverse l hδ)
    (by
      rw [← evaluation_baseInclusion,LinearMap.comp_assoc,baseInclusion_inverse,hε])
    (by
      apply LinearMap.ext
      intro x
      apply Module.Flat.lTensor_preserves_injective_linearMap
        (invariants l).subtype (invariants l).injective_subtype
      change baseInclusion l ((inverse l hδ) (baseMap l x))=baseInclusion l x
      rw [← LinearMap.comp_apply,baseInclusion_inverse,← LinearMap.comp_apply,coaction_baseMap])
end Lech.NativeDescent


namespace Lech.ModuleDescent
open scoped TensorProduct
open TensorProduct
universe u v w
variable {A : Type u} {B : Type v} {M : Type w}
  [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]

 
lemma finitePresentation [Module.FaithfullyFlat A B]
    [Module.FinitePresentation B (B ⊗[A] M)] : Module.FinitePresentation A M := by
  let : Module.Finite A M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  obtain ⟨n,p,hp⟩ := (Submodule.fg_iff_exists_fin_linearMap (N := (⊤ : Submodule A M))).mp
    (Module.Finite.fg_top (R := A) (M := M))
  have hsurj : Function.Surjective p := LinearMap.range_eq_top.mp hp
  let pB := AlgebraTensorModule.lTensor B B p
  have hpB : Function.Surjective pB :=
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective A B p).mpr hsurj
  have hkB : (LinearMap.ker pB).FG := Module.FinitePresentation.fg_ker pB hpB
  let : Module.Finite B (LinearMap.ker pB) := Module.Finite.of_fg hkB
  let : Module.Finite B (B ⊗[A] LinearMap.ker p) :=
    Module.Finite.equiv (LinearMap.tensorKerEquiv B B p).symm
  let : Module.Finite A (LinearMap.ker p) :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  exact Module.finitePresentation_of_surjective p hsurj (Module.Finite.iff_fg.mp inferInstance)
end Lech.ModuleDescent


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl


def module (ms : Fin n → ℤ) : Submodule A d.S :=
  NativeDescent.invariants (RootCoaction.linear f n hn t v hv d ms)

lemma member_eq (ms : Fin n → ℤ) (x : module f n hn t v hv d ms) :
    (RootCoaction.weight f n hn t v hv d ms : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (x:d.S)=RootCoaction.right f n t v d (x:d.S) :=
  x.property

lemma evaluation_eq : (NativeDescent.evaluation (A := A) (B := B) (M := d.S))=
    (RootCoaction.counit f n t v d).toLinearMap := by
  ext x
  change (1:B) • x=algebraMap B d.S 1*x
  rw [one_smul,map_one,one_mul]

lemma delta_eq : TensorProduct.AlgebraTensorModule.lTensor B B
    (NativeDescent.inclusion (A := A) (B := B) (M := d.S))=
      (RootCoaction.delta f n t v d).toLinearMap := by
  ext x
  rfl

 
def tensorEquiv [Module.Flat A B] (ms : Fin n → ℤ) :
    B ⊗[A] module f n hn t v hv d ms ≃ₗ[B] d.S :=
  NativeDescent.tensorEquiv (RootCoaction.linear f n hn t v hv d ms)
    (by rw [evaluation_eq];exact RootCoaction.counit_linear f n hn t v hv d ms)
    (by rw [delta_eq];exact RootCoaction.linear_coassoc f n hn t v hv d ms)

lemma finite [Module.FaithfullyFlat A B] (ms : Fin n → ℤ) :
    Module.Finite A (module f n hn t v hv d ms) := by
  let : Module.Finite B d.S := d.finite
  let : Module.Finite B (B ⊗[A] module f n hn t v hv d ms) :=
    Module.Finite.equiv (tensorEquiv f n hn t v hv d ms).symm
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

lemma finitePresentation [Module.FaithfullyFlat A B] (ms : Fin n → ℤ) :
    Module.FinitePresentation A (module f n hn t v hv d ms) := by
  let : Module.Free B d.S := d.free
  let : Module.Finite B d.S := d.finite
  let : Module.FinitePresentation B d.S := Module.finitePresentation_of_projective B d.S
  let : Module.FinitePresentation B (B ⊗[A] module f n hn t v hv d ms) :=
    Module.FinitePresentation.of_equiv (tensorEquiv f n hn t v hv d ms).symm
  exact ModuleDescent.finitePresentation (B := B)

lemma flat [Module.FaithfullyFlat A B] (ms : Fin n → ℤ) :
    Module.Flat A (module f n hn t v hv d ms) := by
  let : Module.Flat B d.S := d.flat
  let : Module.Flat B (B ⊗[A] module f n hn t v hv d ms) :=
    Module.Flat.of_linearEquiv (tensorEquiv f n hn t v hv d ms)
  exact Module.Flat.of_flat_tensorProduct A (module f n hn t v hv d ms) B

lemma projective [Module.FaithfullyFlat A B] (ms : Fin n → ℤ) :
    Module.Projective A (module f n hn t v hv d ms) := by
  let := finitePresentation f n hn t v hv d ms
  let := flat f n hn t v hv d ms
  exact Module.Flat.projective_of_finitePresentation

lemma rankAtStalk [Module.FaithfullyFlat A B] (ms : Fin n → ℤ)
    (p : PrimeSpectrum A) : Module.rankAtStalk (module f n hn t v hv d ms) p=n.factorial := by
  obtain ⟨q,hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) p
  let : Nontrivial B := q.nontrivial
  let := flat f n hn t v hv d ms
  let := finite f n hn t v hv d ms
  let : Module.Free B d.S := d.free
  have he := congrFun (Module.rankAtStalk_eq_of_equiv (tensorEquiv f n hn t v hv d ms)) q
  rw [Module.rankAtStalk_baseChange,hq,Module.rankAtStalk_eq_finrank_of_free (R := B) (M := d.S)] at he
  exact he.trans (by simpa using Module.finrank_eq_card_basis d.basis)
end Lech.RootInvariants

end

end OAI
