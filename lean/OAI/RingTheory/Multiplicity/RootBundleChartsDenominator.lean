import Mathlib
import OAI.RingTheory.Multiplicity.PrimitiveChartFaithfullyFlat

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
namespace Lech.RootBundleCharts
open Polynomial Lech.RootGluing
universe u
variable {B : Type u} [CommRing B]
variable (f : B[X]) (n : ℕ) (hn : f.natDegree≤n)
  (t u : B) (v w : Bˣ) (hv : f.eval t=(v:B)) (hw : f.eval u=(w:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized f n t v))
  (e : UniversalSplitting.Data B n (BinaryChange.normalized f n u w))

def denominator (i : Fin n) : d.Sˣ := (denominator_unit f n hn t u v w hw d i).unit

lemma denominator_val (i : Fin n) :
    (denominator f n hn t u v w hw d i : d.S)=1+algebraMap B d.S (t-u)*d.roots i :=
  IsUnit.unit_spec _

lemma hom_denominator (s : B) (z : Bˣ) (hz : f.eval s=(z:B)) (i : Fin n) :
    Units.map (hom f n hn t u v w hw d e).toMonoidHom
      (denominator f n hn u s w z hz e i) =
    denominator f n hn t s v z hz d i * (denominator f n hn t u v w hw d i)⁻¹ := by
  apply Units.ext
  change (hom f n hn t u v w hw d e) (denominator f n hn u s w z hz e i : e.S)=_
  rw [denominator_val,map_add,map_one,map_mul,AlgHom.commutes,hom_root]
  simp only [rootShift,← denominator_val f n hn t u v w hw d i,Ring.inverse_unit,
    Units.val_mul]
  rw [denominator_comp _ _ _ _ (denominator_val f n hn t u v w hw d i),denominator_val]
  have hab : algebraMap B d.S (t-u)+algebraMap B d.S (u-s)=
      algebraMap B d.S (t-s) := by rw [← map_add]; congr 1; ring
  rw [hab]

 
def weight (ms : Fin n → ℤ) : d.Sˣ :=
  ∏ i, denominator f n hn t u v w hw d i ^ ms i

lemma weight_cocycle (ms : Fin n → ℤ) (s : B) (z : Bˣ) (hz : f.eval s=(z:B)) :
    weight f n hn t u v w hw d ms *
      Units.map (hom f n hn t u v w hw d e).toMonoidHom
        (weight f n hn u s w z hz e ms) = weight f n hn t s v z hz d ms := by
  unfold weight
  rw [map_prod]
  simp_rw [map_zpow,hom_denominator,mul_zpow,inv_zpow]
  rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib]
  rw [mul_left_comm,mul_inv_cancel,mul_one]


def transition (ms : Fin n → ℤ) : e.S ≃ₗ[B] d.S :=
  (equiv f n hn t u v w hv hw d e).toLinearEquiv.trans
    ((LinearEquiv.smulOfUnit (M := d.S) (weight f n hn t u v w hw d ms)).restrictScalars B)

lemma transition_apply (ms : Fin n → ℤ) (x : e.S) :
    transition f n hn t u v w hv hw d e ms x =
      (weight f n hn t u v w hw d ms : d.S)*hom f n hn t u v w hw d e x := rfl

include hv in
lemma transition_cocycle (ms : Fin n → ℤ) (s : B) (z : Bˣ) (hz : f.eval s=(z:B))
    (c : UniversalSplitting.Data B n (BinaryChange.normalized f n s z)) :
    (transition f n hn u s w z hw hz e c ms).trans
      (transition f n hn t u v w hv hw d e ms)=
        transition f n hn t s v z hv hz d c ms := by
  ext x
  simp only [LinearEquiv.trans_apply,transition_apply,map_mul]
  have h := congrArg (fun q : d.Sˣ => (q:d.S)) (weight_cocycle f n hn t u v w hw d e ms s z hz)
  change (weight f n hn t u v w hw d ms:d.S)*
    (hom f n hn t u v w hw d e) (weight f n hn u s w z hz e ms:e.S)=
      (weight f n hn t s v z hz d ms:d.S) at h
  have hc := congrArg (fun φ : c.S →ₐ[B] d.S => φ x) (hom_cocycle f n hn t u v w hw d e s z hz c)
  change (weight f n hn t u v w hw d ms:d.S)*
    (hom f n hn t u v w hw d e (weight f n hn u s w z hz e ms:e.S)*
      hom f n hn t u v w hw d e (hom f n hn u s w z hz e c x))=_
  change (hom f n hn t u v w hw d e) ((hom f n hn u s w z hz e c) x)=
    (hom f n hn t s v z hz d c) x at hc
  rw [← mul_assoc,h,hc]

lemma hom_identity : hom f n hn t t v v hv d d=AlgHom.id B d.S := by
  apply d.hom_ext
  intro i
  rw [hom_root]
  simp [rootShift]

lemma denominator_identity (i : Fin n) : denominator f n hn t t v v hv d i=1 := by
  apply Units.ext
  rw [denominator_val]
  simp

lemma weight_identity (ms : Fin n → ℤ) : weight f n hn t t v v hv d ms=1 := by
  simp only [weight,denominator_identity,one_zpow,Finset.prod_const_one]

lemma transition_identity (ms : Fin n → ℤ) :
    transition f n hn t t v v hv hv d d ms=LinearEquiv.refl B d.S := by
  ext x
  rw [transition_apply,weight_identity,hom_identity]
  simp


lemma factor_coordinates (i : Fin n) :
    -hom f n hn t u v w hw d e (e.roots i)=
      (↑(denominator f n hn t u v w hw d i)⁻¹:d.S)*(-d.roots i) ∧
    1+algebraMap B d.S u*hom f n hn t u v w hw d e (e.roots i)=
      (↑(denominator f n hn t u v w hw d i)⁻¹:d.S)*(1+algebraMap B d.S t*d.roots i) := by
  rw [hom_root]
  simp only [rootShift,← denominator_val f n hn t u v w hw d i,Ring.inverse_unit]
  constructor
  · ring
  · calc
      _ = (denominator f n hn t u v w hw d i:d.S)*
          (↑(denominator f n hn t u v w hw d i)⁻¹:d.S)+
          algebraMap B d.S u*(d.roots i*(↑(denominator f n hn t u v w hw d i)⁻¹:d.S)) := by
        rw [(denominator f n hn t u v w hw d i).mul_inv]
      _ = _ := by rw [denominator_val,map_sub]; ring


def chartBasis : Module.Basis (Fin n.factorial) B d.S := d.basis

end Lech.RootBundleCharts


namespace Lech.RootBaseChange
open Polynomial Lech.RootGluing Lech.RootBundleCharts
universe u
variable {B T : Type u} [CommRing B] [CommRing T] [Algebra B T]
variable (f : B[X]) (n : ℕ) (hn : f.natDegree ≤ n) (t s : B) (v w : Bˣ)
  (hv : f.eval t=(v:B)) (hw : f.eval s=(w:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized f n t v))
  (e : UniversalSplitting.Data B n (BinaryChange.normalized f n s w))
  (D : UniversalSplitting.Data T n (BinaryChange.normalized (f.map (algebraMap B T)) n
    (algebraMap B T t) (Units.map (algebraMap B T).toMonoidHom v)))
  (E : UniversalSplitting.Data T n (BinaryChange.normalized (f.map (algebraMap B T)) n
    (algebraMap B T s) (Units.map (algebraMap B T).toMonoidHom w)))
  [Algebra B D.S] [IsScalarTower B T D.S]
  [Algebra B E.S] [IsScalarTower B T E.S]

lemma mapped_eval (a : B) (z : Bˣ) (hz : f.eval a=(z:B)) :
    (f.map (algebraMap B T)).eval (algebraMap B T a)=
      ((Units.map (algebraMap B T).toMonoidHom z : Tˣ) : T) := by
  rw [Polynomial.eval_map,eval₂_at_apply,hz]
  rfl

lemma chartFactorization :
    (BinaryChange.normalized f n t v).map (algebraMap B D.S)=
      ∏ i, (Polynomial.X-C (D.roots i)) := by
  rw [IsScalarTower.algebraMap_eq B T D.S,← Polynomial.map_map,
    BinaryCover.map_normalized]
  exact D.factorization


def chartMap : d.S →ₐ[B] D.S :=
  (d.universal D.S D.roots (chartFactorization f n t v D)).choose

lemma chartMap_root (i : Fin n) : chartMap f n t v d D (d.roots i)=D.roots i :=
  (d.universal D.S D.roots (chartFactorization f n t v D)).choose_spec.1 i

lemma chartMap_denominator (i : Fin n) :
    Units.map (chartMap f n t v d D).toMonoidHom
      (denominator f n hn t s v w hw d i)=
    denominator (f.map (algebraMap B T)) n (natDegree_map_le.trans hn)
      (algebraMap B T t) (algebraMap B T s)
      (Units.map (algebraMap B T).toMonoidHom v) (Units.map (algebraMap B T).toMonoidHom w)
      (mapped_eval (T := T) f s w hw) D i := by
  apply Units.ext
  change (chartMap f n t v d D) (denominator f n hn t s v w hw d i : d.S)=_
  rw [denominator_val,map_add,map_one,map_mul,AlgHom.commutes,chartMap_root,
    denominator_val,← map_sub,← IsScalarTower.algebraMap_apply]

lemma chartMap_weight (ms : Fin n → ℤ) :
    Units.map (chartMap f n t v d D).toMonoidHom
      (weight f n hn t s v w hw d ms)=
    weight (f.map (algebraMap B T)) n (natDegree_map_le.trans hn)
      (algebraMap B T t) (algebraMap B T s)
      (Units.map (algebraMap B T).toMonoidHom v) (Units.map (algebraMap B T).toMonoidHom w)
      (mapped_eval (T := T) f s w hw) D ms := by
  simp only [weight,map_prod,map_zpow,chartMap_denominator]

def baseHom : E.S →ₐ[T] D.S :=
  @Lech.RootGluing.hom T (inferInstance : CommRing T) (f.map (algebraMap B T)) n
    (Polynomial.natDegree_map_le.trans hn)
    (algebraMap B T t) (algebraMap B T s)
    (Units.map (algebraMap B T).toMonoidHom v) (Units.map (algebraMap B T).toMonoidHom w)
    (mapped_eval (T := T) f s w hw) D E

def baseTransition (ms : Fin n → ℤ) : E.S ≃ₗ[T] D.S :=
  @Lech.RootBundleCharts.transition T (inferInstance : CommRing T) (f.map (algebraMap B T)) n
    (Polynomial.natDegree_map_le.trans hn)
    (algebraMap B T t) (algebraMap B T s)
    (Units.map (algebraMap B T).toMonoidHom v) (Units.map (algebraMap B T).toMonoidHom w)
    (mapped_eval (T := T) f t v hv) (mapped_eval (T := T) f s w hw) D E ms


lemma chartMap_hom :
    (chartMap f n t v d D).comp (hom f n hn t s v w hw d e)=
      ((baseHom f n hn t s v w hw D E).restrictScalars B).comp
          (chartMap f n s w e E) := by
  apply e.hom_ext
  intro i
  simp only [AlgHom.comp_apply,hom_root,chartMap_root,AlgHom.restrictScalars_apply]
  unfold baseHom
  change (chartMap f n t v d D).toRingHom (rootShift (algebraMap B d.S (t-s)) (d.roots i)) = _
  rw [map_rootShift (chartMap f n t v d D).toRingHom _ _
    (denominator_unit f n hn t s v w hw d i)]
  change rootShift ((chartMap f n t v d D) (algebraMap B d.S (t-s)))
    ((chartMap f n t v d D) (d.roots i))=_
  rw [AlgHom.commutes,chartMap_root,hom_root,← map_sub,← IsScalarTower.algebraMap_apply]

include hv in
lemma transition_natural (ms : Fin n → ℤ) (x : e.S) :
    chartMap f n t v d D (transition f n hn t s v w hv hw d e ms x)=
      baseTransition f n hn t s v w hv hw D E ms
          (chartMap f n s w e E x) := by
  simp only [baseTransition,transition_apply,map_mul]
  have hweight := congrArg (fun a : D.Sˣ => (a:D.S))
    (chartMap_weight f n hn t s v w hw d D ms)
  have hmap := congrArg (fun a : e.S →ₐ[B] D.S => a x)
    (chartMap_hom f n hn t s v w hw d e D E)
  exact congrArg₂ (· * ·) hweight hmap

end Lech.RootBaseChange


namespace Lech.UniversalSplitting

section
open Polynomial
universe u
variable {R : Type u} [CommRing R] {n : ℕ} {f : R[X]}


def Data.canonicalHom (d e : Data R n f) : d.S →ₐ[R] e.S :=
  (d.universal e.S e.roots e.factorization).choose

lemma Data.canonicalHom_root (d e : Data R n f) (i : Fin n) :
    d.canonicalHom e (d.roots i)=e.roots i :=
  (d.universal e.S e.roots e.factorization).choose_spec.1 i

lemma Data.canonicalHom_comp (d e c : Data R n f) :
    (e.canonicalHom c).comp (d.canonicalHom e)=d.canonicalHom c := by
  apply d.hom_ext
  intro i
  simp only [AlgHom.comp_apply,Data.canonicalHom_root]

lemma Data.canonicalHom_self (d : Data R n f) : d.canonicalHom d=AlgHom.id R d.S := by
  apply d.hom_ext
  intro i
  exact d.canonicalHom_root d i

def Data.canonicalEquiv (d e : Data R n f) : d.S ≃ₐ[R] e.S :=
  AlgEquiv.ofAlgHom (d.canonicalHom e) (e.canonicalHom d)
    (by rw [Data.canonicalHom_comp, Data.canonicalHom_self])
    (by rw [Data.canonicalHom_comp, Data.canonicalHom_self])

lemma Data.canonicalEquiv_root (d e : Data R n f) (i : Fin n) :
    d.canonicalEquiv e (d.roots i)=e.roots i := d.canonicalHom_root e i


def Data.baseChangeEquiv (d : Data R n f) (T : Type u) [CommRing T] [Algebra R T]
    (e : Data T n (f.map (algebraMap R T))) :
    TensorProduct R T d.S ≃ₐ[T] e.S :=
  (d.baseChange T).canonicalEquiv e

lemma Data.baseChangeEquiv_root (d : Data R n f) (T : Type u) [CommRing T] [Algebra R T]
    (e : Data T n (f.map (algebraMap R T))) (i : Fin n) :
    d.baseChangeEquiv T e (Algebra.TensorProduct.includeRight (d.roots i))=e.roots i :=
  (d.baseChange T).canonicalEquiv_root e i

end


open Polynomial
universe u
variable {R : Type u} [CommRing R] {n : ℕ} {f : R[X]}

def Data.baseChangeEquivOfMap (d : Data R n f) (T : Type u) [CommRing T] [Algebra R T]
    (g : T[X]) (h : f.map (algebraMap R T)=g) (e : Data T n g) :
    TensorProduct R T d.S ≃ₐ[T] e.S := by
  subst g
  exact d.baseChangeEquiv T e

lemma Data.baseChangeEquivOfMap_root (d : Data R n f) (T : Type u)
    [CommRing T] [Algebra R T] (g : T[X]) (h : f.map (algebraMap R T)=g)
    (e : Data T n g) (i : Fin n) :
    d.baseChangeEquivOfMap T g h e (Algebra.TensorProduct.includeRight (d.roots i))=e.roots i := by
  subst g
  exact d.baseChangeEquiv_root T e i
end Lech.UniversalSplitting


namespace Lech.RootBaseChange
open Polynomial Lech.RootGluing Lech.RootBundleCharts
open scoped TensorProduct
universe u
variable {B T : Type u} [CommRing B] [CommRing T] [Algebra B T]
variable (f : B[X]) (n : ℕ) (hn : f.natDegree ≤ n) (t s : B) (v w : Bˣ)
  (hv : f.eval t=(v:B)) (hw : f.eval s=(w:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized f n t v))
  (e : UniversalSplitting.Data B n (BinaryChange.normalized f n s w))
  (D : UniversalSplitting.Data T n (BinaryChange.normalized (f.map (algebraMap B T)) n
    (algebraMap B T t) (Units.map (algebraMap B T).toMonoidHom v)))
  (E : UniversalSplitting.Data T n (BinaryChange.normalized (f.map (algebraMap B T)) n
    (algebraMap B T s) (Units.map (algebraMap B T).toMonoidHom w)))
  [Algebra B D.S] [IsScalarTower B T D.S]
  [Algebra B E.S] [IsScalarTower B T E.S]

 
def chartTensorEquiv : T ⊗[B] d.S ≃ₐ[T] D.S :=
  d.baseChangeEquivOfMap T _ (BinaryCover.map_normalized (algebraMap B T) f n t v) D

omit [Algebra B D.S] [IsScalarTower B T D.S] in
lemma chartTensorEquiv_root (i : Fin n) :
    chartTensorEquiv f n t v d D (Algebra.TensorProduct.includeRight (d.roots i))=D.roots i :=
  d.baseChangeEquivOfMap_root T _ (BinaryCover.map_normalized (algebraMap B T) f n t v) D i

lemma chartTensorEquiv_includeRight :
    ((chartTensorEquiv f n t v d D).toAlgHom.restrictScalars B).comp
      Algebra.TensorProduct.includeRight = chartMap f n t v d D := by
  apply d.hom_ext
  intro i
  simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,AlgEquiv.coe_toAlgHom,chartTensorEquiv_root,chartMap_root]

lemma chartTensorEquiv_tmul (a : T) (x : d.S) :
    chartTensorEquiv f n t v d D (a ⊗ₜ[B] x)=a • chartMap f n t v d D x := by
  have h := congrArg (fun φ : d.S →ₐ[B] D.S => φ x)
    (chartTensorEquiv_includeRight f n t v d D)
  change chartTensorEquiv f n t v d D (1 ⊗ₜ[B] x)=chartMap f n t v d D x at h
  calc
    _ = chartTensorEquiv f n t v d D (a • (1 ⊗ₜ[B] x)) := by
      congr 1
      simp only [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    _ = a • chartTensorEquiv f n t v d D (1 ⊗ₜ[B] x) := map_smul _ _ _
    _ = _ := congrArg (a • ·) h


lemma tensor_transition (ms : Fin n → ℤ) :
    (LinearEquiv.baseChange B T e.S d.S (transition f n hn t s v w hv hw d e ms)).trans
      (chartTensorEquiv f n t v d D).toLinearEquiv =
    (chartTensorEquiv f n s w e E).toLinearEquiv.trans
      (baseTransition f n hn t s v w hv hw D E ms) := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
      AlgEquiv.toLinearEquiv_apply, chartTensorEquiv_tmul, map_smul]
    exact congrArg (a • ·) (transition_natural f n hn t s v w hv hw d e D E ms x)
  | add x y hx hy =>
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

end Lech.RootBaseChange


namespace Lech.RootTransport
open Polynomial Lech.RootGluing
universe u
variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable (f : B[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : f.eval t=(v:B)) (d : UniversalSplitting.Data B n (BinaryChange.normalized f n t v))
  (u : C) (w : Cˣ) (rs : Fin n → C)
  (hs : BinaryChange.normalized (f.map (algebraMap B C)) n u w=∏ i,(Polynomial.X-Polynomial.C (rs i)))

include hv in
lemma mapped_eval : (f.map (algebraMap B C)).eval (algebraMap B C t)=
    (Units.map (algebraMap B C).toMonoidHom v:Cˣ) := by
  rw [Polynomial.eval_map,eval₂_at_apply,hv]
  rfl

include hn hv hs in
lemma shift_factorization :
    (BinaryChange.normalized f n t v).map (algebraMap B C)=
      ∏ i,(Polynomial.X-Polynomial.C (rootShift (u-algebraMap B C t) (rs i))) := by
  rw [BinaryCover.map_normalized]
  exact normalized_shift _ (natDegree_map_le.trans hn) u (algebraMap B C t) w
    (Units.map (algebraMap B C).toMonoidHom v) rs hs (mapped_eval f t v hv)


def hom : d.S →ₐ[B] C :=
  (d.universal C (fun i => rootShift (u-algebraMap B C t) (rs i))
    (shift_factorization f n hn t v hv u w rs hs)).choose

lemma hom_root (i : Fin n) : hom f n hn t v hv d u w rs hs (d.roots i)=
    rootShift (u-algebraMap B C t) (rs i) :=
  (d.universal C _ (shift_factorization f n hn t v hv u w rs hs)).choose_spec.1 i

include hn hv hs in
lemma denominator_unit (i : Fin n) : IsUnit (1+(u-algebraMap B C t)*rs i) :=
  RootTransitions.denominator_isUnit _ (natDegree_map_le.trans hn) u (algebraMap B C t)
    w (Units.map (algebraMap B C).toMonoidHom v) rs hs (mapped_eval f t v hv) i

def denominator (i : Fin n) : Cˣ :=
  (denominator_unit f n hn t v hv u w rs hs i).unit

lemma denominator_val (i : Fin n) :
    (denominator f n hn t v hv u w rs hs i:C)=1+(u-algebraMap B C t)*rs i :=
  IsUnit.unit_spec _

def weight (ms : Fin n → ℤ) : Cˣ := ∏ i, denominator f n hn t v hv u w rs hs i ^ ms i

 
def linear (ms : Fin n → ℤ) : d.S →ₗ[B] C :=
  ((LinearEquiv.smulOfUnit (M := C) (weight f n hn t v hv u w rs hs ms)).restrictScalars B).toLinearMap.comp
    (hom f n hn t v hv d u w rs hs).toLinearMap

lemma linear_apply (ms : Fin n → ℤ) (x : d.S) :
    linear f n hn t v hv d u w rs hs ms x =
      (weight f n hn t v hv u w rs hs ms:C)*hom f n hn t v hv d u w rs hs x := rfl

end Lech.RootTransport

end

end OAI
