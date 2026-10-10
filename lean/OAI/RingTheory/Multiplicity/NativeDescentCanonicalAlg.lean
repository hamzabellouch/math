import Mathlib
import OAI.RingTheory.Multiplicity.StandardFactorChartsL

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
namespace Lech.NativeDescent
open scoped TensorProduct
universe u v w
variable {A : Type u} (B : Type v) (T : Type w)
  [CommRing A] [CommRing B] [CommRing T] [Algebra A B] [Algebra A T]

 
def canonicalAlg : B ⊗[A] T →ₐ[B] B ⊗[A] (B ⊗[A] T) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (Algebra.TensorProduct.includeRight.comp (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T))
    (fun _ _ => Commute.all _ _)

lemma canonicalAlg_linear : (canonicalAlg (A := A) B T).toLinearMap=canonical (A := A) B T := by
  ext t
  simp [canonicalAlg,canonical]

def canonicalAlgebra : Subalgebra A (B ⊗[A] T) :=
  AlgHom.equalizer ((canonicalAlg (A := A) B T).restrictScalars A) Algebra.TensorProduct.includeRight

lemma canonicalAlgebra_module : (canonicalAlgebra (A := A) B T).toSubmodule=invariants (canonical (A := A) B T) := by
  ext x
  change (canonicalAlg (A := A) B T x=(1:B) ⊗ₜ[A] x) ↔
    (canonical (A := A) B T x=(1:B) ⊗ₜ[A] x)
  rw [← canonicalAlg_linear]
  rfl

 
def canonicalAlgUnit : T →ₐ[A] canonicalAlgebra (A := A) B T where
  toFun t := ⟨1 ⊗ₜ[A] t,by
    change canonicalAlg (A := A) B T (1 ⊗ₜ[A] t)=(1:B) ⊗ₜ[A] ((1:B) ⊗ₜ[A] t)
    simp [canonicalAlg]⟩
  map_zero' := Subtype.ext (map_zero (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T))
  map_one' := Subtype.ext (map_one (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T))
  map_add' x y := Subtype.ext (map_add (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T) x y)
  map_mul' x y := Subtype.ext (map_mul (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T) x y)
  commutes' a := Subtype.ext ((Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T).commutes a)

lemma canonicalAlgUnit_bijective [Module.FaithfullyFlat A B] :
    Function.Bijective (canonicalAlgUnit (A := A) B T) := by
  let e : canonicalAlgebra (A := A) B T ≃ₗ[A] invariants (canonical (A := A) B T) :=
    LinearEquiv.ofEq _ _ (canonicalAlgebra_module (A := A) B T)
  have he : e.toLinearMap.comp (canonicalAlgUnit (A := A) B T).toLinearMap=canonicalUnit (A := A) B T := by
    ext t
    rfl
  have hb : Function.Bijective (e.toLinearMap.comp (canonicalAlgUnit (A := A) B T).toLinearMap) := by
    rw [he]
    exact canonicalUnit_bijective B T
  refine ⟨fun x y h => hb.injective (congrArg e h),?_⟩
  intro y
  obtain ⟨x,hx⟩ := hb.surjective (e y)
  exact ⟨x,e.injective hx⟩

 
def canonicalAlgEquiv [Module.FaithfullyFlat A B] : T ≃ₐ[A] canonicalAlgebra (A := A) B T :=
  AlgEquiv.ofBijective (canonicalAlgUnit (A := A) B T) (canonicalAlgUnit_bijective B T)
end Lech.NativeDescent


namespace Lech.FactorDescent
open Polynomial
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

abbrev R := B ⊗[A] T
abbrev U := B ⊗[A] R (A := A) (B := B) (T := T)
abbrev includeT : T →ₐ[A] R (A := A) (B := B) (T := T) := Algebra.TensorProduct.includeRight
abbrev right : R (A := A) (B := B) (T := T) →ₐ[A] U (A := A) (B := B) (T := T) := Algebra.TensorProduct.includeRight
abbrev canonical : R (A := A) (B := B) (T := T) →ₐ[B] U (A := A) (B := B) (T := T) := NativeDescent.canonicalAlg B T

lemma canonical_include (a : T) : canonical (A := A) (B := B) (includeT a)=right (includeT a) := by
  simp [canonical,includeT,right,NativeDescent.canonicalAlg]

variable (φ : d.S →ₐ[B] R (A := A) (B := B) (T := T))

def coefficients : RootCoaction.T f n t v d →ₐ[B] U (A := A) (B := B) (T := T) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (right.comp (φ.restrictScalars A)) (fun _ _ => Commute.all _ _)

lemma coefficients_right (x : d.S) : coefficients f n t v d φ (RootCoaction.right f n t v d x)=right (φ x) := by
  simp [coefficients,RootCoaction.right]

 

lemma natural (a b : Fin n → T) (μ : Fin n → (R (A := A) (B := B) (T := T))ˣ)
    (hμ : ∀ i,(μ i:R (A := A) (B := B) (T := T))=algebraMap B _ t*includeT (a i)+includeT (b i))
    (hφ : ∀ i,φ (d.roots i)= -includeT (a i)*((μ i)⁻¹).val) :
    (canonical (A := A) (B := B) (T := T)).comp φ=
      (coefficients f n t v d φ).comp (RootCoaction.hom f n hn t v hv d) := by
  apply d.hom_ext
  intro i
  let ν : (U (A := A) (B := B) (T := T))ˣ := Units.map (canonical (A := A) (B := B) (T := T)).toMonoidHom (μ i)
  let η : (U (A := A) (B := B) (T := T))ˣ := Units.map (right (A := A) (B := B) (T := T)).toMonoidHom (μ i)
  have hν : (ν:U (A := A) (B := B) (T := T))=algebraMap B _ t*right (includeT (a i))+right (includeT (b i)) := by
    change canonical (μ i:R (A := A) (B := B) (T := T))=_
    rw [hμ,map_add,map_mul,AlgHom.commutes,canonical_include,canonical_include]
  have hη : (η:U (A := A) (B := B) (T := T))=right (algebraMap B (R (A := A) (B := B) (T := T)) t)*right (includeT (a i))+right (includeT (b i)) := by
    change right (μ i:R (A := A) (B := B) (T := T))=_
    rw [hμ,map_add,map_mul]
  simp only [AlgHom.comp_apply,RootCoaction.hom_root]
  rw [hφ,map_mul,map_neg,canonical_include]
  change -right (includeT (a i))*(ν⁻¹).val=_
  rw [← FactorNormalization.change_root (right (includeT (a i))) (right (includeT (b i)))
    (right (algebraMap B (R (A := A) (B := B) (T := T)) t)) (algebraMap B _ t) η ν hη hν]
  change _=(coefficients f n t v d φ).toRingHom (RootGluing.rootShift _ _)
  rw [RootGluing.map_rootShift _ _ _ (RootCoaction.denominator_unit f n hn t v hv d i)]
  simp only [map_sub,RootCoaction.coord,RootCoaction.roots,coefficients_right,AlgHom.commutes,
    AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,hφ,map_neg,map_mul]
  rfl

 
def invariantMap (a b : Fin n → T) (μ : Fin n → (R (A := A) (B := B) (T := T))ˣ)
    (hμ : ∀ i,(μ i:R (A := A) (B := B) (T := T))=algebraMap B _ t*includeT (a i)+includeT (b i))
    (hφ : ∀ i,φ (d.roots i)= -includeT (a i)*((μ i)⁻¹).val) :
    RootInvariants.algebra f n hn t v hv d →ₐ[A] NativeDescent.canonicalAlgebra (A := A) B T where
  toFun x := ⟨φ (x:d.S),by
    change canonical (φ (x:d.S))=right (φ (x:d.S))
    have h := AlgHom.congr_fun (natural f n hn t v hv d φ a b μ hμ hφ) (x:d.S)
    change canonical (φ (x:d.S))=coefficients f n t v d φ (RootCoaction.hom f n hn t v hv d (x:d.S)) at h
    have hx : RootCoaction.hom f n hn t v hv d (x:d.S)=RootCoaction.right f n t v d (x:d.S) := x.property
    rw [hx,coefficients_right] at h
    exact h⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_one' := Subtype.ext (map_one φ)
  map_add' x y := Subtype.ext (map_add φ _ _)
  map_mul' x y := Subtype.ext (map_mul φ _ _)
  commutes' c := Subtype.ext ((φ.restrictScalars A).commutes c)

 

def descended [Module.FaithfullyFlat A B]
    (a b : Fin n → T) (μ : Fin n → (R (A := A) (B := B) (T := T))ˣ)
    (hμ : ∀ i,(μ i:R (A := A) (B := B) (T := T))=algebraMap B _ t*includeT (a i)+includeT (b i))
    (hφ : ∀ i,φ (d.roots i)= -includeT (a i)*((μ i)⁻¹).val) :
    RootInvariants.algebra f n hn t v hv d →ₐ[A] T :=
  (NativeDescent.canonicalAlgEquiv (A := A) B T).symm.toAlgHom.comp
    (invariantMap f n hn t v hv d φ a b μ hμ hφ)

lemma descended_include [Module.FaithfullyFlat A B]
    (a b : Fin n → T) (μ : Fin n → (R (A := A) (B := B) (T := T))ˣ)
    (hμ : ∀ i,(μ i:R (A := A) (B := B) (T := T))=algebraMap B _ t*includeT (a i)+includeT (b i))
    (hφ : ∀ i,φ (d.roots i)= -includeT (a i)*((μ i)⁻¹).val)
    (x : RootInvariants.algebra f n hn t v hv d) :
    includeT (descended f n hn t v hv d φ a b μ hμ hφ x)=φ (x:d.S) := by
  have h := (NativeDescent.canonicalAlgEquiv (A := A) B T).apply_symm_apply
    (invariantMap f n hn t v hv d φ a b μ hμ hφ x)
  exact congrArg Subtype.val h
end Lech.FactorDescent


namespace Lech.UniversalFactorMap
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable (w : Tˣ) (a b : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))

lemma polynomial_square : (f.map (algebraMap A B)).map (algebraMap B (R (A := A) (B := B) (T := T)))=
    (f.map (algebraMap A T)).map (includeT (A := A) (B := B)).toRingHom := by
  simp only [Polynomial.map_map]
  congr 1
  rw [← IsScalarTower.algebraMap_eq A B (R (A := A) (B := B) (T := T))]
  exact (includeT (A := A) (B := B)).comp_algebraMap.symm

include hf in
lemma form : ((f.map (algebraMap A B)).map (algebraMap B (R (A := A) (B := B) (T := T)))).homogenize n=
    MvPolynomial.C (Units.map (includeT (A := A) (B := B)).toMonoidHom w:R (A := A) (B := B) (T := T))*∏ i,
      (MvPolynomial.C (includeT (a i))*MvPolynomial.X 0+MvPolynomial.C (includeT (b i))*MvPolynomial.X 1) := by
  rw [polynomial_square,Polynomial.homogenize_map,hf]
  simp only [map_mul,map_prod,map_add,MvPolynomial.map_C,MvPolynomial.map_X]
  rfl

include hv in
lemma value : ((f.map (algebraMap A B)).map (algebraMap B (R (A := A) (B := B) (T := T)))).eval
    (algebraMap B _ t)=(Units.map (algebraMap B (R (A := A) (B := B) (T := T))).toMonoidHom v:R (A := A) (B := B) (T := T)) := by
  rw [Polynomial.eval_map,eval₂_at_apply,hv]
  rfl

 
def denominator (i : Fin n) : (R (A := A) (B := B) (T := T))ˣ :=
  FactorNormalization.denominator _ n (natDegree_map_le.trans (natDegree_map_le.trans hn))
    (algebraMap B _ t) (Units.map (algebraMap B (R (A := A) (B := B) (T := T))).toMonoidHom v)
    (Units.map (includeT (A := A) (B := B)).toMonoidHom w) (value f t v hv)
    (fun i => includeT (a i)) (fun i => includeT (b i)) (form f n w a b hf) i

lemma denominator_val (i : Fin n) :
    (denominator f n hn t v hv w a b hf i:R (A := A) (B := B) (T := T))=
      algebraMap B _ t*includeT (a i)+includeT (b i) :=
  FactorNormalization.denominator_val _ _ _ _ _ _ _ _ _ _ _

lemma factorization :
    (BinaryChange.normalized (f.map (algebraMap A B)) n t v).map (algebraMap B (R (A := A) (B := B) (T := T)))=
      ∏ i,(Polynomial.X-C (-includeT (a i)*((denominator f n hn t v hv w a b hf i)⁻¹).val)) := by
  rw [BinaryCover.map_normalized]
  exact FactorNormalization.normalized_factorization _ _ _ _ _ _ _ _ _ _

 

def splittingMap : d.S →ₐ[B] R (A := A) (B := B) (T := T) :=
  (d.universal _ _ (factorization f n hn t v hv w a b hf)).choose

lemma splittingMap_root (i : Fin n) : splittingMap f n hn t v hv d w a b hf (d.roots i)=
    -includeT (a i)*((denominator f n hn t v hv w a b hf i)⁻¹).val :=
  (d.universal _ _ (factorization f n hn t v hv w a b hf)).choose_spec.1 i

 

def map [Module.FaithfullyFlat A B] : RootInvariants.algebra f n hn t v hv d →ₐ[A] T :=
  descended f n hn t v hv d (splittingMap f n hn t v hv d w a b hf) a b
    (denominator f n hn t v hv w a b hf) (denominator_val f n hn t v hv w a b hf)
    (splittingMap_root f n hn t v hv d w a b hf)

lemma map_include [Module.FaithfullyFlat A B] (x : RootInvariants.algebra f n hn t v hv d) :
    includeT (map f n hn t v hv d w a b hf x)=splittingMap f n hn t v hv d w a b hf (x:d.S) :=
  descended_include f n hn t v hv d _ _ _ _ _ _ x
end Lech.UniversalFactorMap


namespace Lech.FactorDescent
open Polynomial
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma includeT_injective [Module.FaithfullyFlat A B] :
    Function.Injective (includeT (A := A) (B := B) (T := T)) := by
  intro x y h
  apply (NativeDescent.canonicalAlgUnit_bijective (A := A) B T).injective
  exact Subtype.ext h

 

def extend [Module.Flat A B] (g : RootInvariants.algebra f n hn t v hv d →ₐ[A] T) :
    d.S →ₐ[B] R (A := A) (B := B) (T := T) :=
  (Algebra.TensorProduct.map (AlgHom.id B B) g).comp
    (RootInvariants.algebraTensorEquiv f n hn t v hv d).symm.toAlgHom

lemma extend_subtype [Module.Flat A B] (g : RootInvariants.algebra f n hn t v hv d →ₐ[A] T)
    (x : RootInvariants.algebra f n hn t v hv d) :
    extend f n hn t v hv d g (x:d.S)=includeT (g x) := by
  have h : (RootInvariants.algebraTensorEquiv f n hn t v hv d).symm (x:d.S)=(1:B) ⊗ₜ[A] x := by
    apply (RootInvariants.algebraTensorEquiv f n hn t v hv d).injective
    rw [AlgEquiv.apply_symm_apply]
    change (x:d.S)=algebraMap B d.S 1*(x:d.S)
    rw [map_one,one_mul]
  simp only [extend,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,h,
    Algebra.TensorProduct.map_tmul,AlgHom.id_apply]
  rfl

lemma extend_injective [Module.FaithfullyFlat A B] :
    Function.Injective (extend f n hn t v hv d (T := T)) := by
  intro g h H
  ext x
  apply includeT_injective (A := A) (B := B)
  have he := AlgHom.congr_fun H (x:d.S)
  simpa only [extend_subtype] using he

 
lemma point_ext [Module.FaithfullyFlat A B]
    (g h : RootInvariants.algebra f n hn t v hv d →ₐ[A] T)
    (H : ∀ i,extend f n hn t v hv d g (d.roots i)=extend f n hn t v hv d h (d.roots i)) : g=h :=
  extend_injective f n hn t v hv d (d.hom_ext _ _ H)

variable (φ : d.S →ₐ[B] R (A := A) (B := B) (T := T))
  (a b : Fin n → T) (μ : Fin n → (R (A := A) (B := B) (T := T))ˣ)
  (hμ : ∀ i,(μ i:R (A := A) (B := B) (T := T))=algebraMap B _ t*includeT (a i)+includeT (b i))
  (hφ : ∀ i,φ (d.roots i)= -includeT (a i)*((μ i)⁻¹).val)

lemma extend_descended [Module.FaithfullyFlat A B] :
    extend f n hn t v hv d (descended f n hn t v hv d φ a b μ hμ hφ)=φ := by
  apply (AlgHom.cancel_right (RootInvariants.algebraTensorEquiv f n hn t v hv d).surjective).mp
  ext x
  have he : RootInvariants.algebraTensorEquiv f n hn t v hv d ((1:B) ⊗ₜ[A] x)=(x:d.S) := by
    change algebraMap B d.S 1*(x:d.S)=(x:d.S)
    rw [map_one,one_mul]
  change extend f n hn t v hv d (descended f n hn t v hv d φ a b μ hμ hφ)
    (RootInvariants.algebraTensorEquiv f n hn t v hv d ((1:B) ⊗ₜ[A] x))=
      φ (RootInvariants.algebraTensorEquiv f n hn t v hv d ((1:B) ⊗ₜ[A] x))
  rw [he,extend_subtype]
  exact descended_include f n hn t v hv d φ a b μ hμ hφ x

include hμ hφ in
 

theorem unique [Module.FaithfullyFlat A B] :
    ∃! g : RootInvariants.algebra f n hn t v hv d →ₐ[A] T,
      ∀ i,extend f n hn t v hv d g (d.roots i)= -includeT (a i)*((μ i)⁻¹).val := by
  refine ⟨descended f n hn t v hv d φ a b μ hμ hφ,?_,?_⟩
  · intro i
    rw [extend_descended]
    exact hφ i
  · intro g hg
    apply point_ext f n hn t v hv d
    intro i
    rw [extend_descended,hg,hφ]
end Lech.FactorDescent


namespace Lech.UniversalFactorMap
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable (w : Tˣ) (a b : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))

lemma denominator_product :
    Units.map (includeT (A := A) (B := B)).toMonoidHom w*∏ i,denominator f n hn t v hv w a b hf i=
      Units.map (algebraMap B (R (A := A) (B := B) (T := T))).toMonoidHom v :=
  FactorNormalization.unit_product _ _ _ _ _ _ _ _ _ _

lemma recover_selected (σ : Fin n → Bool) (i : Fin n) :
    (denominator f n hn t v hv w a b hf i:R (A := A) (B := B) (T := T))*
      splittingMap f n hn t v hv d w a b hf (RootInvariants.selected f n hn t v hv d σ i:d.S)=
        includeT (if σ i then a i else b i) := by
  let μ := denominator f n hn t v hv w a b hf i
  have hμ : (μ:R (A := A) (B := B) (T := T))=algebraMap B _ t*includeT (a i)+includeT (b i) :=
    denominator_val f n hn t v hv w a b hf i
  have hx : (μ:R (A := A) (B := B) (T := T))*
      (-splittingMap f n hn t v hv d w a b hf (d.roots i))=includeT (a i) := by
    rw [splittingMap_root]
    change (μ:R (A := A) (B := B) (T := T))*(-(-includeT (a i)*(μ⁻¹).val))=includeT (a i)
    simp only [neg_mul,neg_neg]
    rw [mul_left_comm,Units.mul_inv,mul_one]
  simp only [RootInvariants.selected]
  split_ifs
  · change (μ:R (A := A) (B := B) (T := T))*splittingMap f n hn t v hv d w a b hf (-d.roots i)=_
    rw [map_neg]
    exact hx
  · change (μ:R (A := A) (B := B) (T := T))*splittingMap f n hn t v hv d w a b hf
      (1+algebraMap B d.S t*d.roots i)=_
    rw [map_add,map_one,map_mul,AlgHom.commutes]
    calc
      _ = (μ:R (A := A) (B := B) (T := T))-algebraMap B _ t*((μ:R (A := A) (B := B) (T := T))*
        (-splittingMap f n hn t v hv d w a b hf (d.roots i))) := by ring
      _ = includeT (b i) := by rw [hx,hμ];ring

 

lemma map_chartFunction [Module.FaithfullyFlat A B] (σ : Fin n → Bool) :
    map f n hn t v hv d w a b hf (RootInvariants.chartFunction f n hn t v hv d σ)=
      (w:T)*∏ i,if σ i then a i else b i := by
  apply includeT_injective (A := A) (B := B)
  rw [map_include]
  change splittingMap f n hn t v hv d w a b hf
    (algebraMap B d.S (v:B)*∏ i,(RootInvariants.selected f n hn t v hv d σ i:d.S))=_
  rw [map_mul,map_prod,AlgHom.commutes]
  have hvv := congrArg (fun u : (R (A := A) (B := B) (T := T))ˣ => (u:R (A := A) (B := B) (T := T)))
    (denominator_product f n hn t v hv w a b hf)
  simp only [Units.val_mul,Units.coe_map,Units.coe_prod] at hvv
  change includeT (w:T)*∏ i,(denominator f n hn t v hv w a b hf i:R (A := A) (B := B) (T := T))=
    algebraMap B (R (A := A) (B := B) (T := T)) (v:B) at hvv
  rw [←hvv,mul_assoc,←Finset.prod_mul_distrib]
  simp only [recover_selected,map_mul,map_prod]
end Lech.UniversalFactorMap


namespace Lech.StandardFactorCharts
open Polynomial
universe u
variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
variable (D : Subalgebra A S) (n : ℕ) (P : Fin n → Bool → S)
  (v : Sˣ) (c : (Fin n → Bool) → D)
  (hc : ∀ σ,(c σ:S)=(v:S)*∏ i,P i (σ i))
variable {T : Type u} [CommRing T] [Algebra A T]

include hc in
lemma map_coordinate_relation (σ : Fin n → Bool) (ψ : L D n c σ →ₐ[A] T) (φ : S →ₐ[A] T)
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

 

lemma normalized_root {R : Type*} [CommRing R] (x t a b α : R) (μ : Rˣ)
    (hμ : (μ:R)=t*a+b) (ha : a*α= -x) (hb : b*α=1+t*x) :
    x= -a*(μ⁻¹).val := by
  have hm : (μ:R)*α=1 := by
    rw [hμ,add_mul,mul_assoc,ha,hb]
    ring
  have hα : α=(μ⁻¹).val := by
    calc
      α = ((μ⁻¹).val*(μ:R))*α := by rw [Units.inv_mul,one_mul]
      _ = (μ⁻¹).val := by rw [mul_assoc,hm,mul_one]
  rw [←hα,neg_mul,ha,neg_neg]
end Lech.StandardFactorCharts
end
end

end OAI
