import Mathlib
import OAI.RingTheory.Multiplicity.RootInvariantsWeightZero

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
namespace Lech.StandardFactorCharts
open Polynomial
universe u
variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
variable (D : Subalgebra A S) (n : ℕ) (P : Fin n → Bool → S)
  (v : Sˣ) (c : (Fin n → Bool) → D)
  (hc : ∀ σ,(c σ:S)=(v:S)*∏ i,P i (σ i))

abbrev L (σ : Fin n → Bool) := Localization.Away (c σ)
abbrev E (σ : Fin n → Bool) := Localization.Away (D.val (c σ))

def embedding (σ : Fin n → Bool) : L D n c σ →ₐ[A] E D n c σ :=
  IsLocalization.Away.mapₐ _ _ D.val (c σ)

lemma embedding_injective (σ : Fin n → Bool) : Function.Injective (embedding D n c σ) :=
  IsLocalization.Away.mapₐ_injective_of_injective (f := D.val) (c σ) Subtype.val_injective

lemma embedding_map (σ : Fin n → Bool) (x : D) :
    embedding D n c σ (algebraMap D (L D n c σ) x)=algebraMap S (E D n c σ) (x:S) := by
  change IsLocalization.Away.map (L D n c σ) (E D n c σ) D.val.toRingHom (c σ)
    (algebraMap D (L D n c σ) x)=algebraMap S (E D n c σ) (D.val x)
  dsimp only [IsLocalization.Away.map]
  exact IsLocalization.map_eq _ x

def chartUnit (σ : Fin n → Bool) : (L D n c σ)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (c σ)).unit

lemma chartUnit_val (σ : Fin n → Bool) : (chartUnit D n c σ:L D n c σ)=algebraMap D _ (c σ) :=
  (IsLocalization.Away.algebraMap_isUnit (c σ)).unit_spec

 
def coordinate (σ : Fin n → Bool) (i : Fin n) (b : Bool) : L D n c σ :=
  algebraMap D _ (c (Function.update σ i b))*((chartUnit D n c σ)⁻¹).val

lemma coordinate_selected (σ : Fin n → Bool) (i : Fin n) : coordinate D n c σ i (σ i)=1 := by
  simp only [coordinate,Function.update_eq_self]
  rw [← chartUnit_val,Units.mul_inv]

include hc in
lemma cross_identity (σ : Fin n → Bool) (i : Fin n) (b : Bool) :
    (c σ:S)*P i b=(c (Function.update σ i b):S)*P i (σ i) := by
  classical
  rw [hc,hc]
  have he : (∏ j ∈ Finset.univ.erase i,P j (Function.update σ i b j))=
      ∏ j ∈ Finset.univ.erase i,P j (σ j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j => P j (Function.update σ i b j)) (Finset.mem_univ i)]
  rw [he,Function.update_self]
  ring

include hc in
lemma coordinate_relation (σ : Fin n → Bool) (i : Fin n) (b : Bool) :
    embedding D n c σ (coordinate D n c σ i b)*algebraMap S (E D n c σ) (P i (σ i))=
      algebraMap S (E D n c σ) (P i b) := by
  have h := congrArg (algebraMap S (E D n c σ)) (cross_identity D n P v c hc σ i b)
  simp only [map_mul] at h
  have hu := congrArg (embedding D n c σ) (Units.mul_inv (chartUnit D n c σ))
  rw [map_mul,chartUnit_val,embedding_map,map_one] at hu
  rw [coordinate,map_mul,embedding_map]
  calc
    algebraMap S _ (c (Function.update σ i b):S)*
        embedding D n c σ ((chartUnit D n c σ)⁻¹).val*algebraMap S _ (P i (σ i)) =
      (algebraMap S _ (c (Function.update σ i b):S)*algebraMap S _ (P i (σ i)))*
        embedding D n c σ ((chartUnit D n c σ)⁻¹).val := by ring
    _ = (algebraMap S _ (c σ:S)*algebraMap S _ (P i b))*
        embedding D n c σ ((chartUnit D n c σ)⁻¹).val := by rw [h]
    _ = algebraMap S _ (P i b)*(algebraMap S _ (c σ:S)*
        embedding D n c σ ((chartUnit D n c σ)⁻¹).val) := by ring
    _ = algebraMap S _ (P i b) := by rw [hu,mul_one]
 
lemma normalize_product {R : Type*} [CommRing R] (m : ℕ)
    (P Q : Fin m → Bool → R) (σ : Fin m → Bool) (r d : R)
    (hd : d=r*∏ i,P i (σ i))
    (hQ : ∀ i b,Q i b*P i (σ i)=P i b) :
    MvPolynomial.C r*∏ i : Fin m,(MvPolynomial.C (P i true)*MvPolynomial.X (0:Fin 2)+
      MvPolynomial.C (P i false)*MvPolynomial.X 1)=
    MvPolynomial.C d*∏ i : Fin m,(MvPolynomial.C (Q i true)*MvPolynomial.X (0:Fin 2)+
      MvPolynomial.C (Q i false)*MvPolynomial.X 1) := by
  rw [hd,map_mul,map_prod,mul_assoc,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_add,← mul_assoc,← MvPolynomial.C_mul, mul_comm (P i (σ i)),hQ]
  rw [← mul_assoc,← MvPolynomial.C_mul,mul_comm (P i (σ i)),hQ]

include hc in
 

lemma chart_factorization (f : A[X])
    (hf : MvPolynomial.map (algebraMap A S) (f.homogenize n)=
      MvPolynomial.C (v:S)*∏ i : Fin n,(MvPolynomial.C (P i true)*MvPolynomial.X 0+
        MvPolynomial.C (P i false)*MvPolynomial.X 1)) (σ : Fin n → Bool) :
    MvPolynomial.map (algebraMap A (L D n c σ)) (f.homogenize n)=
      MvPolynomial.C (chartUnit D n c σ:L D n c σ)*∏ i : Fin n,
        (MvPolynomial.C (coordinate D n c σ i true)*MvPolynomial.X 0+
          MvPolynomial.C (coordinate D n c σ i false)*MvPolynomial.X 1) := by
  apply MvPolynomial.map_injective (embedding D n c σ).toRingHom (embedding_injective D n c σ)
  simp only [map_mul,map_prod,map_add,MvPolynomial.map_C,MvPolynomial.map_X]
  have hco : (embedding D n c σ).toRingHom.comp (algebraMap A (L D n c σ))=
      (algebraMap S (E D n c σ)).comp (algebraMap A S) := by
    exact (embedding D n c σ).comp_algebraMap.trans
      (IsScalarTower.algebraMap_eq A S (E D n c σ))
  rw [MvPolynomial.map_map,hco,← MvPolynomial.map_map,hf]
  simp only [map_mul,map_prod,map_add,MvPolynomial.map_C,MvPolynomial.map_X]
  refine normalize_product n (fun i b => algebraMap S (E D n c σ) (P i b))
    (fun i b => embedding D n c σ (coordinate D n c σ i b)) σ
    (algebraMap S (E D n c σ) (v:S)) (embedding D n c σ (chartUnit D n c σ)) ?_ ?_
  · rw [chartUnit_val,embedding_map,hc,map_mul,map_prod]
  · exact coordinate_relation D n P v c hc σ

end Lech.StandardFactorCharts


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

def pair (i : Fin n) (b : Bool) : d.S :=
  if b then (sectionX f n hn t v hv d i:d.S) else (sectionY f n hn t v hv d i:d.S)

lemma pair_product (σ : Fin n → Bool) : (chartFunction f n hn t v hv d σ:d.S)=
    (Units.map (algebraMap B d.S).toMonoidHom v:d.S)*∏ i,pair f n hn t v hv d i (σ i) := by
  rw [chartFunction_val]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases h : σ i <;> simp only [selected,pair,h,Bool.false_eq_true,↓reduceIte]

abbrev chartRing (σ : Fin n → Bool) :=
  StandardFactorCharts.L (algebra f n hn t v hv d) n (chartFunction f n hn t v hv d) σ

def chartCoordinate (σ : Fin n → Bool) (i : Fin n) (b : Bool) : chartRing f n hn t v hv d σ :=
  StandardFactorCharts.coordinate (algebra f n hn t v hv d) n (chartFunction f n hn t v hv d) σ i b

def chartUnit (σ : Fin n → Bool) : (chartRing f n hn t v hv d σ)ˣ :=
  StandardFactorCharts.chartUnit (algebra f n hn t v hv d) n (chartFunction f n hn t v hv d) σ

lemma chartCoordinate_selected (σ : Fin n → Bool) (i : Fin n) :
    chartCoordinate f n hn t v hv d σ i (σ i)=1 :=
  StandardFactorCharts.coordinate_selected _ _ _ _ _

lemma sections_binary_form_unit : MvPolynomial.map (algebraMap A d.S) (f.homogenize n)=
    MvPolynomial.C (algebraMap B d.S (v:B))*∏ i : Fin n,
      (MvPolynomial.C (pair f n hn t v hv d i true)*MvPolynomial.X 0+
        MvPolynomial.C (pair f n hn t v hv d i false)*MvPolynomial.X 1) := by
  have h := congrArg (fun p : MvPolynomial (Fin 2) d.S => MvPolynomial.C (algebraMap B d.S (v:B))*p)
    (sections_binary_form f n hn t v hv d)
  change MvPolynomial.C (algebraMap B d.S (v:B))*(MvPolynomial.C (algebraMap B d.S (v⁻¹:Bˣ))*_)=_ at h
  rw [←mul_assoc,←MvPolynomial.C_mul,←map_mul,Units.mul_inv,map_one,map_one,one_mul] at h
  exact h


lemma chart_factorization (σ : Fin n → Bool) :
    (f.map (algebraMap A (chartRing f n hn t v hv d σ))).homogenize n=
      MvPolynomial.C (chartUnit f n hn t v hv d σ:chartRing f n hn t v hv d σ)*∏ i : Fin n,
        (MvPolynomial.C (chartCoordinate f n hn t v hv d σ i true)*MvPolynomial.X 0+
          MvPolynomial.C (chartCoordinate f n hn t v hv d σ i false)*MvPolynomial.X 1) := by
  rw [Polynomial.homogenize_map]
  exact StandardFactorCharts.chart_factorization (algebra f n hn t v hv d) n
    (pair f n hn t v hv d) (Units.map (algebraMap B d.S).toMonoidHom v)
    (chartFunction f n hn t v hv d) (pair_product f n hn t v hv d) f
    (sections_binary_form_unit f n hn t v hv d) σ
end Lech.RootInvariants


namespace Lech.FactorNormalization

section
open Polynomial
universe u
variable {A : Type u} [CommRing A]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : A) (v w : Aˣ)
  (hv : f.eval t=(v:A)) (a b : Fin n → A)
  (hf : f.homogenize n=MvPolynomial.C (w:A)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))

include hn hv hf in
lemma evaluation_product : (v:A)=(w:A)*∏ i,(t*a i+b i) := by
  have h := congrArg (MvPolynomial.aeval ![t,1]) hf
  rw [Polynomial.aeval_homogenize_of_eq_one hn _ rfl] at h
  simpa [mul_comm] using hv.symm.trans h

include hn hv hf in
lemma factor_value_unit (i : Fin n) : IsUnit (t*a i+b i) := by
  have h : IsUnit (∏ i,(t*a i+b i)) := by
    apply isUnit_of_mul_isUnit_right (x := (w:A))
    rw [← evaluation_product f n hn t v w hv a b hf]
    exact v.isUnit
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => t*a i+b i) (Finset.mem_univ i)) h


def denominator (i : Fin n) : Aˣ :=
  (factor_value_unit f n hn t v w hv a b hf i).unit

lemma denominator_val (i : Fin n) :
    (denominator f n hn t v w hv a b hf i:A)=t*a i+b i :=
  (factor_value_unit f n hn t v w hv a b hf i).unit_spec

def roots (i : Fin n) : A := -a i*(denominator f n hn t v w hv a b hf i)⁻¹

lemma unit_product : w*∏ i,denominator f n hn t v w hv a b hf i=v := by
  apply Units.ext
  simpa only [Units.val_mul,Units.coe_prod,denominator_val] using
    (evaluation_product f n hn t v w hv a b hf).symm

lemma transform_factor (i : Fin n) :
    C (a i)*(C t*Polynomial.X+1)+C (b i)*Polynomial.X=
      C (denominator f n hn t v w hv a b hf i:A)*
        (Polynomial.X-C (roots f n hn t v w hv a b hf i)) := by
  let μ := denominator f n hn t v w hv a b hf i
  have hμ : (μ:A)=t*a i+b i := denominator_val f n hn t v w hv a b hf i
  have hroot : (μ:A)*roots f n hn t v w hv a b hf i= -a i := by
    change (μ:A)*(-a i*↑μ⁻¹)= -a i
    rw [mul_left_comm,Units.mul_inv,mul_one]
  rw [mul_sub,← C_mul,hroot,C_neg,sub_neg_eq_add,hμ,C_add,C_mul]
  ring

lemma normalized_factorization : BinaryChange.normalized f n t v=∏ i,(Polynomial.X-C (roots f n hn t v w hv a b hf i)) := by
  have ht : BinaryChange.transform f n t=C (w:A)*∏ i,
      (C (denominator f n hn t v w hv a b hf i:A)*(Polynomial.X-C (roots f n hn t v w hv a b hf i))) := by
    rw [BinaryChange.transform_eq_aeval,hf,map_mul,map_prod]
    simp only [MvPolynomial.aeval_C]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simpa using transform_factor f n hn t v w hv a b hf i
  have hu : (v⁻¹:Aˣ)*w*∏ i,denominator f n hn t v w hv a b hf i=1 := by
    rw [mul_assoc,unit_product,inv_mul_cancel]
  have hc := congrArg (fun u : Aˣ => (u:A)) hu
  simp only [Units.val_mul,Units.coe_prod,Units.val_one] at hc
  rw [BinaryChange.normalized,ht,Finset.prod_mul_distrib,← map_prod C,
    ← mul_assoc,← mul_assoc,← C_mul,← C_mul,hc,C_1,one_mul]

lemma recover_X (i : Fin n) :
    (denominator f n hn t v w hv a b hf i:A)*(-roots f n hn t v w hv a b hf i)=a i := by
  let μ := denominator f n hn t v w hv a b hf i
  change (μ:A)*(-(-a i*↑μ⁻¹))=a i
  simp only [neg_mul,neg_neg]
  rw [mul_left_comm,Units.mul_inv,mul_one]

lemma recover_Y (i : Fin n) :
    (denominator f n hn t v w hv a b hf i:A)*(1+t*roots f n hn t v w hv a b hf i)=b i := by
  have hx := recover_X f n hn t v w hv a b hf i
  have hvv := denominator_val f n hn t v w hv a b hf i
  calc
    _ = (denominator f n hn t v w hv a b hf i:A)-
        t*((denominator f n hn t v w hv a b hf i:A)*(-roots f n hn t v w hv a b hf i)) := by ring
    _ = b i := by rw [hx,hvv];ring


theorem universal (d : UniversalSplitting.Data A n (BinaryChange.normalized f n t v)) :
    ∃! φ : d.S →ₐ[A] A, ∀ i, φ (d.roots i)=roots f n hn t v w hv a b hf i := by
  apply d.universal A
  simpa using normalized_factorization f n hn t v w hv a b hf

variable {T : Type u} [CommRing T] [Algebra A T]
  (W : Tˣ) (p q : Fin n → T)
  (hF : MvPolynomial.map (algebraMap A T) (f.homogenize n)=
    MvPolynomial.C (W:T)*∏ i,
      (MvPolynomial.C (p i)*MvPolynomial.X 0+MvPolynomial.C (q i)*MvPolynomial.X 1))

include hv in
lemma mapped_value : (f.map (algebraMap A T)).eval (algebraMap A T t)=
    (Units.map (algebraMap A T).toMonoidHom v:T) := by
  rw [Polynomial.eval_map,eval₂_at_apply,hv]
  rfl

include hF in
lemma mapped_form : (f.map (algebraMap A T)).homogenize n=
    MvPolynomial.C (W:T)*∏ i,
      (MvPolynomial.C (p i)*MvPolynomial.X 0+MvPolynomial.C (q i)*MvPolynomial.X 1) := by
  rw [Polynomial.homogenize_map]
  exact hF


theorem universal_over (d : UniversalSplitting.Data A n (BinaryChange.normalized f n t v)) :
    ∃! φ : d.S →ₐ[A] T, ∀ i, φ (d.roots i)=
      roots (f.map (algebraMap A T)) n (natDegree_map_le.trans hn) (algebraMap A T t)
        (Units.map (algebraMap A T).toMonoidHom v) W (mapped_value f t v hv) p q
        (mapped_form f n W p q hF) i := by
  apply d.universal T
  rw [BinaryCover.map_normalized]
  exact normalized_factorization _ _ _ _ _ _ _ _ _ _

end


universe u
variable {R : Type u} [CommRing R]

 
lemma change_denominator (a b s t : R) (μ ν : Rˣ)
    (hμ : (μ:R)=s*a+b) (hν : (ν:R)=t*a+b) :
    1+(s-t)*(-a*(μ⁻¹:Rˣ))=((ν*μ⁻¹:Rˣ):R) := by
  simp only [Units.val_mul]
  calc
    _ = ((μ:R)-(s-t)*a)*(μ⁻¹:Rˣ) := by
      calc
        _ = (μ:R)*(μ⁻¹:Rˣ) - ((s-t)*a)*(μ⁻¹:Rˣ) := by rw [Units.mul_inv];ring
        _ = _ := (sub_mul _ _ _).symm
    _ = _ := by rw [hμ,hν];ring


lemma change_root (a b s t : R) (μ ν : Rˣ)
    (hμ : (μ:R)=s*a+b) (hν : (ν:R)=t*a+b) :
    RootGluing.rootShift (s-t) (-a*(μ⁻¹:Rˣ))= -a*(ν⁻¹:Rˣ) := by
  rw [RootGluing.rootShift,change_denominator a b s t μ ν hμ hν,Ring.inverse_unit]
  simp only [mul_inv_rev,inv_inv,Units.val_mul]
  rw [← mul_assoc,mul_assoc (-a),Units.inv_mul,mul_one]

open Polynomial
variable (f : R[X]) (n : ℕ) (hn : f.natDegree≤n) (s t : R) (v w c : Rˣ)
  (hs : f.eval s=(v:R)) (ht : f.eval t=(w:R)) (a b : Fin n → R)
  (hf : f.homogenize n=MvPolynomial.C (c:R)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))

lemma roots_reparam (i : Fin n) :
    RootGluing.rootShift (s-t) (roots f n hn s v c hs a b hf i)=
      roots f n hn t w c ht a b hf i :=
  change_root (a i) (b i) s t _ _
    (denominator_val f n hn s v c hs a b hf i)
    (denominator_val f n hn t w c ht a b hf i)
end Lech.FactorNormalization


namespace Lech.FFTensorMaps
open scoped TensorProduct
universe u v w w' z
variable {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  [Module.FaithfullyFlat R S]
variable {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

lemma bijective_baseChange_iff (f : M →ₗ[R] N) : Function.Bijective (f.baseChange S) ↔ Function.Bijective f := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact and_congr (Module.FaithfullyFlat.lTensor_injective_iff_injective R S f)
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S f)

variable {Q : Type z} [AddCommGroup Q] [Module S Q]
lemma bijective (f : M →ₗ[R] N) (e : S ⊗[R] M ≃ₗ[S] Q) (e' : S ⊗[R] N ≃ₗ[S] Q)
    (h : e'.toLinearMap.comp (f.baseChange S)=e.toLinearMap) : Function.Bijective f := by
  apply (bijective_baseChange_iff S f).mp
  have he (x) : e' ((f.baseChange S) x)=e x := LinearMap.congr_fun h x
  constructor
  · intro x y hxy
    apply e.injective
    rw [← he x,← he y,hxy]
  · intro y
    obtain ⟨x,hx⟩ := e.surjective (e' y)
    exact ⟨x,e'.injective ((he x).trans hx)⟩
end Lech.FFTensorMaps


namespace Lech.NativeDescent
open scoped TensorProduct
open TensorProduct
universe u v w
variable {A : Type u} (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
  (N : Type w) [AddCommGroup N] [Module A N]

 
def canonical : B ⊗[A] N →ₗ[B] B ⊗[A] (B ⊗[A] N) :=
  AlgebraTensorModule.lTensor B B (TensorProduct.mk A B N 1)

lemma canonical_counit :
    (evaluation (A := A) (B := B) (M := B ⊗[A] N)).comp (canonical (A := A) B N)=LinearMap.id := by
  ext x
  simp [evaluation,canonical]

lemma canonical_coassoc :
    (AlgebraTensorModule.lTensor B B inclusion).comp (canonical (A := A) B N)=
      (AlgebraTensorModule.lTensor B B ((canonical (A := A) B N).restrictScalars A)).comp (canonical (A := A) B N) := by
  ext x
  simp [inclusion,canonical]

 
def canonicalUnit : N →ₗ[A] invariants (canonical (A := A) B N) :=
  (TensorProduct.mk A B N 1).codRestrict _ (fun x => by
    change canonical (A := A) B N (1 ⊗ₜ[A] x)=(1:B) ⊗ₜ[A] (1 ⊗ₜ[A] x)
    rfl)

lemma canonical_compat [Module.Flat A B] :
    (tensorEquiv (canonical (A := A) B N) (canonical_counit (A := A) B N) (canonical_coassoc (A := A) B N)).toLinearMap.comp
      ((canonicalUnit (A := A) B N).baseChange B)=LinearMap.id := by
  ext x
  change (1:B) • ((1:B) ⊗ₜ[A] x)=(1:B) ⊗ₜ[A] x
  rw [one_smul]

lemma canonicalUnit_bijective [Module.FaithfullyFlat A B] :
    Function.Bijective (canonicalUnit (A := A) B N) := by
  apply (FFTensorMaps.bijective_baseChange_iff (R := A) (M := N)
    (N := invariants (A := A) (canonical (A := A) B N)) B
    (canonicalUnit (A := A) B N)).mp
  have h := canonical_compat (A := A) B N
  let he := tensorEquiv (canonical (A := A) B N)
    (canonical_counit (A := A) B N) (canonical_coassoc (A := A) B N)
  have hf : (canonicalUnit (A := A) B N).baseChange B=he.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply he.injective
    change he ((canonicalUnit (A := A) B N).baseChange B x)=he (he.symm x)
    rw [he.apply_symm_apply]
    exact LinearMap.congr_fun h x
  rw [hf]
  exact he.symm.bijective

def canonicalEquiv [Module.FaithfullyFlat A B] : N ≃ₗ[A] invariants (canonical (A := A) B N) := by
  apply LinearEquiv.ofBijective (canonicalUnit (A := A) B N)
  exact canonicalUnit_bijective B N
end Lech.NativeDescent

end

end OAI
