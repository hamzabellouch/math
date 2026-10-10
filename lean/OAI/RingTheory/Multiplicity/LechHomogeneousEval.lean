import Mathlib
import OAI.RingTheory.Multiplicity.ProductSourceCoverRootSigned

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
open MvPolynomial
open scoped BigOperators
universe u v w
variable {R : Type u} [CommSemiring R] {S : Type v} [CommSemiring S] {ι : Type w}
lemma homogeneous_eval_scale (f : R →+* S) (g : ι → S) (t : S)
    {p : MvPolynomial ι R} {n : ℕ} (hp : p.IsHomogeneous n) :
    eval₂ f (fun i => t*g i) p=t^n*eval₂ f g p := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [eval₂_add,ihp,ihq,mul_add]
  | monomial d r hd =>
    simp only [eval₂_monomial,mul_pow,Finsupp.prod,Finset.prod_mul_distrib]
    have hd' : ∑ i ∈ d.support,d i=n := by
      simpa only [Finsupp.weight_apply,Finsupp.sum,Pi.one_apply,smul_eq_mul,mul_one] using hd
    rw [Finset.prod_pow_eq_pow_sum,hd']
    ring
end Lech


namespace Lech.ProjectiveCoefficientChart

section
open MvPolynomial HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
attribute [local instance] MvPolynomial.gradedAlgebra
lemma coordinate_self : coordinate R n k k=1 := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (X k))
  rw [coordinate_val,HomogeneousLocalization.val_one,Localization.mk_eq_mk']
  exact IsLocalization.mk'_self' (Ambient R n k)
lemma forward_coefficient (j : Fin (n+1)) :
    forward R n k (UniversalCoefficientChart.coefficient R n k j)=coordinate R n k j := by
  by_cases h : j=k
  · subst j
    rw [UniversalCoefficientChart.coefficient_self,map_one,coordinate_self]
  · rw [UniversalCoefficientChart.coefficient, dite_eq_right h]
    simp [forward]
lemma coordinate_mul (j : Fin (n+1)) :
    algebraMap (MvPolynomial (Fin (n+1)) R) (Ambient R n k) (X k)*
      (coordinate R n k j).val=algebraMap (MvPolynomial (Fin (n+1)) R) (Ambient R n k) (X j) := by
  rw [coordinate_val,Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec' (Ambient R n k) (X j) (⟨X k,⟨1,by simp⟩⟩ : Submonoid.powers (X (R:=R) k))
lemma inclusion_forward_evaluate (p : MvPolynomial (Fin (n+1)) R) :
    inclusion R n k (forward R n k (evaluate R n k p))=
      eval₂ (algebraMap R (Ambient R n k)) (fun j => (coordinate R n k j).val) p := by
  have he : (inclusion R n k).comp ((forward R n k).comp (evaluate R n k))=
      MvPolynomial.aeval (fun j => (coordinate R n k j).val) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply,evaluate,aeval_X,forward_coefficient]
    rfl
  exact DFunLike.congr_fun he p
lemma homogeneous_identity (d : ℕ) (p : MvPolynomial (Fin (n+1)) R)
    (hp : p.IsHomogeneous d) :
    (inclusion R n k (forward R n k (evaluate R n k p)))*
      algebraMap (MvPolynomial (Fin (n+1)) R) (Ambient R n k) (X k)^d=
      algebraMap _ _ p := by
  rw [inclusion_forward_evaluate,mul_comm]
  have hs := homogeneous_eval_scale (algebraMap R (Ambient R n k))
    (fun j => (coordinate R n k j).val)
    (algebraMap (MvPolynomial (Fin (n+1)) R) (Ambient R n k) (X k)) hp
  simp only [coordinate_mul] at hs
  rw [←hs]
  have he : MvPolynomial.aeval
      (fun j : Fin (n+1) => algebraMap (MvPolynomial (Fin (n+1)) R) (Ambient R n k) (X j))=
      IsScalarTower.toAlgHom R (MvPolynomial (Fin (n+1)) R) (Ambient R n k) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp
  exact DFunLike.congr_fun he p
lemma forward_backward (x : Chart R n k) : forward R n k (backward R n k x)=x := by
  obtain ⟨d,p,hp,rfl⟩ := Away.mk_surjective (grading R n) (isHomogeneous_X R k) x
  rw [backward_mk]
  apply HomogeneousLocalization.val_injective (Submonoid.powers (X k))
  change (inclusion R n k (forward R n k (evaluate R n k p)))=
    Localization.mk p (⟨X k ^ d,⟨d,rfl⟩⟩ : Submonoid.powers (X (R:=R) k))
  rw [Localization.mk_eq_mk',IsLocalization.eq_mk'_iff_mul_eq]
  change _ * algebraMap (MvPolynomial (Fin (n+1)) R) (Ambient R n k) (X k ^ d)=_
  rw [map_pow]
  exact homogeneous_identity R n k d p (by simpa using hp)
 

def equiv : UniversalCoefficientChart.Ring R n k ≃ₐ[R] Chart R n k :=
  AlgEquiv.ofAlgHom (forward R n k) (backward R n k)
    (AlgHom.ext (fun x => forward_backward R n k x))
    (AlgHom.ext (fun x => backward_forward R n k x))
end


open MvPolynomial HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
attribute [local instance] MvPolynomial.gradedAlgebra
variable {d : ℕ} (g : MvPolynomial (Fin (n+1)) R) (hg : g∈grading R n d)
abbrev Overlap := Away (grading R n) (X k*g)
def overlapMap : Chart R n k →+* Overlap R n k g :=
  HomogeneousLocalization.awayMap (grading R n) hg rfl
@[instance_reducible] def overlapChartAlgebra : Algebra (Chart R n k) (Overlap R n k g) :=
  (overlapMap R n k g hg).toAlgebra
def overlapCoefficientMap : UniversalCoefficientChart.Ring R n k →+* Overlap R n k g :=
  (overlapMap R n k g hg).comp (equiv R n k).toRingHom
@[instance_reducible] def overlapCoefficientAlgebra : Algebra (UniversalCoefficientChart.Ring R n k) (Overlap R n k g) :=
  (overlapCoefficientMap R n k g hg).toAlgebra
lemma backward_localizationElem :
    backward R n k (Away.isLocalizationElem (isHomogeneous_X R k) hg)=evaluate R n k g := by
  convert backward_mk R n k d g (by simpa using hg) using 1; simp [Away.isLocalizationElem]
lemma equiv_evaluate_localizationElem :
    equiv R n k (evaluate R n k g)=Away.isLocalizationElem (isHomogeneous_X R k) hg := by
  apply (equiv R n k).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  exact (backward_localizationElem R n k g hg).symm
 

theorem overlap_isLocalization :
    let := overlapCoefficientAlgebra R n k g hg
    IsLocalization.Away (evaluate R n k g) (Overlap R n k g) := by
  let := overlapCoefficientAlgebra R n k g hg
  let := overlapChartAlgebra R n k g hg
  let : IsLocalization.Away (Away.isLocalizationElem (isHomogeneous_X R k) hg)
      (Overlap R n k g) := Away.isLocalization_mul (isHomogeneous_X R k) hg rfl (by decide)
  apply IsLocalization.of_ringEquiv_left (equiv R n k).toRingEquiv
    (M₁:=Submonoid.powers (Away.isLocalizationElem (isHomogeneous_X R k) hg))
  · rw [Submonoid.map_powers]
    congr 1
    exact equiv_evaluate_localizationElem R n k g hg
  · intro a
    rfl
end Lech.ProjectiveCoefficientChart


namespace Lech.ProductSourceCover

section

section
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma chartScalar_coefficient_unit (σ : Chart n) (k : Fin (n+1)) :
    IsUnit (chartScalar R n σ ((ProductLinearChart.product R n σ).coeff k)) := by
  change IsUnit (embed R n (ProductLaurent.chartMap R n σ _))
  rw [ProductLaurent.chartMap_coefficient,map_mul]
  apply IsUnit.mul
  · exact (Units.isUnit ((ProductLaurent.chartUnit R n σ)⁻¹)).map (embed R n)
  · simpa only [denominator,AwayCover.denominator,Finset.prod_singleton] using denominator_unit R n {k}
 

def localizedChart (σ : Chart n) (k : Fin (n+1)) :
    ProductLinearChart.chart R n σ k →ₐ[R] GridAmbient R n :=
  IsLocalization.Away.liftAlgHom ((ProductLinearChart.product R n σ).coeff k)
    (chartScalar_coefficient_unit R n σ k)
lemma localizedChart_algebraMap (σ : Chart n) (k : Fin (n+1)) (a : ProductLinearChart.Ring R n) :
    localizedChart R n σ k (algebraMap (ProductLinearChart.Ring R n) (ProductLinearChart.chart R n σ k) a)=
      chartScalar R n σ a := IsLocalization.Away.lift_eq _ (chartScalar_coefficient_unit R n σ k) _
lemma chartScalar_injective (σ : Chart n) : Function.Injective (chartScalar R n σ) :=
  (embed_injective R n).comp (ProductLaurent.chartMap_injective R n σ)
lemma localizedChart_injective (σ : Chart n) (k : Fin (n+1)) :
    Function.Injective (localizedChart R n σ k) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers ((ProductLinearChart.product R n σ).coeff k))
    (localizedChart R n σ k).toRingHom).mpr
  intro a b
  simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,localizedChart_algebraMap]
  constructor
  · intro h
    simpa only [localizedChart_algebraMap] using congrArg (localizedChart R n σ k) h
  · intro h
    exact congrArg (algebraMap (ProductLinearChart.Ring R n) (ProductLinearChart.chart R n σ k))
      (chartScalar_injective R n σ h)
lemma twistExponent_add (m l : Fin n → ℤ) (σ : Chart n) :
    twistExponent n (m+l) σ=twistExponent n m σ+twistExponent n l σ := by
  ext i
  cases hs : σ i <;> simp [twistExponent_apply,hs]
lemma twistExponent_level (m : Fin n → ℤ) (σ : Chart n) (N : ℕ) :
    twistExponent n (levelTwist n m 1 N) σ=twistExponent n m σ+N • twistExponent n (fun _ => 1) σ := by
  ext i
  cases hs : σ i <;> simp [twistExponent_apply,levelTwist,hs]
lemma monomialUnit_nsmul (e : Exponent n) (N : ℕ) :
    ProductLaurent.monomialUnit R n (N • e)=ProductLaurent.monomialUnit R n e^N := by
  induction N with
  | zero => rw [zero_smul,pow_zero];apply Units.ext;rfl
  | succ N ih => rw [succ_nsmul,ProductLaurent.monomialUnit_add,ih,pow_succ]
lemma chartLine_level (m : Fin n → ℤ) (σ : Chart n) (N : ℕ) (a : ProductLinearChart.Ring R n) :
    chartLine R n (levelTwist n m 1 N) σ a=
      (ProductLaurent.chartUnit R n σ:Ambient R n)^N*chartLine R n m σ a := by
  change (ProductLaurent.monomialUnit R n (twistExponent n (levelTwist n m 1 N) σ):Ambient R n)*_= _
  rw [twistExponent_level,ProductLaurent.monomialUnit_add,monomialUnit_nsmul,←chartUnit_monomial]
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,AlgHom.toLinearMap_apply]
  change _=(ProductLaurent.chartUnit R n σ:Ambient R n)^N*
    ((ProductLaurent.monomialUnit R n (twistExponent n m σ):Ambient R n)*ProductLaurent.chartMap R n σ a)
  ring

def localizedLine (m : Fin n → ℤ) (σ : Chart n) (k : Fin (n+1)) :
    ProductLinearChart.chart R n σ k →ₗ[R] GridAmbient R n :=
  (LinearMap.mulLeft R (embed R n (ProductLaurent.monomialUnit R n (twistExponent n m σ):Ambient R n))).comp
    (localizedChart R n σ k).toLinearMap
lemma localizedLine_apply (m : Fin n → ℤ) (σ : Chart n) (k : Fin (n+1))
    (z : ProductLinearChart.chart R n σ k) :
    localizedLine R n m σ k z=embed R n (ProductLaurent.monomialUnit R n (twistExponent n m σ):Ambient R n)*
      localizedChart R n σ k z := rfl
lemma targetCoeff_chart (σ : Chart n) (k : Fin (n+1)) :
    embed R n (targetCoeff R n k)=embed R n (ProductLaurent.chartUnit R n σ:Ambient R n)*
      chartScalar R n σ ((ProductLinearChart.product R n σ).coeff k) := by
  change _=embed R n _ * embed R n (ProductLaurent.chartMap R n σ _)
  rw [ProductLaurent.chartMap_coefficient,map_mul,←mul_assoc,←map_mul,Units.mul_inv,map_one,one_mul]
lemma localizedLine_mem (m : Fin n → ℤ) (σ : Chart n) (k : Fin (n+1))
    (z : ProductLinearChart.chart R n σ k) : localizedLine R n m σ k z∈grid R n m {k} {σ} := by
  obtain ⟨N,a,ha⟩ := IsLocalization.Away.surj ((ProductLinearChart.product R n σ).coeff k) z
  have ha' := congrArg (localizedChart R n σ k) ha
  simp only [map_mul,map_pow,localizedChart_algebraMap] at ha'
  refine ⟨N,chartLine R n (levelTwist n m 1 N) σ a,?_,?_⟩
  · simpa only [Finset.card_singleton] using chartLine_mem R n (levelTwist n m 1 N) σ a
  · simp only [denominator,AwayCover.denominator,Finset.prod_singleton]
    rw [targetCoeff_chart R n σ k,mul_pow,
      localizedLine_apply,chartLine_level,map_mul,map_pow]
    simp only [chartLine,LinearMap.comp_apply,LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply,map_mul]
    change _=embed R n (ProductLaurent.chartUnit R n σ:Ambient R n)^N*
      (embed R n ((ProductLaurent.monomialUnit R n (twistExponent n m σ)):Ambient R n)*chartScalar R n σ a)
    rw [←ha']
    ring
lemma localizedLine_injective (m : Fin n → ℤ) (σ : Chart n) (k : Fin (n+1)) :
    Function.Injective (localizedLine R n m σ k) := by
  intro x y h
  apply localizedChart_injective R n σ k
  apply ((Units.isUnit (ProductLaurent.monomialUnit R n (twistExponent n m σ))).map (embed R n)).mul_left_cancel
  exact h
 

theorem localizedLine_range (m : Fin n → ℤ) (σ : Chart n) (k : Fin (n+1)) :
    (localizedLine R n m σ k).range=grid R n m {k} {σ} := by
  apply le_antisymm
  · rintro _ ⟨z,rfl⟩;exact localizedLine_mem R n m σ k z
  · intro x hx
    obtain ⟨N,h,hh,he⟩ := hx
    simp only [Finset.card_singleton] at hh
    obtain ⟨a,rfl⟩ := (show h∈(chartLine R n (levelTwist n m 1 N) σ).range from
      (chartLine_range R n (levelTwist n m 1 N) σ).symm ▸ hh)
    let z : ProductLinearChart.chart R n σ k :=
      algebraMap (ProductLinearChart.Ring R n) _ a * (↑((ProductLinearChart.denominator R n σ k)⁻¹))^N
    have hz : z*(algebraMap (ProductLinearChart.Ring R n) (ProductLinearChart.chart R n σ k)
        ((ProductLinearChart.product R n σ).coeff k))^N=algebraMap (ProductLinearChart.Ring R n) _ a := by
      dsimp only [z]
      rw [←ProductLinearChart.denominator_val,mul_assoc,←mul_pow,Units.inv_mul,one_pow,mul_one]
    have hz' := congrArg (localizedChart R n σ k) hz
    simp only [map_mul,map_pow,localizedChart_algebraMap] at hz'
    refine ⟨z,?_⟩
    apply ((denominator_unit R n {k}).pow N).mul_left_cancel
    rw [he]
    simp only [denominator,AwayCover.denominator,Finset.prod_singleton]
    rw [targetCoeff_chart R n σ k,mul_pow,localizedLine_apply,chartLine_level,map_mul,map_pow]
    simp only [chartLine,LinearMap.comp_apply,LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply,map_mul,map_pow]
    change _=embed R n (ProductLaurent.chartUnit R n σ:Ambient R n)^N*
      (embed R n ((ProductLaurent.monomialUnit R n (twistExponent n m σ)):Ambient R n)*chartScalar R n σ a)
    rw [←hz']
    simp only [z,map_mul,map_pow]
    ring
 
def localizedLineEquiv (m : Fin n → ℤ) (σ : Chart n) (k : Fin (n+1)) :
    ProductLinearChart.chart R n σ k ≃ₗ[R] grid R n m {k} {σ} :=
  (LinearEquiv.ofInjective (localizedLine R n m σ k) (localizedLine_injective R n m σ k)).trans
    (LinearEquiv.ofEq _ _ (localizedLine_range R n m σ k))
end


open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def targetUnit (k : Fin (n+1)) : (GridAmbient R n)ˣ := (denominator_unit R n {k}).unit
lemma targetUnit_val (k : Fin (n+1)) :
    (targetUnit R n k:GridAmbient R n)=embed R n (targetCoeff R n k) := by
  simpa only [targetUnit,denominator,AwayCover.denominator,Finset.prod_singleton] using
    (denominator_unit R n {k}).unit_spec
 
def gridTarget (k : Fin (n+1)) : UniversalCoefficientChart.Ring R n k →ₐ[R] GridAmbient R n :=
  UniversalCoefficientChart.eval R n k (fun j => (↑((targetUnit R n k)⁻¹):GridAmbient R n)*embed R n (targetCoeff R n j))
lemma gridTarget_coefficient (k j : Fin (n+1)) :
    gridTarget R n k (UniversalCoefficientChart.coefficient R n k j)=
      (↑((targetUnit R n k)⁻¹):GridAmbient R n)*embed R n (targetCoeff R n j) := by
  apply UniversalCoefficientChart.eval_coefficient
  rw [←targetUnit_val,Units.inv_mul]
lemma targetUnit_chart (σ : Chart n) (k : Fin (n+1)) :
    targetUnit R n k=Units.map (embed R n).toMonoidHom (ProductLaurent.chartUnit R n σ)*
      Units.map (localizedChart R n σ k).toMonoidHom (ProductLinearChart.denominator R n σ k) := by
  apply Units.ext
  change (targetUnit R n k:GridAmbient R n)=embed R n (ProductLaurent.chartUnit R n σ:Ambient R n)*
    localizedChart R n σ k (ProductLinearChart.denominator R n σ k:ProductLinearChart.chart R n σ k)
  rw [targetUnit_val,ProductLinearChart.denominator_val,localizedChart_algebraMap]
  exact targetCoeff_chart R n σ k
lemma ratio_rescale {S : Type*} [CommRing S] (u v : Sˣ) (b : S) :
    (↑((u*v)⁻¹):S)*((u:S)*b)=(↑(v⁻¹):S)*b := by
  rw [mul_inv_rev,Units.val_mul]
  calc
    _ = (↑(v⁻¹):S)*((↑(u⁻¹):S)*(u:S))*b := by ring
    _ = _ := by rw [Units.inv_mul,mul_one]
 

theorem localizedChart_target (σ : Chart n) (k : Fin (n+1)) :
    (localizedChart R n σ k).comp (ProductLinearChart.target R n σ k)=gridTarget R n k := by
  apply UniversalCoefficientChart.ext
  intro j
  rw [gridTarget_coefficient,AlgHom.comp_apply]
  change localizedChart R n σ k (UniversalCoefficientChart.eval R n k
    (fun j => (ProductLinearChart.normalized R n σ k).coeff j)
    (UniversalCoefficientChart.coefficient R n k j))=_
  rw [UniversalCoefficientChart.eval_coefficient _ _ _ _ (ProductLinearChart.normalized_self R n σ k),
    ProductLinearChart.normalized,coeff_C_mul,coeff_map,map_mul,localizedChart_algebraMap,
    targetUnit_chart R n σ k,targetCoeff_chart R n σ j]
  exact (ratio_rescale (Units.map (embed R n).toMonoidHom (ProductLaurent.chartUnit R n σ))
    (Units.map (localizedChart R n σ k).toMonoidHom (ProductLinearChart.denominator R n σ k))
    (chartScalar R n σ ((ProductLinearChart.product R n σ).coeff j))).symm
instance gridTargetAlgebra (k : Fin (n+1)) : Algebra (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) :=
  (gridTarget R n k).toRingHom.toAlgebra
instance gridTargetTower (k : Fin (n+1)) : IsScalarTower R (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) :=
  IsScalarTower.of_algebraMap_eq' (gridTarget R n k).comp_algebraMap.symm
 
def localizedChartA (σ : Chart n) (k : Fin (n+1)) :
    ProductLinearChart.chart R n σ k →ₐ[UniversalCoefficientChart.Ring R n k] GridAmbient R n where
  toRingHom := (localizedChart R n σ k).toRingHom
  commutes' a := AlgHom.congr_fun (localizedChart_target R n σ k) a
end


universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma grid_mul_mem (m l : Fin n → ℤ) (s : Finset (Fin (n+1))) (t : Finset (Chart n))
    (x y : GridAmbient R n) (hx : x∈grid R n m s t) (hy : y∈grid R n l s t) :
    x*y∈grid R n (m+l) s t := by
  obtain ⟨N,h,hh,he⟩ := hx
  obtain ⟨M,g,hg,hge⟩ := hy
  refine ⟨N+M,h*g,?_,?_⟩
  · have ht : levelTwist n m s.card N+levelTwist n l s.card M=levelTwist n (m+l) s.card (N+M) := by
      ext i
      simp only [levelTwist,Pi.add_apply,Nat.cast_add]
      ring
    rw [←ht]
    exact mul_mem R n _ _ t h g hh hg
  · rw [map_mul,pow_add]
    calc
      _ = (embed R n (denominator R n s)^N*x)*(embed R n (denominator R n s)^M*y) := by ring
      _ = _ := by rw [he,hge]
lemma grid_one_mem (s : Finset (Fin (n+1))) (t : Finset (Chart n)) :
    (1:GridAmbient R n)∈grid R n 0 s t := by
  refine ⟨0,1,?_,by simp⟩
  rw [show levelTwist n 0 s.card 0=0 by ext i;simp [levelTwist]]
  exact one_mem R n t
lemma grid_zero_pow_mem (s : Finset (Fin (n+1))) (t : Finset (Chart n))
    (x : GridAmbient R n) (hx : x∈grid R n 0 s t) (N : ℕ) : x^N∈grid R n 0 s t := by
  induction N with
  | zero => simpa only [pow_zero] using grid_one_mem R n s t
  | succ N ih => simpa only [pow_succ,zero_add] using grid_mul_mem R n 0 0 s t _ _ ih hx
 
def targetProduct (k : Fin (n+1)) (s : Finset (Fin (n+1))) : UniversalCoefficientChart.Ring R n k :=
  ∏ j∈s,UniversalCoefficientChart.coefficient R n k j
lemma targetProduct_map (k : Fin (n+1)) (s : Finset (Fin (n+1))) :
    gridTarget R n k (targetProduct R n k s)=
      (↑((targetUnit R n k)⁻¹):GridAmbient R n)^s.card*embed R n (denominator R n s) := by
  simp only [targetProduct,map_prod,gridTarget_coefficient,Finset.prod_mul_distrib,Finset.prod_const]
  change _ = _ * embed R n (∏ j∈s,targetCoeff R n j)
  rw [map_prod]
lemma targetProduct_relation (k : Fin (n+1)) (s : Finset (Fin (n+1))) :
    (targetUnit R n k:GridAmbient R n)^s.card*gridTarget R n k (targetProduct R n k s)=embed R n (denominator R n s) := by
  rw [targetProduct_map,←mul_assoc,←mul_pow,Units.mul_inv,one_pow,one_mul]
def targetProductUnit (k : Fin (n+1)) (s : Finset (Fin (n+1))) : (GridAmbient R n)ˣ :=
  (targetUnit R n k)⁻¹^s.card*(denominator_unit R n s).unit
lemma targetProductUnit_val (k : Fin (n+1)) (s : Finset (Fin (n+1))) :
    (targetProductUnit R n k s:GridAmbient R n)=gridTarget R n k (targetProduct R n k s) := by
  rw [targetProduct_map]
  simp only [targetProductUnit,Units.val_mul,Units.val_pow_eq_pow_val,IsUnit.unit_spec]
lemma targetProductUnit_inv_mem (k : Fin (n+1)) (s : Finset (Fin (n+1))) :
    (↑((targetProductUnit R n k s)⁻¹):GridAmbient R n)∈grid R n 0 s ∅ := by
  refine ⟨1,(targetCoeff R n k)^s.card,?_,?_⟩
  · have hp := pow_mem R n (fun _ => 1) ∅ (targetCoeff R n k) (coefficient_mem R n k) s.card
    have ht : s.card • (fun _ : Fin n => (1:ℤ))=levelTwist n 0 s.card 1 := by
      ext i
      simp [levelTwist]
    rw [←ht]
    exact hp
  · rw [pow_one,map_pow,←targetUnit_val]
    change (↑((denominator_unit R n s).unit):GridAmbient R n)*
      (↑(((targetUnit R n k)⁻¹^s.card*(denominator_unit R n s).unit)⁻¹):GridAmbient R n)=_
    rw [mul_inv_rev,Units.val_mul,←mul_assoc,Units.mul_inv,one_mul,inv_pow,inv_inv,Units.val_pow_eq_pow_val]
end Lech.ProductSourceCover


namespace Lech.UniversalSplitting
open Polynomial
universe u

structure Data (R : Type u) [CommRing R] (n : ℕ) (f : R[X]) where
  S : Type u
  [ring : CommRing S]
  [algebra : Algebra R S]
  basis : Module.Basis (Fin n.factorial) R S
  roots : Fin n → S
  factorization : f.map (algebraMap R S) = ∏ i, (Polynomial.X - C (roots i))
  universal : ∀ (T : Type u) [CommRing T] [Algebra R T] (xs : Fin n → T),
    f.map (algebraMap R T) = ∏ i, (Polynomial.X - C (xs i)) →
    ∃! φ : S →ₐ[R] T, ∀ i, φ (roots i)=xs i
attribute [instance] Data.ring Data.algebra


theorem exists_data (n : ℕ) : ∀ (R : Type u) [CommRing R] [Nontrivial R]
    (f : R[X]), f.Monic → f.natDegree=n → Nonempty (Data R n f) := by
  induction n with
  | zero =>
    intro R _ _ f hf hn
    have hf1 : f=1 := hf.natDegree_eq_zero.mp hn
    exact ⟨{
      S := R
      basis := Module.Basis.singleton (Fin 1) R
      roots := Fin.elim0
      factorization := by simp [hf1]
      universal := by
        intro T _ _ xs _
        refine ⟨Algebra.ofId R T, fun i => Fin.elim0 i, ?_⟩
        intro φ _
        ext }⟩
  | succ n ih =>
    intro R _ _ f hf hn
    let B := AdjoinRoot f
    let b : Module.Basis (Fin (n+1)) R B :=
      (AdjoinRoot.powerBasisAux' hf).reindex (finCongr hn)
    let : Nontrivial B := b.repr.symm.injective.nontrivial
    let g : B[X] := f.map (algebraMap R B) /ₘ (Polynomial.X-C (AdjoinRoot.root f))
    have hfac : f.map (algebraMap R B) = (Polynomial.X-C (AdjoinRoot.root f))*g := by
      apply Eq.symm
      exact (mul_divByMonic_eq_iff_isRoot).mpr (AdjoinRoot.isRoot_root f)
    have hg : g.Monic := (monic_X_sub_C _).of_mul_monic_left (hfac ▸ hf.map _)
    have hdeg : g.natDegree=n := by
      rw [show g = _ from rfl, natDegree_divByMonic _ (monic_X_sub_C _),
        hf.natDegree_map, natDegree_X_sub_C, hn]
      omega
    obtain ⟨d⟩ := ih B g hg hdeg
    let : Algebra R d.S := ((algebraMap B d.S).comp (algebraMap R B)).toAlgebra
    let : IsScalarTower R B d.S := IsScalarTower.of_algebraMap_eq fun r => rfl
    let bb : Module.Basis (Fin (n+1) × Fin n.factorial) R d.S := b.smulTower d.basis
    let c : Module.Basis (Fin (n+1).factorial) R d.S :=
      bb.reindex (finProdFinEquiv.trans (finCongr (Nat.factorial_succ n).symm))
    let rs : Fin (n+1) → d.S := Fin.cons
      (algebraMap B d.S (AdjoinRoot.root f)) d.roots
    refine ⟨{
      S := d.S
      basis := c
      roots := rs
      factorization := ?_
      universal := ?_ }⟩
    · have hmap := congrArg (Polynomial.map (algebraMap B d.S)) hfac
      rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C, d.factorization] at hmap
      simpa [rs, Fin.prod_univ_succ, Polynomial.map_map,
        IsScalarTower.algebraMap_eq R B d.S] using hmap

    · intro T _ _ xs hxs
      have hx0 : f.eval₂ (algebraMap R T) (xs 0)=0 := by
        rw [← Polynomial.eval_map, hxs, Fin.prod_univ_succ]
        simp
      let β : B →ₐ[R] T := AdjoinRoot.liftAlgHom f (Algebra.ofId R T) (xs 0) hx0
      have hβ : β (AdjoinRoot.root f)=xs 0 := AdjoinRoot.liftAlgHom_root _ _ _ _
      let : Algebra B T := β.toRingHom.toAlgebra
      let : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq fun r => (β.commutes r).symm
      have hgxs : g.map (algebraMap B T)=∏ i : Fin n, (Polynomial.X-C (xs i.succ)) := by
        apply (monic_X_sub_C (xs 0)).isRegular.left
        have hmap := congrArg (Polynomial.map β.toRingHom) hfac
        rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
          Polynomial.map_C, show β.toRingHom (AdjoinRoot.root f)=xs 0 from hβ] at hmap
        have heq : (f.map (algebraMap R B)).map β.toRingHom =
            f.map (algebraMap R T) := by
          rw [Polynomial.map_map]
          congr 1
          exact β.comp_algebraMap
        rw [heq, hxs, Fin.prod_univ_succ] at hmap
        exact hmap.symm
      obtain ⟨φ, hφ, huniq⟩ := d.universal T (fun i => xs i.succ) hgxs
      refine ⟨φ.restrictScalars R, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change φ (algebraMap B d.S (AdjoinRoot.root f))=xs 0
          rw [φ.commutes]
          exact hβ
        · exact hφ j
      · intro ψ hψ
        have hc : ψ.toRingHom.comp (algebraMap B d.S)=β.toRingHom := by
          apply AdjoinRoot.ringHom_ext
          · ext r
            change ψ ((algebraMap B d.S) ((algebraMap R B) r))=β ((algebraMap R B) r)
            rw [← IsScalarTower.algebraMap_apply R B d.S, ψ.commutes, β.commutes]
          · change ψ (algebraMap B d.S (AdjoinRoot.root f))=β (AdjoinRoot.root f)
            rw [hβ]
            exact hψ 0
        let ψB : d.S →ₐ[B] T := {
          toRingHom := ψ.toRingHom
          commutes' := fun b => DFunLike.congr_fun hc b }
        have hψB : ψB=φ := huniq ψB (fun i => hψ i.succ)
        ext x
        exact DFunLike.congr_fun hψB x

 
theorem exists_data_all (R : Type u) [CommRing R] (n : ℕ) (f : R[X])
    (hf : f.Monic) (hn : f.natDegree=n) : Nonempty (Data R n f) := by
  cases subsingleton_or_nontrivial R with
  | inr h => exact exists_data n R f hf hn
  | inl h =>
    refine ⟨{
      S := R
      basis := Module.Basis.ofRepr (LinearEquiv.ofSubsingleton R (Fin n.factorial →₀ R))
      roots := fun _ => 0
      factorization := Subsingleton.elim _ _
      universal := ?_ }⟩
    intro T _ _ xs _
    have : Subsingleton T := Module.subsingleton R T
    refine ⟨Algebra.ofId R T, fun _ => Subsingleton.elim _ _, ?_⟩
    intro φ _
    exact Subsingleton.elim _ _

variable {R : Type u} [CommRing R] {n : ℕ} {f : R[X]}

lemma Data.hom_ext (d : Data R n f) {T : Type u} [CommRing T] [Algebra R T]
    (φ ψ : d.S →ₐ[R] T) (h : ∀ i, φ (d.roots i)=ψ (d.roots i)) : φ=ψ := by
  have hfac : f.map (algebraMap R T)=∏ i, (Polynomial.X-C (ψ (d.roots i))) := by
    have he := congrArg (Polynomial.map ψ.toRingHom) d.factorization
    simpa only [Polynomial.map_map, AlgHom.comp_algebraMap, Polynomial.map_prod,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using he
  obtain ⟨a, _, ha⟩ := d.universal T (fun i => ψ (d.roots i)) hfac
  exact (ha φ h).trans (ha ψ (fun _ => rfl)).symm


def Data.baseChange (d : Data R n f) (T : Type u) [CommRing T] [Algebra R T] :
    Data T n (f.map (algebraMap R T)) := by
  classical
  let ι : d.S →ₐ[R] TensorProduct R T d.S := Algebra.TensorProduct.includeRight
  refine {
    S := TensorProduct R T d.S
    basis := d.basis.baseChange T
    roots := fun i => ι (d.roots i)
    factorization := ?_
    universal := ?_ }
  · have he := congrArg (Polynomial.map ι.toRingHom) d.factorization
    simpa only [Polynomial.map_map, AlgHom.comp_algebraMap, Polynomial.map_prod,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      ← IsScalarTower.algebraMap_eq R T (TensorProduct R T d.S)] using he
  · intro U _ _ xs hxs
    let : Algebra R U := ((algebraMap T U).comp (algebraMap R T)).toAlgebra
    let : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq fun r => rfl
    have hx : f.map (algebraMap R U)=∏ i, (Polynomial.X-C (xs i)) := by
      simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq R T U] using hxs
    obtain ⟨φ, hφ, huniq⟩ := d.universal U xs hx
    let ψ : TensorProduct R T d.S →ₐ[T] U :=
      Algebra.TensorProduct.lift (Algebra.ofId T U) φ (fun _ _ => Commute.all _ _)
    have hψ : ∀ i, ψ (ι (d.roots i))=xs i := by
      intro i
      simpa only [ψ, ι, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul] using hφ i
    refine ⟨ψ, hψ, ?_⟩
    intro ζ hζ
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply d.hom_ext
      intro i
      exact (hζ i).trans (hψ i).symm

lemma Data.finite (d : Data R n f) : Module.Finite R d.S :=
  Module.Finite.of_basis d.basis

lemma Data.free (d : Data R n f) : Module.Free R d.S :=
  Module.Free.of_basis d.basis

lemma Data.flat (d : Data R n f) : Module.Flat R d.S := by
  have := d.free
  exact Module.Flat.of_free

end Lech.UniversalSplitting

end

end OAI
