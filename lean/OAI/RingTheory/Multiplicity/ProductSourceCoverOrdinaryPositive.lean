import Mathlib
import OAI.RingTheory.Multiplicity.ProductSourceCoverAllowedEmpty

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
namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
local instance chartOrder (n : ℕ) : LinearOrder (Chart n) :=
  LinearOrder.lift' (Fintype.equivFin (Chart n)) (Fintype.equivFin _).injective
 

theorem ordinary_positive_pure (m : Fin n → ℤ) (d r : ℕ) (hd : 0<d)
    (hm : PureCohomology R (ordinaryComplex R n m) d r) (a : ℕ) :
    PureCohomology R (ordinaryComplex R (n+1) (Fin.cons (a:ℤ) m)) d ((a+1)*r) := by
  induction a with
  | zero =>
    have hz := pureCohomology_acyclic (ordinaryComplex R (n+1) (Fin.cons (-1) m))
      (ordinary_endpoint_acyclic R (n+1) (Fin.cons (-1) m) 0 rfl) d
    have h := pureCohomology_middle (ordinaryDivisorSequence R n 0 m)
      (ordinaryDivisorSequence_shortExact R n 0 m) hd hz hm
    simpa using h
  | succ a ih =>
    have hi : PureCohomology R (ordinaryComplex R (n+1) (Fin.cons ((a+1:ℕ):ℤ) m)) d (((a+1)*r)+r) := by
      apply pureCohomology_middle (ordinaryDivisorSequence R n ((a+1:ℕ):ℤ) m)
        (ordinaryDivisorSequence_shortExact R n ((a+1:ℕ):ℤ) m) hd _ hm
      simpa only [ordinaryDivisorSequence_X1,Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using ih
    convert hi using 1; ring
 

theorem ordinary_negative_pure (m : Fin n → ℤ) (d r : ℕ)
    (hm : PureCohomology R (ordinaryComplex R n m) d r) (a : ℕ) :
    PureCohomology R (ordinaryComplex R (n+1) (Fin.cons (-(a:ℤ)-2) m)) (d+1) ((a+1)*r) := by
  induction a with
  | zero =>
    have hz := pureCohomology_acyclic (ordinaryComplex R (n+1) (Fin.cons (-1) m))
      (ordinary_endpoint_acyclic R (n+1) (Fin.cons (-1) m) 0 rfl) (d+1)
    have h := pureCohomology_left (ordinaryDivisorSequence R n (-1) m)
      (ordinaryDivisorSequence_shortExact R n (-1) m)
      (ordinary_homology_zero R (n+1) (Fin.cons (-1-1) m)) hz hm
    simpa using h
  | succ a ih =>
    have hi := pureCohomology_left (ordinaryDivisorSequence R n (-(a:ℤ)-2) m)
      (ordinaryDivisorSequence_shortExact R n (-(a:ℤ)-2) m)
      (ordinary_homology_zero R (n+1) (Fin.cons (-(a:ℤ)-2-1) m)) ih hm
    rw [ordinaryDivisorSequence_X1] at hi
    convert hi using 1
    · congr 2
      push_cast
      ring
    · ring
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open scoped BigOperators
 
def negativeCount {n : ℕ} (m : Fin n → ℤ) : ℕ := ∑ i,if m i < -1 then 1 else 0
 
def signedRank {n : ℕ} (m : Fin n → ℤ) : ℕ := ∏ i,(m i+1).natAbs
lemma negativeCount_cons {n : ℕ} (k : ℤ) (m : Fin n → ℤ) :
    negativeCount (Fin.cons k m)=(if k < -1 then 1 else 0)+negativeCount m := by
  simp only [negativeCount,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
lemma signedRank_cons {n : ℕ} (k : ℤ) (m : Fin n → ℤ) :
    signedRank (Fin.cons k m)=(k+1).natAbs*signedRank m := by
  simp [signedRank,Fin.prod_univ_succ]
lemma negativeCount_le {n : ℕ} (m : Fin n → ℤ) : negativeCount m ≤ n := by
  calc negativeCount m ≤ ∑ _i : Fin n,1 := Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
       _ = n := by simp
lemma single_signed_rank (k : ℤ) :
    (-1:ℤ)^(if k < -1 then 1 else 0)*(k+1).natAbs=k+1 := by
  by_cases hk : k < -1
  · rw [ite_eq_left hk,pow_one,Int.natCast_natAbs,abs_of_neg (by omega)]
    ring
  · rw [ite_eq_right hk,pow_zero,one_mul,Int.natCast_natAbs,abs_of_nonneg (by omega)]
 

lemma signedRank_euler (n : ℕ) (m : Fin n → ℤ) :
    (-1:ℤ)^negativeCount m*(signedRank m:ℤ)=∏ i,(m i+1) := by
  induction n with
  | zero => simp [negativeCount,signedRank]
  | succ n ih =>
    rw [←Fin.cons_self_tail m,negativeCount_cons,signedRank_cons,Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Nat.cast_mul,pow_add]
    calc _ = ((-1:ℤ)^(if m 0 < -1 then 1 else 0)*(m 0+1).natAbs)*
        ((-1:ℤ)^negativeCount (Fin.tail m)*(signedRank (Fin.tail m):ℤ)) := by ring
         _ = _ := by rw [single_signed_rank,ih]
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R]
local instance zeroDimChartOrder (n : ℕ) : LinearOrder (Chart n) :=
  LinearOrder.lift' (Fintype.equivFin (Chart n)) (Fintype.equivFin _).injective
lemma ordinary_zero_dim_pure (m : Fin 0 → ℤ) :
    PureCohomology R (ordinaryComplex R 0 m) 1 1 := by
  have hm : ∀ i,-1 ≤ m i := fun i => Fin.elim0 i
  refine ⟨?_,?_⟩
  · intro p hp
    cases p with
    | zero => exact ordinary_homology_zero R 0 m
    | succ p =>
      cases p with
      | zero => exact (hp rfl).elim
      | succ p => exact (highTwistHigher R 0 m hm p).of_iso (ordinaryCohomologyIso R 0 m (p+2))
  · let b := (highTwistH0Basis R 0 m hm).map (ordinaryCohomologyIso R 0 m 1).toLinearEquiv.symm
    exact ⟨b.reindex (Fintype.equivFinOfCardEq (by rw [globalIndex_card];simp))⟩
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R]
local instance signedChartOrder (n : ℕ) : LinearOrder (Chart n) :=
  LinearOrder.lift' (Fintype.equivFin (Chart n)) (Fintype.equivFin _).injective
 

theorem ordinary_signed_pure (n : ℕ) (m : Fin n → ℤ) :
    PureCohomology R (ordinaryComplex R n m) (negativeCount m+1) (signedRank m) := by
  induction n with
  | zero => simpa [negativeCount,signedRank] using ordinary_zero_dim_pure R m
  | succ n ih =>
    have hh := ih (Fin.tail m)
    rw [←Fin.cons_self_tail m]
    by_cases hz : m 0=-1
    · have he := ordinary_endpoint_acyclic R (n+1) (Fin.cons (m 0) (Fin.tail m)) 0 hz
      have hp := pureCohomology_acyclic _ he (negativeCount (Fin.cons (m 0) (Fin.tail m))+1)
      simpa [signedRank_cons,hz] using hp
    · by_cases hk : 0 ≤ m 0
      · obtain ⟨a,ha⟩ := Int.eq_ofNat_of_zero_le hk
        have hp := ordinary_positive_pure R n (Fin.tail m) (negativeCount (Fin.tail m)+1)
          (signedRank (Fin.tail m)) (by omega) hh a
        rw [ha]
        have hlt : ¬ (a:ℤ) < -1 := by omega
        have habs : ((a:ℤ)+1).natAbs=a+1 := by
          rw [show (a:ℤ)+1=((a+1:ℕ):ℤ) by omega,Int.natAbs_natCast]
        simpa only [negativeCount_cons,ite_eq_right hlt,zero_add,signedRank_cons,habs] using hp
      · have hk' : m 0≤-2 := by omega
        obtain ⟨a,ha⟩ := Int.eq_ofNat_of_zero_le (show 0≤-m 0-2 by omega)
        have hhead : m 0= -(a:ℤ)-2 := by omega
        have hp := ordinary_negative_pure R n (Fin.tail m) (negativeCount (Fin.tail m)+1)
          (signedRank (Fin.tail m)) hh a
        rw [hhead]
        convert hp using 1
        · rw [negativeCount_cons]
          have : -(a:ℤ)-2 < -1 := by omega
          simp [this,Nat.add_comm]
        · rw [signedRank_cons]
          congr 1
          have he : -(a:ℤ)-2+1= -((a+1:ℕ):ℤ) := by push_cast;ring
          rw [he,Int.natAbs_neg,Int.natAbs_natCast]
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AddMonoidAlgebra Polynomial
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma prod_mem {ι : Type*} (s : Finset ι) (x : ι → Ambient R n) (m : ι → Fin n → ℤ)
    (t : Finset (Chart n)) (h : ∀ i∈s,x i∈ringSections R n (m i) t) :
    (∏ i∈s,x i)∈ringSections R n (∑ i∈s,m i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,Finset.sum_empty] using one_mem R n t
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    exact mul_mem R n (m a) (∑ i∈s,m i) t (x a) (∏ i∈s,x i)
      (h a (Finset.mem_insert_self _ _)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
def subsetExponent (s : Finset (Fin n)) : Exponent n := ∑ i∈s,Finsupp.single i 1
lemma subsetExponent_apply (s : Finset (Fin n)) (j : Fin n) :
    subsetExponent n s j=if j∈s then 1 else 0 := by
  classical
  simp [subsetExponent,Finsupp.finsetSum_apply,Finsupp.single_apply]
lemma prod_variables (s : Finset (Fin n)) :
    (∏ i∈s,(ProductLaurent.variableUnit R n i:Ambient R n))=single (subsetExponent n s) (1:R) := by
  induction s using Finset.induction_on with
  | empty => simp [subsetExponent,←one_def]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,subsetExponent,Finset.sum_insert ha,ih]
    change single (Finsupp.single a 1) 1 * single (subsetExponent n s) (1:R)=_
    rw [single_mul_single,one_mul]
    rfl
lemma subsetExponent_allowed (s : Finset (Fin n)) :
    allowed n (fun _ => 1) ∅ (subsetExponent n s) := by
  intro i
  rw [subsetExponent_apply]
  split_ifs <;> simp
lemma polynomial_subproduct (s : Finset (Fin n)) :
    (∏ i∈s,(C (ProductLaurent.variableUnit R n i:Ambient R n)*Polynomial.X))=
      C (∏ i∈s,(ProductLaurent.variableUnit R n i:Ambient R n))*Polynomial.X^s.card := by
  rw [Finset.prod_mul_distrib,←map_prod]
  simp only [Finset.prod_const]
lemma subproduct_coeff_mem (s : Finset (Fin n)) (k : ℕ) :
    (∏ i∈s,(C (ProductLaurent.variableUnit R n i:Ambient R n)*Polynomial.X)).coeff k∈
      ringSections R n (fun _ => 1) ∅ := by
  rw [polynomial_subproduct,coeff_C_mul,coeff_X_pow,prod_variables]
  split_ifs
  · rw [mul_one];exact single_mem R n _ _ _ _ (subsetExponent_allowed n s)
  · rw [mul_zero];exact (ringSections R n _ _).zero_mem
 

lemma coefficient_mem (k : ℕ) : (ProductLaurent.binaryForm R n).coeff k∈
    ringSections R n (fun _ => 1) ∅ := by
  rw [ProductLaurent.binaryForm,Finset.prod_add_one,finsetSum_coeff]
  apply (ringSections R n _ _).sum_mem
  intro s _
  exact subproduct_coeff_mem R n s k
 

lemma coefficient_product_mem (s : Finset (Fin (n+1))) :
    (∏ k∈s,(ProductLaurent.binaryForm R n).coeff k)∈ringSections R n (fun _ => (s.card:ℤ)) ∅ := by
  have h := prod_mem R n s (fun k : Fin (n+1) => (ProductLaurent.binaryForm R n).coeff k)
    (fun _ _ => (1:ℤ)) ∅ (fun k _ => coefficient_mem R n k)
  have he : (∑ _∈s,fun _ : Fin n => (1:ℤ))=(fun _ : Fin n => (s.card:ℤ)) := by
    ext i
    simp
  rwa [he] at h
end Lech.ProductSourceCover


namespace Lech.AwayCover
universe u w
variable {R : Type u} [CommRing R]
 
def restrict {f g : R} (h : f ∣ g) : Localization.Away f →ₐ[R] Localization.Away g :=
  IsLocalization.Away.liftAlgHom f (f := Algebra.algHom R R (Localization.Away g))
    (IsLocalization.Away.isUnit_of_dvd g h)
@[simp] lemma restrict_algebraMap {f g : R} (h : f∣g) (a : R) :
    restrict h (algebraMap R (Localization.Away f) a)=algebraMap R (Localization.Away g) a :=
  IsLocalization.Away.lift_eq f (IsLocalization.Away.isUnit_of_dvd g h) a
lemma restrict_comp {f g t : R} (hfg : f∣g) (hgt : g∣t) :
    (restrict hgt).comp (restrict hfg)=restrict (hfg.trans hgt) := by
  apply IsLocalization.algHom_ext (Submonoid.powers f)
  exact Subsingleton.elim _ _
lemma restrict_self (f : R) : restrict (dvd_refl f)=AlgHom.id R _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers f)
  exact Subsingleton.elim _ _
 
lemma clear {f g t : R} (hf : f∣t) (hfg : f*g∣t) (x : Localization.Away (f*g)) :
    ∃ (n : ℕ) (y : Localization.Away f),
      restrict hf y=g^n • restrict hfg x := by
  obtain ⟨n,a,ha⟩ := IsLocalization.Away.surj (f*g) x
  let y := IsLocalization.mk' (Localization.Away f) a (⟨f^n,n,rfl⟩ : Submonoid.powers f)
  have hy : y*algebraMap R (Localization.Away f) f^n=algebraMap R (Localization.Away f) a := by
    simpa only [map_pow] using IsLocalization.mk'_spec (Localization.Away f) a (⟨f^n,n,rfl⟩ : Submonoid.powers f)
  refine ⟨n,y,?_⟩
  apply ((IsLocalization.Away.isUnit_of_dvd t hf).pow n).mul_left_inj.mp
  have hy' := congrArg (restrict hf) hy
  have ha' := congrArg (restrict hfg) ha
  simp only [map_mul,map_pow,restrict_algebraMap] at hy' ha'
  rw [Algebra.smul_def,map_pow,mul_assoc]
  rw [hy']
  rw [mul_pow] at ha'
  rw [←ha']
  ring
variable {ι : Type w} [Fintype ι] [DecidableEq ι] (q : ι → R)
def denominator (s : Finset ι) : R := ∏ i∈s,q i
omit [Fintype ι] in
lemma denominator_dvd {s v : Finset ι} (h : s ⊆ v) : denominator q s ∣ denominator q v := by
  refine ⟨denominator q (v\s),?_⟩
  simpa only [denominator,mul_comm] using (Finset.prod_sdiff (f := q) h).symm
abbrev Total := Localization.Away (denominator q Finset.univ)
abbrev chart (s : Finset ι) := Localization.Away (denominator q s)
def inclusion (s : Finset ι) : chart q s →ₐ[R] Total q :=
  restrict (denominator_dvd q (Finset.subset_univ s))
def image (s : Finset ι) : Submodule R (Total q) := (inclusion q s).toLinearMap.range
lemma image_mono : Monotone (image q) := by
  intro s v h x hx
  obtain ⟨y,rfl⟩ := hx
  refine ⟨restrict (denominator_dvd q h) y,?_⟩
  exact AlgHom.congr_fun (restrict_comp (denominator_dvd q h) (denominator_dvd q (Finset.subset_univ v))) y
lemma image_clear (s : Finset ι) (j : ι) (x : Total q) (hx : x∈image q (insert j s)) :
    ∃ n : ℕ,q j^n • x∈image q s := by
  by_cases hj : j∈s
  · rw [Finset.insert_eq_of_mem hj] at hx
    exact ⟨0,by simpa only [pow_zero,one_smul] using hx⟩
  have hd : denominator q (insert j s)=denominator q s*q j := by
    simp only [denominator,Finset.prod_insert hj,mul_comm]
  obtain ⟨y,rfl⟩ := hx
  change ∃ n : ℕ,q j^n • inclusion q (insert j s) y∈image q s
  have he (p : R) (hp : p∣denominator q Finset.univ)
      (hd : p=denominator q s*q j) (z : Localization.Away p) :
      ∃ n : ℕ,q j^n • restrict hp z∈image q s := by
    subst p
    obtain ⟨n,w,hw⟩ := clear (denominator_dvd q (Finset.subset_univ s)) hp z
    exact ⟨n,⟨w,hw⟩⟩
  exact he _ (denominator_dvd q (Finset.subset_univ _)) hd y
end Lech.AwayCover


namespace Lech.AwayCover
universe u w
variable {R : Type u} [CommRing R] {ι : Type w} [Fintype ι] [DecidableEq ι]
  (q : ι → R) (hq : Ideal.span (Set.range q)=⊤)
include hq in
 

theorem image_exact (n : ℕ) (f : FiniteCoverCech.cochains R (Total q) (image q) (n+1))
    (hf : FiniteCoverCech.delta R (Total q) (n+1) f.val=0) :
    ∃ g : FiniteCoverCech.cochains R (Total q) (image q) n,
      FiniteCoverCech.delta R (Total q) n g.val=f.val :=
  FiniteCoverCech.exact R (Total q) (image q) q hq (image_clear q) n f hf
 

lemma inclusion_injective (hreg : IsRegular (denominator q Finset.univ)) (s : Finset ι) :
    Function.Injective (inclusion q s) := by
  have hi : Function.Injective (algebraMap R (Total q)) := by
    apply IsLocalization.injectiveₛ (M := Submonoid.powers (denominator q Finset.univ))
    rintro _ ⟨n,rfl⟩
    exact hreg.pow n
  apply IsLocalization.injective_of_map_algebraMap_zero (M := Submonoid.powers (denominator q s))
    (chart q s) (inclusion q s).toRingHom
  intro x hx
  have hh : algebraMap R (Total q) x=0 := by
    simpa only [inclusion,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,restrict_algebraMap] using hx
  have hz : x=0 := hi (hh.trans (map_zero _).symm)
  simp only [hz,map_zero]

def chartEquivImage (hreg : IsRegular (denominator q Finset.univ)) (s : Finset ι) :
    chart q s ≃ₗ[R] image q s :=
  LinearEquiv.ofInjective (inclusion q s).toLinearMap (inclusion_injective q hreg s)
lemma chartEquivImage_val (hreg : IsRegular (denominator q Finset.univ)) (s : Finset ι) (x : chart q s) :
    (chartEquivImage q hreg s x:Total q)=inclusion q s x := rfl
lemma chartEquivImage_restrict (hreg : IsRegular (denominator q Finset.univ))
    {s v : Finset ι} (h : s ⊆ v) (x : chart q s) :
    (chartEquivImage q hreg v (restrict (denominator_dvd q h) x):Total q)=
      (chartEquivImage q hreg s x:Total q) :=
  AlgHom.congr_fun (restrict_comp (denominator_dvd q h) (denominator_dvd q (Finset.subset_univ v))) x
end Lech.AwayCover


namespace Lech.ProductSourceCover
open AddMonoidAlgebra
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
abbrev targetCoeff : Fin (n+1) → Ambient R n := fun k => (ProductLaurent.binaryForm R n).coeff k
abbrev denominator (s : Finset (Fin (n+1))) : Ambient R n := AwayCover.denominator (targetCoeff R n) s
abbrev GridAmbient := AwayCover.Total (targetCoeff R n)
def embed : Ambient R n →ₐ[R] GridAmbient R n := IsScalarTower.toAlgHom R (Ambient R n) (GridAmbient R n)
lemma denom_regular (s : Finset (Fin (n+1))) : IsRegular (denominator R n s) :=
  IsRegular.prod (fun i _ => ProductLaurent.binaryForm_coefficient_regular R n i)
lemma embed_injective : Function.Injective (embed R n) := by
  apply IsLocalization.injectiveₛ (M:=Submonoid.powers (denominator R n Finset.univ))
  rintro _ ⟨N,rfl⟩
  exact (denom_regular R n Finset.univ).pow N
lemma denominator_unit (s : Finset (Fin (n+1))) : IsUnit (embed R n (denominator R n s)) :=
  IsLocalization.Away.isUnit_of_dvd (denominator R n Finset.univ)
    (AwayCover.denominator_dvd (targetCoeff R n) (Finset.subset_univ s))
def levelTwist (m : Fin n → ℤ) (d N : ℕ) : Fin n → ℤ := fun i => m i+(N:ℤ)*(d:ℤ)
lemma multiply_level (m : Fin n → ℤ) (d N K : ℕ) (t : Finset (Chart n))
    (q x : Ambient R n) (hq : q∈ringSections R n (fun _ => (d:ℤ)) ∅)
    (hx : x∈ringSections R n (levelTwist n m d N) t) :
    q^K*x∈ringSections R n (levelTwist n m d (N+K)) t := by
  have hpow := pow_mem R n (fun _ => (d:ℤ)) t q
    ((ringSections_mono R n _ (Finset.empty_subset t)) hq) K
  have h := mul_mem R n (K • fun _ => (d:ℤ)) (levelTwist n m d N) t _ x hpow hx
  have he : (K • fun _ : Fin n => (d:ℤ))+levelTwist n m d N=levelTwist n m d (N+K) := by
    ext i
    change (K • (d:ℤ))+(m i+(N:ℤ)*(d:ℤ))=m i+((N+K:ℕ):ℤ)*(d:ℤ)
    rw [nsmul_eq_mul,Nat.cast_add]
    ring
  rwa [he] at h
 

def RationalMember (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (t : Finset (Chart n))
    (x : GridAmbient R n) : Prop :=
  ∃ N : ℕ,∃ h : Ambient R n,h∈ringSections R n (levelTwist n m s.card N) t ∧
    embed R n (denominator R n s)^N*x=embed R n h
lemma raise_witness (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (t : Finset (Chart n))
    (x : GridAmbient R n) (N M : ℕ) (hNM : N≤M) (h : Ambient R n)
    (hh : h∈ringSections R n (levelTwist n m s.card N) t)
    (he : embed R n (denominator R n s)^N*x=embed R n h) :
    ∃ g : Ambient R n,g∈ringSections R n (levelTwist n m s.card M) t ∧
      embed R n (denominator R n s)^M*x=embed R n g := by
  obtain ⟨K,rfl⟩ := Nat.exists_eq_add_of_le hNM
  refine ⟨denominator R n s^K*h,multiply_level R n m s.card N K t _ h (coefficient_product_mem R n s) hh,?_⟩
  rw [map_mul,map_pow,pow_add,mul_right_comm,he]
  exact mul_comm _ _
def grid (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (t : Finset (Chart n)) :
    Submodule R (GridAmbient R n) where
  carrier := RationalMember R n m s t
  zero_mem' := ⟨0,0,(ringSections R n _ _).zero_mem,by simp⟩
  add_mem' := by
    rintro x y ⟨N,h,hh,he⟩ ⟨M,k,hk,hke⟩
    obtain ⟨h',hh',he'⟩ := raise_witness R n m s t x N (N+M) (by omega) h hh he
    obtain ⟨k',hk',hke'⟩ := raise_witness R n m s t y M (N+M) (by omega) k hk hke
    exact ⟨N+M,h'+k',(ringSections R n _ _).add_mem hh' hk',by rw [mul_add,he',hke',map_add]⟩
  smul_mem' := by
    rintro r x ⟨N,h,hh,he⟩
    refine ⟨N,r • h,(ringSections R n _ _).smul_mem r hh,?_⟩
    rw [map_smul,mul_smul_comm,he]
lemma grid_mem (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (t : Finset (Chart n))
    (x : GridAmbient R n) : x∈grid R n m s t ↔ RationalMember R n m s t x := Iff.rfl
lemma grid_source_mono (m : Fin n → ℤ) (s : Finset (Fin (n+1))) : Monotone (grid R n m s) := by
  intro t v htv x hx
  obtain ⟨N,h,hh,he⟩ := hx
  exact ⟨N,h,ringSections_mono R n _ htv hh,he⟩
lemma grid_target_mono (m : Fin n → ℤ) (t : Finset (Chart n)) : Monotone (fun s => grid R n m s t) := by
  intro s v hsv x hx
  obtain ⟨N,h,hh,he⟩ := hx
  let r := denominator R n (v\s)
  have hv : denominator R n v=r*denominator R n s := (Finset.prod_sdiff hsv).symm
  refine ⟨N,r^N*h,?_,?_⟩
  · have hr : r∈ringSections R n (fun _ => ((v\s).card:ℤ)) t :=
      ringSections_mono R n _ (Finset.empty_subset t) (coefficient_product_mem R n (v\s))
    have hp := mul_mem R n (N • fun _ => ((v\s).card:ℤ)) (levelTwist n m s.card N) t
      (r^N) h (pow_mem R n _ t r hr N) hh
    have hc : (v\s).card+s.card=v.card := Finset.card_sdiff_add_card_eq_card hsv
    have hc' : ((v\s).card:ℤ)+(s.card:ℤ)=(v.card:ℤ) := by exact_mod_cast hc
    have ht : (N • fun _ : Fin n => ((v\s).card:ℤ))+levelTwist n m s.card N=levelTwist n m v.card N := by
      ext i
      change (N • ((v\s).card:ℤ))+(m i+(N:ℤ)*(s.card:ℤ))=m i+(N:ℤ)*(v.card:ℤ)
      rw [nsmul_eq_mul,←hc']
      ring
    rwa [ht] at hp
  · rw [hv,map_mul,mul_pow,map_mul,map_pow,mul_assoc,he]
end Lech.ProductSourceCover
end
end

end OAI
