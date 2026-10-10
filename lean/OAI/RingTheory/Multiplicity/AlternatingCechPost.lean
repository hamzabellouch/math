import Mathlib
import OAI.RingTheory.Multiplicity.AlternatingCechAlt

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
namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def post (n : ℕ) (P : M →ₗ[R] M) : Alt R M (ι:=ι) n →ₗ[R] Alt R M (ι:=ι) n where
  toFun f := P.compAlternatingMap f
  map_add' _ _ := by ext v;exact P.map_add _ _
  map_smul' r f := by ext v;exact P.map_smul r (f v)
omit [DecidableEq ι] in
lemma evaluation_post (n : ℕ) (P : M →ₗ[R] M) (f : Alt R M (ι:=ι) n) (a : Fin n → ι) :
    evaluation R M n (post R M n P f) a=P (evaluation R M n f a) := rfl
lemma delta_post (n : ℕ) (P : M →ₗ[R] M) (f : Alt R M (ι:=ι) n) :
    delta R M n (post R M n P f)=post R M (n+1) P (delta R M n f) := by
  apply evaluation_injective R M (n+1)
  ext a
  rw [evaluation_delta,evaluation_post,evaluation_delta]
  change (∑ i : Fin (n+1),(-1:R)^i.val • evaluation R M n (post R M n P f) (a ∘ i.succAbove)) =
    P (∑ i : Fin (n+1),(-1:R)^i.val • evaluation R M n f (a ∘ i.succAbove))
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [evaluation_post]
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
variable (P : ι → M →ₗ[R] M) (hP : ∀ x,∑ j,P j x=x)
  (hmem : ∀ s j x,x∈F (insert j s) → P j x∈F s)
include hP hmem in
 

lemma projection_exact (n : ℕ) (f : cochains R M F (n+1)) (hf : delta R M (n+1) f.val=0) :
    ∃ g : cochains R M F n,delta R M n g.val=f.val := by
  let g : Alt R M (ι:=ι) n := ∑ j,post R M n (P j) (extra R M j n f.val)
  have hg : g∈cochains R M F n := by
    intro a
    change evaluation R M n g a∈F (FiniteCoverCech.intersection a)
    simp only [g,map_sum,Finset.sum_apply,evaluation_post,evaluation_extra]
    apply (F _).sum_mem
    intro j _
    apply hmem _ j _
    have hj := f.property (Fin.cons j a)
    change evaluation R M (n+1) f.val (Fin.cons j a) ∈ F _
    simpa only [FiniteCoverCech.intersection_cons] using hj
  refine ⟨⟨g,hg⟩,?_⟩
  have hj (j : ι) : delta R M n (extra R M j n f.val)=f.val := by
    have h := extra_delta R M j n f.val
    rw [hf,map_zero,zero_add] at h
    exact h
  simp only [g,map_sum,delta_post,hj]
  apply evaluation_injective R M (n+1)
  ext a
  simp only [map_sum,Finset.sum_apply,evaluation_post]
  exact hP _
include hP hmem in
lemma projection_complex_exactAt (n : ℕ) : (complex R M F hF).ExactAt (n+1) := by
  apply ((complex R M F hF).exactAt_iff' (i:=n) (j:=n+1) (k:=n+2) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change ((complex R M F hF).d (n+1) (n+2)).hom f=0 at hf
  rw [complex_d] at hf
  obtain ⟨g,hg⟩ := projection_exact R M F P hP hmem n f (congrArg Subtype.val hf)
  refine ⟨g,?_⟩
  change ((complex R M F hF).d n (n+1)).hom g=f
  rw [complex_d]
  exact Subtype.ext hg
lemma complex_exactAt_zero_of_nonempty [Nonempty ι] : (complex R M F hF).ExactAt 0 := by
  apply ((complex R M F hF).exactAt_iff' (i:=0) (j:=0) (k:=1) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change ((complex R M F hF).d 0 1).hom f=0 at hf
  rw [complex_d] at hf
  have hδ : delta R M 0 f.val=0 := congrArg Subtype.val hf
  have h := extra_delta_zero R M (Classical.choice (inferInstance : Nonempty ι)) f.val
  rw [hδ,map_zero] at h
  have hf0 : f=0 := Subtype.ext h.symm
  exact ⟨0,by simp [hf0]⟩
include hP hmem in
lemma projection_complex_acyclic [Nonempty ι] : (complex R M F hF).Acyclic := by
  intro n
  cases n with
  | zero => exact complex_exactAt_zero_of_nonempty R M F hF
  | succ n => exact projection_complex_exactAt R M F hF P hP hmem n
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
lemma post_prism_mem (τ : ι → ι) (hτ : ∀ i,τ (τ i)=τ i) (P : M →ₗ[R] M)
    (F : Finset ι → Submodule R M) (hF : Monotone F)
    (hcarrier : ∀ s x,x∈F (s∪s.image τ) → P x∈F s) (p : ℕ)
    (f : Alt R M (ι:=ι) (p+1)) (hf : f∈cochains R M F (p+1)) :
    post R M p P (prism R M τ p f)∈cochains R M F p := by
  apply (mem_cochains_iff_sorted R M F p _).mpr
  intro s
  rw [sortedCoordinates_eq_evaluation,evaluation_post]
  change evaluation R M p (prism R M τ p f) (s.val.orderEmbOfFin s.property)∈(F s.val).comap P
  have hstable : ∀ i∈s.val∪s.val.image τ,τ i∈s.val∪s.val.image τ := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      rw [hτ]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
  apply prism_local R M τ (s.val∪s.val.image τ) hstable ((F s.val).comap P) p f
  · intro a ha
    apply hcarrier s.val
    apply hF ?_ (hf a)
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact ha j
  · intro i
    exact Finset.mem_union_left _ (s.val.orderEmbOfFin_mem s.property i)
omit [LinearOrder ι] in
lemma post_pullback_zero (τ : ι → ι) (P : M →ₗ[R] M)
    (F : Finset ι → Submodule R M)
    (hzero : ∀ (s : Finset ι) x,x∈F (s.image τ) → P x=0) (p : ℕ)
    (f : Alt R M (ι:=ι) p) (hf : f∈cochains R M F p) :
    post R M p P (pullback R M τ p f)=0 := by
  apply evaluation_injective R M p
  ext a
  rw [evaluation_post,pullback_eval,map_zero,Pi.zero_apply]
  apply hzero (FiniteCoverCech.intersection a)
  have h := hf (τ ∘ a)
  have he : FiniteCoverCech.intersection (τ ∘ a)=(FiniteCoverCech.intersection a).image τ := by
    simp only [FiniteCoverCech.intersection,Finset.image_image,Function.comp_def]
  simpa only [he] using h
variable {κ : Type} [Fintype κ]
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
variable (P : κ → M →ₗ[R] M) (hP : ∀ x,∑ j,P j x=x)
  (τ : κ → ι → ι) (hτ : ∀ j i,τ j (τ j i)=τ j i)
  (hcarrier : ∀ s j x,x∈F (s∪s.image (τ j)) → P j x∈F s)
  (hzero : ∀ (s : Finset ι) j x,x∈F (s.image (τ j)) → P j x=0)
include hF hP hτ hcarrier hzero in
 

lemma projection_prism_exact (p : ℕ) (f : cochains R M F (p+1)) (hf : delta R M (p+1) f.val=0) :
    ∃ g : cochains R M F p,delta R M p g.val=f.val := by
  let g : Alt R M (ι:=ι) p := ∑ j,post R M p (P j) (prism R M (τ j) p f.val)
  have hg : g∈cochains R M F p :=
    (cochains R M F p).sum_mem (fun j _ => post_prism_mem R M (τ j) (hτ j) (P j) F hF
      (fun s x hx => hcarrier s j x hx) p f.val f.property)
  refine ⟨⟨g,hg⟩,?_⟩
  have hj (j : κ) : delta R M p (post R M p (P j) (prism R M (τ j) p f.val))=post R M (p+1) (P j) f.val := by
    have h := prism_identity R M (τ j) p f.val
    rw [hf,map_zero,zero_add] at h
    rw [delta_post,h,map_sub,post_pullback_zero R M (τ j) (P j) F
      (fun s x hx => hzero s j x hx) (p+1) f.val f.property,sub_zero]
  simp only [g,map_sum,hj]
  apply evaluation_injective R M (p+1)
  ext a
  simp only [map_sum,Finset.sum_apply,evaluation_post]
  exact hP _
include hP hτ hcarrier hzero in
lemma projection_prism_exactAt (p : ℕ) : (complex R M F hF).ExactAt (p+1) := by
  apply ((complex R M F hF).exactAt_iff' (i:=p) (j:=p+1) (k:=p+2) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change ((complex R M F hF).d (p+1) (p+2)).hom f=0 at hf
  rw [complex_d] at hf
  obtain ⟨g,hg⟩ := projection_prism_exact R M F hF P hP τ hτ hcarrier hzero p f (congrArg Subtype.val hf)
  refine ⟨g,?_⟩
  change ((complex R M F hF).d p (p+1)).hom g=f
  rw [complex_d]
  exact Subtype.ext hg
include hP hτ hcarrier hzero in
lemma projection_prism_acyclic [Nonempty ι] : (complex R M F hF).Acyclic := by
  intro p
  cases p with
  | zero => exact complex_exactAt_zero_of_nonempty R M F hF
  | succ p => exact projection_prism_exactAt R M F hF P hP τ hτ hcarrier hzero p
end Lech.AlternatingCech

open scoped Classical
namespace Lech.UniversalCoefficientChart
open Polynomial
universe u v
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
 
abbrev Ring := MvPolynomial {j : Fin (n+1) // j ≠ k} R

def coefficient (j : Fin (n+1)) : Ring R n k := if h : j=k then 1 else MvPolynomial.X ⟨j,h⟩

def form : (Ring R n k)[X] := Polynomial.ofFn (n+1) (coefficient R n k)

lemma coefficient_self : coefficient R n k k=1 := by simp [coefficient]
lemma coefficient_other (j : {j : Fin (n+1) // j ≠ k}) :
    coefficient R n k j=MvPolynomial.X j := by simp [coefficient,j.property]
lemma form_coeff (j : Fin (n+1)) : (form R n k).coeff j=coefficient R n k j := by
  exact Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt
lemma form_degree : (form R n k).natDegree≤n :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)
lemma form_primitive : Ideal.span (Set.range (form R n k).coeff)=⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.subset_span
  exact ⟨k,(form_coeff R n k k).trans (coefficient_self R n k)⟩

variable {T : Type v} [CommRing T] [Algebra R T]
def eval (c : Fin (n+1) → T) : Ring R n k →ₐ[R] T := MvPolynomial.aeval (fun j => c j)
lemma eval_coefficient (c : Fin (n+1) → T) (hc : c k=1) (j : Fin (n+1)) :
    eval R n k c (coefficient R n k j)=c j := by
  by_cases h : j=k
  · subst j
    simp [coefficient,eval,hc]
  · simp [coefficient,h,eval]

 

lemma eval_form (g : T[X]) (hg : g.natDegree≤n) (hk : g.coeff k=1) :
    (form R n k).map (eval R n k (fun j => g.coeff j)).toRingHom=g := by
  ext j
  rw [Polynomial.coeff_map]
  by_cases hj : j<n+1
  · rw [form_coeff R n k ⟨j,hj⟩]
    exact eval_coefficient R n k (fun j => g.coeff j) hk ⟨j,hj⟩
  · have hj' : n<j := by omega
    rw [coeff_eq_zero_of_natDegree_lt ((form_degree R n k).trans_lt hj'),map_zero,
      coeff_eq_zero_of_natDegree_lt (hg.trans_lt hj')]

lemma ext {φ ψ : Ring R n k →ₐ[R] T}
    (h : ∀ j : Fin (n+1),φ (coefficient R n k j)=ψ (coefficient R n k j)) : φ=ψ := by
  apply MvPolynomial.algHom_ext
  intro j
  simpa only [coefficient_other R n k j] using h j
end Lech.UniversalCoefficientChart


namespace Lech.ProductLinearChart
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Fin n → Bool)
abbrev Ring := MvPolynomial (Fin n) R

def a (i : Fin n) : Ring R n := if σ i then 1 else MvPolynomial.X i
def b (i : Fin n) : Ring R n := if σ i then MvPolynomial.X i else 1

lemma selected (i : Fin n) : (if σ i then a R n σ i else b R n σ i)=1 := by
  cases h : σ i <;> simp [a,b,h]
lemma other (i : Fin n) : (if σ i then b R n σ i else a R n σ i)=MvPolynomial.X i := by
  cases h : σ i <;> simp [a,b,h]

def product : (Ring R n)[X] := ∏ i : Fin n,(C (a R n σ i)*Polynomial.X+C (b R n σ i))

lemma linear_degree {S : Type*} [CommRing S] (x y : S) : (C x*Polynomial.X+C y).natDegree≤1 := by
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  · simp

lemma product_degree : (product R n σ).natDegree≤n := by
  change (∏ i : Fin n,(C (a R n σ i)*Polynomial.X+C (b R n σ i))).natDegree≤n
  calc
    (∏ i : Fin n,(C (a R n σ i)*Polynomial.X+C (b R n σ i))).natDegree ≤
      ∑ i : Fin n,(C (a R n σ i)*Polynomial.X+C (b R n σ i)).natDegree := Polynomial.natDegree_prod_le Finset.univ (fun i : Fin n => C (a R n σ i)*Polynomial.X+C (b R n σ i))
    _ ≤ ∑ _ : Fin n,(1:ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      exact linear_degree (a R n σ i) (b R n σ i)
    _ = n := by simp

lemma product_homogenize : (product R n σ).homogenize n=
    ∏ i : Fin n,(MvPolynomial.C (a R n σ i)*MvPolynomial.X 0+
      MvPolynomial.C (b R n σ i)*MvPolynomial.X 1) := by
  have h := homogenize_finsetProd (s := Finset.univ)
    (p := fun i : Fin n => C (a R n σ i)*Polynomial.X+C (b R n σ i)) (n := fun _ => 1)
    (fun i _ => linear_degree _ _)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,
    product,homogenize_add,homogenize_C_mul,homogenize_X (by omega : (1:ℕ)≠0),
    Nat.sub_self,pow_zero,mul_one,homogenize_C,pow_one] using h

variable (k : Fin (n+1))
 

abbrev chart := Localization.Away ((product R n σ).coeff k)

def denominator : (chart R n σ k)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit ((product R n σ).coeff k)).unit
lemma denominator_val : (denominator R n σ k:chart R n σ k)=
    algebraMap (Ring R n) (chart R n σ k) ((product R n σ).coeff k) :=
  (IsLocalization.Away.algebraMap_isUnit ((product R n σ).coeff k)).unit_spec

def normalized : (chart R n σ k)[X] :=
  C ((denominator R n σ k)⁻¹).val*(product R n σ).map (algebraMap (Ring R n) (chart R n σ k))

lemma normalized_degree : (normalized R n σ k).natDegree≤n :=
  (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans (product_degree R n σ))
lemma normalized_self : (normalized R n σ k).coeff k=1 := by
  rw [normalized,coeff_C_mul,coeff_map,←denominator_val,Units.inv_mul]

def target : UniversalCoefficientChart.Ring R n k →ₐ[R] chart R n σ k :=
  UniversalCoefficientChart.eval R n k (fun j => (normalized R n σ k).coeff j)

lemma target_form : (UniversalCoefficientChart.form R n k).map (target R n σ k).toRingHom=
    normalized R n σ k :=
  UniversalCoefficientChart.eval_form R n k _ (normalized_degree R n σ k) (normalized_self R n σ k)

lemma target_factorization :
    ((UniversalCoefficientChart.form R n k).map (target R n σ k).toRingHom).homogenize n=
      MvPolynomial.C ((denominator R n σ k)⁻¹).val*∏ i : Fin n,
        (MvPolynomial.C (algebraMap (Ring R n) (chart R n σ k) (a R n σ i))*MvPolynomial.X 0+
          MvPolynomial.C (algebraMap (Ring R n) (chart R n σ k) (b R n σ i))*MvPolynomial.X 1) := by
  rw [target_form,normalized,homogenize_C_mul,homogenize_map,product_homogenize]
  simp only [map_prod,map_add,map_mul,MvPolynomial.map_C,MvPolynomial.map_X]

instance targetAlgebra : Algebra (UniversalCoefficientChart.Ring R n k) (chart R n σ k) :=
  (target R n σ k).toRingHom.toAlgebra
instance targetTower :
    @IsScalarTower R (UniversalCoefficientChart.Ring R n k) (chart R n σ k)
      _ (targetAlgebra R n σ k).toSMul _ :=
  letI := targetAlgebra R n σ k
  IsScalarTower.of_algebraMap_eq fun r => ((target R n σ k).commutes r).symm

end Lech.ProductLinearChart


namespace Lech.ProductLinearChart
open Polynomial
universe u
variable (R : Type u) [CommRing R]
lemma finSucc_rename (n : ℕ) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.rename Fin.succ p)=Polynomial.C p := by
  have he : (MvPolynomial.finSuccEquiv R n).toRingHom.comp (MvPolynomial.rename Fin.succ).toRingHom=
      (Polynomial.C : MvPolynomial (Fin n) R →+* Polynomial (MvPolynomial (Fin n) R)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change MvPolynomial.finSuccEquiv R n (MvPolynomial.rename Fin.succ (MvPolynomial.C r))=_
      simp [MvPolynomial.finSuccEquiv_apply]
    · intro i
      change MvPolynomial.finSuccEquiv R n (MvPolynomial.rename Fin.succ (MvPolynomial.X i))=_
      rw [MvPolynomial.rename_X,MvPolynomial.finSuccEquiv_X_succ]
  exact RingHom.congr_fun he p
lemma rename_a (n : ℕ) (σ : Fin (n+1) → Bool) (i : Fin n) :
    MvPolynomial.rename Fin.succ (a R n (fun j => σ j.succ) i)=a R (n+1) σ i.succ := by
  cases hs : σ i.succ <;> simp [a,hs]
lemma rename_b (n : ℕ) (σ : Fin (n+1) → Bool) (i : Fin n) :
    MvPolynomial.rename Fin.succ (b R n (fun j => σ j.succ) i)=b R (n+1) σ i.succ := by
  cases hs : σ i.succ <;> simp [b,hs]
lemma rename_factor (n : ℕ) (σ : Fin (n+1) → Bool) (i : Fin n) :
    (C (a R n (fun j => σ j.succ) i)*Polynomial.X+C (b R n (fun j => σ j.succ) i)).map
      (MvPolynomial.rename Fin.succ).toRingHom=
    C (a R (n+1) σ i.succ)*Polynomial.X+C (b R (n+1) σ i.succ) := by
  simp only [Polynomial.map_add,Polynomial.map_mul,map_C,map_X]
  change C (MvPolynomial.rename Fin.succ (a R n (fun j => σ j.succ) i))*Polynomial.X+
    C (MvPolynomial.rename Fin.succ (b R n (fun j => σ j.succ) i))=_
  rw [rename_a,rename_b]
lemma product_succ (n : ℕ) (σ : Fin (n+1) → Bool) :
    product R (n+1) σ=(C (a R (n+1) σ 0)*Polynomial.X+C (b R (n+1) σ 0))*
      (product R n (fun i => σ i.succ)).map (MvPolynomial.rename Fin.succ).toRingHom := by
  rw [product,Fin.prod_univ_succ]
  apply congrArg ((C (a R (n+1) σ 0)*Polynomial.X+C (b R (n+1) σ 0))*·)
  rw [product,Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (rename_factor R n σ i).symm
lemma finSucc_a (n : ℕ) (σ : Fin (n+1) → Bool) :
    MvPolynomial.finSuccEquiv R n (a R (n+1) σ 0)=(if σ 0 then C 1 else Polynomial.X) := by
  cases hs : σ 0 <;> simp [a,hs,MvPolynomial.finSuccEquiv_X_zero]
lemma finSucc_b (n : ℕ) (σ : Fin (n+1) → Bool) :
    MvPolynomial.finSuccEquiv R n (b R (n+1) σ 0)=(if σ 0 then Polynomial.X else C 1) := by
  cases hs : σ 0 <;> simp [b,hs,MvPolynomial.finSuccEquiv_X_zero]
lemma product_succ_coeff_zero (n : ℕ) (σ : Fin (n+1) → Bool) :
    MvPolynomial.finSuccEquiv R n ((product R (n+1) σ).coeff 0)=
      (if σ 0 then Polynomial.X else C 1)*C ((product R n (fun i => σ i.succ)).coeff 0) := by
  rw [product_succ,mul_coeff_zero]
  simp only [coeff_add,coeff_C_mul,coeff_X_zero,mul_zero,coeff_C_zero,zero_add,coeff_map]
  change MvPolynomial.finSuccEquiv R n (b R (n+1) σ 0 * MvPolynomial.rename Fin.succ
    ((product R n (fun i => σ i.succ)).coeff 0))=_
  rw [map_mul,finSucc_b,finSucc_rename]
lemma product_succ_coeff_succ (n : ℕ) (σ : Fin (n+1) → Bool) (j : ℕ) :
    MvPolynomial.finSuccEquiv R n ((product R (n+1) σ).coeff (j+1))=
      (if σ 0 then C 1 else Polynomial.X)*C ((product R n (fun i => σ i.succ)).coeff j)+
      (if σ 0 then Polynomial.X else C 1)*C ((product R n (fun i => σ i.succ)).coeff (j+1)) := by
  rw [product_succ,add_mul,coeff_add,mul_assoc,coeff_C_mul,coeff_X_mul,coeff_C_mul]
  simp only [coeff_map]
  change MvPolynomial.finSuccEquiv R n (a R (n+1) σ 0 * MvPolynomial.rename Fin.succ
    ((product R n (fun i => σ i.succ)).coeff j) + b R (n+1) σ 0 * MvPolynomial.rename Fin.succ
    ((product R n (fun i => σ i.succ)).coeff (j+1)))=_
  rw [map_add,map_mul,map_mul,finSucc_a,finSucc_b,finSucc_rename,finSucc_rename]
 

theorem coefficient_regular (n : ℕ) (σ : Fin n → Bool) (k : Fin (n+1)) :
    IsRegular ((product R n σ).coeff k) := by
  induction n with
  | zero =>
    have hk : k=0 := by apply Fin.ext; omega
    simp only [hk,product,Finset.univ_eq_empty,Finset.prod_empty,Fin.val_zero,coeff_one_zero]
    exact isRegular_one
  | succ n ih =>
    let p := (product R (n+1) σ).coeff k
    have hr : IsRegular (MvPolynomial.finSuccEquiv R n p) := by
      apply isRegular_iff_mem_nonZeroDivisors.mpr
      cases k using Fin.cases with
      | zero =>
        by_cases hs : σ 0=true
        · apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
          simpa only [p,Fin.val_zero,product_succ_coeff_zero,hs,↓reduceIte,
            coeff_X_mul,coeff_C_zero] using (ih (fun i => σ i.succ) 0).mem_nonZeroDivisors
        · apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 0
          simpa only [p,Fin.val_zero,product_succ_coeff_zero,hs,↓reduceIte,
            Bool.false_eq_true,C_1,one_mul,coeff_C_zero] using (ih (fun i => σ i.succ) 0).mem_nonZeroDivisors
      | succ k =>
        by_cases hs : σ 0=true
        · apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 0
          simpa only [p,Fin.val_succ,product_succ_coeff_succ,hs,↓reduceIte,C_1,one_mul,
            coeff_add,coeff_X_mul_zero,coeff_C_zero,add_zero] using (ih (fun i => σ i.succ) k).mem_nonZeroDivisors
        · apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
          simpa only [p,Fin.val_succ,product_succ_coeff_succ,hs,↓reduceIte,C_1,one_mul,
            Bool.false_eq_true,coeff_add,coeff_X_mul,coeff_C_zero,coeff_C_succ,add_zero] using
            (ih (fun i => σ i.succ) k).mem_nonZeroDivisors
    refine ⟨?_,?_⟩
    · intro x y h
      apply (MvPolynomial.finSuccEquiv R n).injective
      exact hr.left (by simpa only [map_mul] using congrArg (MvPolynomial.finSuccEquiv R n) h)
    · intro x y h
      apply (MvPolynomial.finSuccEquiv R n).injective
      exact hr.right (by simpa only [map_mul] using congrArg (MvPolynomial.finSuccEquiv R n) h)
end Lech.ProductLinearChart
end
end

end OAI
