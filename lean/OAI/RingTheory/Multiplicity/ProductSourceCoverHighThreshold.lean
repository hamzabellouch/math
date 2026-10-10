import Mathlib
import OAI.RingTheory.Multiplicity.ProductSourceCoverOrdinaryPositive

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
open Set AddMonoidAlgebra CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def highThreshold (m : Fin n → ℤ) : ℕ := Finset.univ.sup (fun i => (m i).natAbs)
lemma level_high (m : Fin n → ℤ) (d N : ℕ) (hd : 0<d) (hN : highThreshold n m≤N) :
    ∀ i,-1≤levelTwist n m d N i := by
  intro i
  have hm : (m i).natAbs≤N := (Finset.le_sup (f:=fun i : Fin n => (m i).natAbs) (Finset.mem_univ i)).trans hN
  have hm' : |m i|≤(N:ℤ) := by rw [←Int.natCast_natAbs];exact_mod_cast hm
  have hd' : (1:ℤ)≤(d:ℤ) := by exact_mod_cast hd
  have hN' : (0:ℤ)≤(N:ℤ) := Nat.cast_nonneg _
  have hn := neg_le_abs (m i)
  dsimp [levelTwist]
  nlinarith

def fraction (s : Finset (Fin (n+1))) (N : ℕ) : Ambient R n →ₗ[R] GridAmbient R n :=
  (LinearMap.mulLeft R ((↑((denominator_unit R n s).unit⁻¹):GridAmbient R n)^N)).comp (embed R n).toLinearMap
lemma fraction_spec (s : Finset (Fin (n+1))) (N : ℕ) (h : Ambient R n) :
    embed R n (denominator R n s)^N*fraction R n s N h=embed R n h := by
  change embed R n (denominator R n s)^N*((↑((denominator_unit R n s).unit⁻¹):GridAmbient R n)^N*embed R n h)=_
  have hu : embed R n (denominator R n s)*(↑((denominator_unit R n s).unit⁻¹):GridAmbient R n)=1 := by
    simpa only [IsUnit.unit_spec] using Units.mul_inv (denominator_unit R n s).unit
  rw [←mul_assoc,←mul_pow,hu,one_pow,one_mul]
lemma uniform_witness (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (p : ℕ)
    (f : AlternatingCech.sorted R (GridAmbient R n) (grid R n m s) p) :
    ∃ N : ℕ,highThreshold n m≤N ∧
      ∃ h : AlternatingCech.sorted R (Ambient R n) (ringSections R n (levelTwist n m s.card N)) p,
      ∀ t,embed R n (denominator R n s)^N*(f t:GridAmbient R n)=embed R n (h t) := by
  have hf : ∀ t : powersetCard (Chart n) p,∃ N : ℕ,∃ h : Ambient R n,
      h∈ringSections R n (levelTwist n m s.card N) t.val ∧
      embed R n (denominator R n s)^N*(f t:GridAmbient R n)=embed R n h := fun t => (f t).property
  choose N h hh he using hf
  let M := max (highThreshold n m) (Finset.univ.sup N)
  have hNM (t : powersetCard (Chart n) p) : N t≤M :=
    (Finset.le_sup (f:=N) (Finset.mem_univ t)).trans (le_max_right _ _)
  have hraise (t : powersetCard (Chart n) p) := raise_witness R n m s t.val (f t) (N t) M (hNM t) (h t) (hh t) (he t)
  choose H hH heH using hraise
  exact ⟨M,le_max_left _ _,fun t => ⟨H t,hH t⟩,heH⟩
variable [LinearOrder (Chart n)]
local instance gridSourceDecEq : DecidableEq (Chart n) := LinearOrder.toDecidableEq
 

lemma grid_source_exact (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hs : s.Nonempty)
    (p : ℕ) (f : AlternatingCech.sorted R (GridAmbient R n) (grid R n m s) (p+1))
    (hf : AlternatingCech.sortedDelta R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s) (p+1) f=0) :
    ∃ g : AlternatingCech.sorted R (GridAmbient R n) (grid R n m s) p,
      AlternatingCech.sortedDelta R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s) p g=f := by
  obtain ⟨N,hN,h,he⟩ := uniform_witness R n m s (p+1) f
  let T := levelTwist n m s.card N
  let Q := embed R n (denominator R n s)^N
  have hT : ∀ i,-1≤T i := level_high n m s.card N (Finset.card_pos.mpr hs) hN
  have hcycled : AlternatingCech.sortedDelta R (Ambient R n) (ringSections R n T) (ringSections_mono R n T) (p+1) h=0 := by
    have he' : (fun t => (embed R n).toLinearMap (h t))=(fun t => (LinearMap.mulLeft R Q) (f t:GridAmbient R n)) :=
      funext (fun t => (he t).symm)
    have hd := congrArg (AlternatingCech.rawDelta R (GridAmbient R n) (p+1)) he'
    rw [AlternatingCech.rawDelta_post,AlternatingCech.rawDelta_post,
      AlternatingCech.rawDelta_sorted R (Ambient R n) (ringSections R n T) (ringSections_mono R n T),
      AlternatingCech.rawDelta_sorted R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s),hf] at hd
    funext t
    apply Subtype.ext
    apply embed_injective R n
    simpa only [Pi.zero_apply,Submodule.coe_zero,map_zero,AlgHom.toLinearMap_apply] using congrFun hd t
  let C := AlternatingCech.sortedComplex R (Ambient R n) (ringSections R n T) (ringSections_mono R n T)
  have hc := (C.exactAt_iff' (i:=p) (j:=p+1) (k:=p+2) (by simp) (by simp)).mp (ring_sorted_acyclic R n T hT (p+1))
  rw [ShortComplex.moduleCat_exact_iff] at hc
  obtain ⟨g,hg⟩ := hc h (by
    change (C.d (p+1) (p+2)).hom h=0
    rw [AlternatingCech.sortedComplex_d]
    exact hcycled)
  change (C.d p (p+1)).hom g=h at hg
  rw [AlternatingCech.sortedComplex_d] at hg
  change AlternatingCech.sorted R (Ambient R n) (ringSections R n T) p at g
  change AlternatingCech.sortedDelta R (Ambient R n) (ringSections R n T) (ringSections_mono R n T) p g=h at hg
  let G : AlternatingCech.sorted R (GridAmbient R n) (grid R n m s) p := fun t =>
    ⟨fraction R n s N (g t),N,(g t:Ambient R n),(g t).property,fraction_spec R n s N (g t)⟩
  refine ⟨G,?_⟩
  have hd : (fun t => (AlternatingCech.sortedDelta R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s) p G t:GridAmbient R n))=
      (fun t => fraction R n s N (h t)) := by
    rw [←AlternatingCech.rawDelta_sorted]
    change AlternatingCech.rawDelta R (GridAmbient R n) p (fun t => fraction R n s N (g t))=_
    rw [AlternatingCech.rawDelta_post,AlternatingCech.rawDelta_sorted R (Ambient R n) (ringSections R n T) (ringSections_mono R n T),hg]
  funext t
  apply Subtype.ext
  apply ((denominator_unit R n s).pow N).isRegular.left
  change embed R n (denominator R n s)^N*_ = embed R n (denominator R n s)^N*_
  rw [congrFun hd t,fraction_spec,he t]

 

theorem grid_source_acyclic (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    (AlternatingCech.sortedComplex R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s)).Acyclic := by
  intro p
  cases p with
  | zero =>
    apply (AlternatingCech.complex_exactAt_zero_of_nonempty R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s)).of_iso
    convert AlternatingCech.cochainsSortedIso R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s) using 1
    congr 1
  | succ p =>
    apply ((AlternatingCech.sortedComplex R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s)).exactAt_iff'
      (i:=p) (j:=p+1) (k:=p+2) (by simp) (by simp)).mpr
    rw [ShortComplex.moduleCat_exact_iff]
    intro f hf
    change ((AlternatingCech.sortedComplex R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s)).d (p+1) (p+2)).hom f=0 at hf
    rw [AlternatingCech.sortedComplex_d] at hf
    obtain ⟨g,hg⟩ := grid_source_exact R n m s hs p f hf
    refine ⟨g,?_⟩
    change ((AlternatingCech.sortedComplex R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s)).d p (p+1)).hom g=f
    rw [AlternatingCech.sortedComplex_d]
    exact hg
end Lech.ProductSourceCover


namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (K : Type u) [CommRing K] [Algebra R K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (F : Finset ι → Submodule R K)
variable (A : Type u) [CommRing A] [Algebra R A] (φ : A →ₐ[R] K)
variable (hstable : ∀ (s : Finset ι) (a : A) (x : K),x∈F s → φ a*x∈F s)
variable (q : ι → A) (hq : Ideal.span (Set.range q)=⊤)
variable (hclear : ∀ (s : Finset ι) (j : ι) (x : K),x∈F (insert j s) → ∃ N : ℕ,φ (q j)^N*x∈F s)
include hstable hclear in
lemma scalar_uniform_clear (n : ℕ) (f : cochains R K F (n+1)) :
    ∃ N : ℕ,∀ (j : ι) (a : Fin n → ι),φ (q j)^N*evaluation R K (n+1) f.val (Fin.cons j a)∈F (FiniteCoverCech.intersection a) := by
  choose m hm using fun (p : ι × (Fin n → ι)) =>
    hclear (FiniteCoverCech.intersection p.2) p.1 (evaluation R K (n+1) f.val (Fin.cons p.1 p.2)) (by
      rw [←FiniteCoverCech.intersection_cons];exact f.property _)
  let N := Finset.univ.sup m
  refine ⟨N,fun j a => ?_⟩
  have hn : m (j,a)≤N := Finset.le_sup (Finset.mem_univ _)
  rw [←Nat.sub_add_cancel hn,pow_add,mul_assoc,←map_pow]
  exact hstable _ _ _ (hm (j,a))
include hstable hq hclear in
 

theorem scalar_exact (n : ℕ) (f : cochains R K F (n+1)) (hf : delta R K (n+1) f.val=0) :
    ∃ g : cochains R K F n,delta R K n g.val=f.val := by
  obtain ⟨N,hN⟩ := scalar_uniform_clear R K F A φ hstable q hclear n f
  obtain ⟨c,hc⟩ := FiniteCoverCech.partition A q hq N
  let P (j : ι) : K →ₗ[R] K := LinearMap.mulLeft R (φ (c j*q j^N))
  let g : Alt R K (ι:=ι) n := ∑ j,post R K n (P j) (extra R K j n f.val)
  have hg : g∈cochains R K F n := by
    intro a
    change evaluation R K n g a∈F (FiniteCoverCech.intersection a)
    simp only [g,map_sum,Finset.sum_apply,evaluation_post,evaluation_extra]
    apply (F _).sum_mem
    intro j _
    change φ (c j*q j^N)*evaluation R K (n+1) f.val (Fin.cons j a)∈_
    rw [map_mul,map_pow,mul_assoc]
    exact hstable _ _ _ (hN j a)
  refine ⟨⟨g,hg⟩,?_⟩
  have hj (j : ι) : delta R K n (extra R K j n f.val)=f.val := by
    have h := extra_delta R K j n f.val
    rw [hf,map_zero,zero_add] at h
    exact h
  simp only [g,map_sum,delta_post,hj]
  apply evaluation_injective R K (n+1)
  ext a
  simp only [map_sum,Finset.sum_apply,evaluation_post]
  change (∑ j,φ (c j*q j^N)*evaluation R K (n+1) f.val a)=_
  rw [←Finset.sum_mul,←map_sum,hc,map_one,one_mul]
include hstable hq hclear in
lemma scalar_complex_acyclic [Nonempty ι] (hF : Monotone F) : (complex R K F hF).Acyclic := by
  intro n
  cases n with
  | zero => exact complex_exactAt_zero_of_nonempty R K F hF
  | succ n =>
    apply ((complex R K F hF).exactAt_iff' (i:=n) (j:=n+1) (k:=n+2) (by simp) (by simp)).mpr
    rw [ShortComplex.moduleCat_exact_iff]
    intro f hf
    change ((complex R K F hF).d (n+1) (n+2)).hom f=0 at hf
    rw [complex_d] at hf
    obtain ⟨g,hg⟩ := scalar_exact R K F A φ hstable q hq hclear n f (congrArg Subtype.val hf)
    refine ⟨g,?_⟩
    change ((complex R K F hF).d n (n+1)).hom g=f
    rw [complex_d]
    exact Subtype.ext hg
end Lech.AlternatingCech


namespace Lech.ProductLinearChart
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Fin n → Bool)
lemma linear_content_top (i : Fin n) :
    (C (a R n σ i)*Polynomial.X+C (b R n σ i)).contentIdeal=⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  cases hs : σ i
  · have hi := (C (a R n σ i)*Polynomial.X+C (b R n σ i)).coeff_mem_contentIdeal 0
    simpa only [coeff_add,coeff_C_mul,coeff_X_zero,mul_zero,zero_add,coeff_C_zero,b,hs,Bool.false_eq_true,↓reduceIte] using hi
  · have hi := (C (a R n σ i)*Polynomial.X+C (b R n σ i)).coeff_mem_contentIdeal 1
    simpa only [coeff_add,coeff_C_mul,coeff_X_one,mul_one,coeff_C_succ,add_zero,a,hs,↓reduceIte] using hi
lemma product_content_top : (product R n σ).contentIdeal=⊤ := by
  apply Finset.prod_induction (fun i : Fin n => C (a R n σ i)*Polynomial.X+C (b R n σ i))
    (fun p : (Ring R n)[X] => p.contentIdeal=⊤)
  · intro p q hp hq
    exact contentIdeal_mul_eq_top_of_contentIdeal_eq_top hp hq
  · exact contentIdeal_one
  · intro i _
    exact linear_content_top R n σ i
 

lemma coefficients_span :
    Ideal.span (Set.range (fun k : Fin (n+1) => (product R n σ).coeff k))=⊤ := by
  apply top_unique
  rw [←product_content_top R n σ,contentIdeal_def,Ideal.span_le]
  intro r hr
  obtain ⟨j,hj,rfl⟩ := Polynomial.mem_coeffs_iff.mp hr
  by_cases h : j<n+1
  · exact Ideal.subset_span (Set.mem_range_self (⟨j,h⟩ : Fin (n+1)))
  · have hz : (product R n σ).coeff j=0 := coeff_eq_zero_of_natDegree_lt (by
      have hd := product_degree R n σ
      omega)
    exact ((Polynomial.mem_support_iff.mp hj) hz).elim
end Lech.ProductLinearChart


namespace Lech.ProductSourceCover
open AddMonoidAlgebra CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma monomialUnit_sum {ι : Type} (s : Finset ι) (e : ι → Exponent n) :
    ProductLaurent.monomialUnit R n (∑ i∈s,e i)=∏ i∈s,ProductLaurent.monomialUnit R n (e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty];apply Units.ext;rfl
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,ProductLaurent.monomialUnit_add,ih]
lemma chartUnit_monomial (σ : Chart n) :
    ProductLaurent.chartUnit R n σ=ProductLaurent.monomialUnit R n (twistExponent n (fun _ => 1) σ) := by
  have he : twistExponent n (fun _ => 1) σ=∑ i : Fin n,if σ i then Finsupp.single i 1 else 0 := by
    ext j
    simp only [twistExponent_apply,Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single j]
    · cases h : σ j <;> simp
    · intro i _ hij
      cases h : σ i <;> simp [Finsupp.single_eq_of_ne (Ne.symm hij)]
    · simp
  rw [he,monomialUnit_sum,ProductLaurent.chartUnit]
  apply Finset.prod_congr rfl
  intro i _
  cases hs : σ i
  · simp only [Bool.false_eq_true,↓reduceIte]
    apply Units.ext
    rfl
  · rfl
lemma chartUnit_inv_section (σ : Chart n) :
    (↑((ProductLaurent.chartUnit R n σ)⁻¹):Ambient R n)∈ringSections R n (fun _ => -1) {σ} := by
  rw [chartUnit_monomial,←ProductLaurent.monomialUnit_neg]
  change single (-(twistExponent n (fun _ => 1) σ)) (1:R)∈_
  apply single_mem
  intro i
  simp only [Finsupp.neg_apply,twistExponent_apply]
  cases hs : σ i <;> simp [hs]
lemma chartMap_zero_section (σ : Chart n) (a : ProductLinearChart.Ring R n) :
    ProductLaurent.chartMap R n σ a∈ringSections R n 0 {σ} := by
  have he : twistExponent n 0 σ=0 := by ext i;simp [twistExponent_apply]
  have h := chartLine_mem R n 0 σ a
  change (ProductLaurent.monomialUnit R n (twistExponent n 0 σ):Ambient R n)*ProductLaurent.chartMap R n σ a∈_ at h
  rw [he] at h
  simpa only [ProductLaurent.monomialUnit,←one_def,one_mul] using h

def chartScalar (σ : Chart n) : ProductLinearChart.Ring R n →ₐ[R] GridAmbient R n :=
  (embed R n).comp (ProductLaurent.chartMap R n σ)
lemma grid_chart_stable (m : Fin n → ℤ) (t : Finset (Chart n)) (σ : Chart n) (hσ : σ∈t)
    (s : Finset (Fin (n+1))) (a : ProductLinearChart.Ring R n) (x : GridAmbient R n)
    (hx : x∈grid R n m s t) : chartScalar R n σ a*x∈grid R n m s t := by
  obtain ⟨N,h,hh,he⟩ := hx
  refine ⟨N,ProductLaurent.chartMap R n σ a*h,?_,?_⟩
  · have ha := ringSections_mono R n 0 (Finset.singleton_subset_iff.mpr hσ) (chartMap_zero_section R n σ a)
    simpa only [zero_add] using mul_mem R n 0 (levelTwist n m s.card N) t _ h ha hh
  · change embed R n (denominator R n s)^N*(embed R n (ProductLaurent.chartMap R n σ a)*x)=_
    rw [mul_left_comm,he,map_mul]
lemma grid_target_clear (m : Fin n → ℤ) (t : Finset (Chart n)) (σ : Chart n) (hσ : σ∈t)
    (s : Finset (Fin (n+1))) (k : Fin (n+1)) (x : GridAmbient R n)
    (hx : x∈grid R n m (insert k s) t) :
    ∃ N : ℕ,chartScalar R n σ ((ProductLinearChart.product R n σ).coeff k)^N*x∈grid R n m s t := by
  by_cases hk : k∈s
  · refine ⟨0,?_⟩
    simpa only [pow_zero,one_mul,Finset.insert_eq_of_mem hk] using hx
  obtain ⟨N,h,hh,he⟩ := hx
  let u : Ambient R n := ↑((ProductLaurent.chartUnit R n σ)⁻¹)
  have hu : u^N∈ringSections R n (N • fun _ => (-1:ℤ)) t :=
    pow_mem R n (fun _ => (-1:ℤ)) t u (ringSections_mono R n _ (Finset.singleton_subset_iff.mpr hσ) (chartUnit_inv_section R n σ)) N
  have ht : (N • fun _ : Fin n => (-1:ℤ))+levelTwist n m (insert k s).card N=levelTwist n m s.card N := by
    ext i
    change (N • (-1:ℤ))+(m i+(N:ℤ)*((insert k s).card:ℤ))=m i+(N:ℤ)*(s.card:ℤ)
    rw [Finset.card_insert_of_notMem hk,Nat.cast_add,Nat.cast_one,nsmul_eq_mul]
    ring
  refine ⟨N,N,u^N*h,?_,?_⟩
  · have hb := mul_mem R n (N • fun _ => (-1:ℤ)) (levelTwist n m (insert k s).card N) t (u^N) h hu hh
    rwa [ht] at hb
  · have hc : chartScalar R n σ ((ProductLinearChart.product R n σ).coeff k)=embed R n u*embed R n (targetCoeff R n k) := by
      change embed R n (ProductLaurent.chartMap R n σ ((ProductLinearChart.product R n σ).coeff k))=_
      rw [ProductLaurent.chartMap_coefficient,map_mul]
    have hd : denominator R n (insert k s)=targetCoeff R n k*denominator R n s := Finset.prod_insert hk
    rw [hc,mul_pow,map_mul,map_pow]
    calc
      _ = embed R n u^N*(embed R n (denominator R n (insert k s))^N*x) := by rw [hd,map_mul,mul_pow];ring
      _ = _ := by rw [he]

 

theorem grid_target_acyclic (m : Fin n → ℤ) (t : Finset (Chart n)) (ht : t.Nonempty) :
    (AlternatingCech.sortedComplex R (GridAmbient R n) (fun s => grid R n m s t) (grid_target_mono R n m t)).Acyclic := by
  obtain ⟨σ,hσ⟩ := ht
  intro j
  have h := AlternatingCech.scalar_complex_acyclic R (GridAmbient R n) (fun s => grid R n m s t)
    (ProductLinearChart.Ring R n) (chartScalar R n σ) (grid_chart_stable R n m t σ hσ)
    (fun k : Fin (n+1) => (ProductLinearChart.product R n σ).coeff k)
    (ProductLinearChart.coefficients_span R n σ) (grid_target_clear R n m t σ hσ) (grid_target_mono R n m t) j
  apply h.of_iso
  convert AlternatingCech.cochainsSortedIso R (GridAmbient R n) (fun s => grid R n m s t) (grid_target_mono R n m t) using 1
  congr 1
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
 

abbrev gridComplex (m : Fin n → ℤ) :=
  DoubleCech.complex R (GridAmbient R n) (grid R n m) (grid_target_mono R n m) (grid_source_mono R n m)
 

def grid_homology_comparison (m : Fin n → ℤ) (i : ℤ) :
    (((gridComplex R n m).X 0).extend ComplexShape.embeddingUpNat).homology i ≅
      (((flip (gridComplex R n m)).X 0).extend ComplexShape.embeddingUpNat).homology i :=
  DoubleCech.coverComparison R (GridAmbient R n) (grid R n m)
    (grid_target_mono R n m) (grid_source_mono R n m)
    (fun _p hp s => grid_source_acyclic R n m s.val (Finset.card_pos.mp (s.property.symm ▸ hp)))
    (fun _q hq t => grid_target_acyclic R n m t.val (Finset.card_pos.mp (t.property.symm ▸ hq))) i
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma grid_empty_target (m : Fin n → ℤ) (t : Finset (Chart n)) :
    (ringSections R n m t).map (embed R n).toLinearMap=grid R n m ∅ t := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨0,x,?_,?_⟩
    · have ht : levelTwist n m (∅ : Finset (Fin (n+1))).card 0=m := by ext i;simp [levelTwist]
      exact ht.symm ▸ hx
    · simp only [pow_zero,one_mul,AlgHom.toLinearMap_apply]
  · rintro x ⟨N,h,hh,he⟩
    simp only [denominator,AwayCover.denominator,Finset.prod_empty,map_one,one_pow,one_mul] at he
    refine ⟨h,?_,?_⟩
    · have ht : levelTwist n m (∅ : Finset (Fin (n+1))).card N=m := by ext i;simp [levelTwist]
      exact ht ▸ hh
    · simpa only [AlgHom.toLinearMap_apply] using he.symm
variable [LinearOrder (Chart n)]
 

def gridSourceEdgeIso (m : Fin n → ℤ) :
    AlternatingCech.sortedComplex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m) ≅
      AlternatingCech.sortedComplex R (GridAmbient R n) (grid R n m ∅) (grid_source_mono R n m ∅) :=
  AlternatingCech.sortedFamilyIso R (Ambient R n) (GridAmbient R n)
    (ringSections R n m) (grid R n m ∅) (embed R n).toLinearMap (embed_injective R n)
    (grid_empty_target R n m) (ringSections_mono R n m) (grid_source_mono R n m ∅)
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
def sourceSectionComplex (m : Fin n → ℤ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  AlternatingCech.sortedComplex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)
def targetSectionComplex (m : Fin n → ℤ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  AlternatingCech.sortedComplex R (GridAmbient R n) (fun s => grid R n m s ∅) (grid_target_mono R n m ∅)
 

def sectionCohomologyComparison (m : Fin n → ℤ) (i : ℤ) :
    ((sourceSectionComplex R n m).extend ComplexShape.embeddingUpNat).homology i ≅
      ((targetSectionComplex R n m).extend ComplexShape.embeddingUpNat).homology i :=
  (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
    ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso
      (gridSourceEdgeIso R n m ≪≫ (DoubleCech.rowZeroIso R (GridAmbient R n) (grid R n m)
        (grid_target_mono R n m) (grid_source_mono R n m)).symm)) ≪≫
    grid_homology_comparison R n m i ≪≫
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
      ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso
        (DoubleCech.columnZeroIso R (GridAmbient R n) (grid R n m)
          (grid_target_mono R n m) (grid_source_mono R n m)))
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
 

def sourceCech (m : Fin n → ℤ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  AlternatingCech.unaugmentedComplex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)
 
def targetCech (m : Fin n → ℤ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  AlternatingCech.unaugmentedComplex R (GridAmbient R n) (fun s => grid R n m s ∅) (grid_target_mono R n m ∅)
def gridSourceUnaugmentedIso (m : Fin n → ℤ) : sourceCech R n m ≅
    AlternatingCech.unaugmentedComplex R (GridAmbient R n) (grid R n m ∅) (grid_source_mono R n m ∅) :=
  AlternatingCech.sortedUnaugmentedFamilyIso R (Ambient R n) (GridAmbient R n)
    (ringSections R n m) (grid R n m ∅) (embed R n).toLinearMap (embed_injective R n)
    (grid_empty_target R n m) (ringSections_mono R n m) (grid_source_mono R n m ∅)
def gridUnaugmentedComparison (m : Fin n → ℤ) (i : ℤ) :
    ((AlternatingCech.unaugmentedComplex R (GridAmbient R n) (grid R n m ∅) (grid_source_mono R n m ∅)).extend ComplexShape.embeddingUpNat).homology i ≅
      ((targetCech R n m).extend ComplexShape.embeddingUpNat).homology i :=
  DoubleCech.unaugmentedCoverComparison R (GridAmbient R n) (grid R n m)
    (grid_target_mono R n m) (grid_source_mono R n m)
    (fun _p hp s => grid_source_acyclic R n m s.val (Finset.card_pos.mp (s.property.symm ▸ hp)))
    (fun _q hq t => grid_target_acyclic R n m t.val (Finset.card_pos.mp (t.property.symm ▸ hq))) i
 

def cechCohomologyComparison (m : Fin n → ℤ) (i : ℤ) :
    ((sourceCech R n m).extend ComplexShape.embeddingUpNat).homology i ≅
      ((targetCech R n m).extend ComplexShape.embeddingUpNat).homology i :=
  (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
    ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso (gridSourceUnaugmentedIso R n m)) ≪≫
    gridUnaugmentedComparison R n m i
end Lech.ProductSourceCover
end
end

end OAI
