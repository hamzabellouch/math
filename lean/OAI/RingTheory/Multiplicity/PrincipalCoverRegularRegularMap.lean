import Mathlib
import OAI.RingTheory.Multiplicity.AlternatingCechPost

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
namespace Lech.PrincipalCoverRegular
universe u v
variable {R : Type u} [CommRing R] {ι : Type v}
lemma regular_map {M : Submonoid R} {S : Type*} [CommRing S] [Algebra R S] [IsLocalization M S]
    {x : R} (hx : IsRegular x) : IsRegular (algebraMap R S x) :=
  isRegular_iff_mem_nonZeroDivisors.mpr (IsLocalization.nonZeroDivisors_le_comap M S hx.mem_nonZeroDivisors)
 

theorem regular_of_cover (q : ι → R) (hq : Ideal.span (Set.range q)=⊤) (x : R)
    (h : ∀ i,IsRegular (algebraMap R (Localization.Away (q i)) x)) : IsRegular x := by
  constructor
  · intro y z hyz
    apply Localization.algebraMap_injective_of_span_eq_top (Set.range q) hq
    funext a
    obtain ⟨a,⟨i,rfl⟩⟩ := a
    simp only [Pi.algebraMap_apply]
    exact (h i).left (by simpa only [map_mul] using congrArg (algebraMap R (Localization.Away (q i))) hyz)
  · intro y z hyz
    apply Localization.algebraMap_injective_of_span_eq_top (Set.range q) hq
    funext a
    obtain ⟨a,⟨i,rfl⟩⟩ := a
    simp only [Pi.algebraMap_apply]
    exact (h i).right (by simpa only [map_mul] using congrArg (algebraMap R (Localization.Away (q i))) hyz)
end Lech.PrincipalCoverRegular


namespace Lech.ProductLaurent
open AddMonoidAlgebra Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
abbrev Exponent := Fin n →₀ ℤ
abbrev Ring := AddMonoidAlgebra R (Exponent n)
 
def signedExponent (σ : Fin n → Bool) : (Fin n →₀ ℕ) →+ Exponent n where
  toFun e := Finsupp.onFinset e.support (fun i => if σ i then -(e i:ℤ) else (e i:ℤ)) (by
    intro i hi
    by_contra he
    have hei : e i=0 := Finsupp.notMem_support_iff.mp he
    simp [hei] at hi)
  map_zero' := by ext i;simp
  map_add' a b := by
    ext i
    change (if σ i then -((a i+b i:ℕ):ℤ) else ((a i+b i:ℕ):ℤ))=
      (if σ i then -(a i:ℤ) else (a i:ℤ))+(if σ i then -(b i:ℤ) else (b i:ℤ))
    split_ifs <;> push_cast <;> abel
lemma signedExponent_apply (σ : Fin n → Bool) (e : Fin n →₀ ℕ) (i : Fin n) :
    signedExponent n σ e i=(if σ i then -(e i:ℤ) else (e i:ℤ)) := rfl
lemma signedExponent_injective (σ : Fin n → Bool) : Function.Injective (signedExponent n σ) := by
  intro a b h
  ext i
  have hi := congrArg (fun e : Exponent n => e i) h
  simp only [signedExponent_apply] at hi
  cases hs : σ i <;> simp [hs] at hi <;> exact hi

def chartMap (σ : Fin n → Bool) : ProductLinearChart.Ring R n →ₐ[R] Ring R n :=
  mapDomainAlgHom R R (signedExponent n σ)
lemma chartMap_injective (σ : Fin n → Bool) : Function.Injective (chartMap R n σ) :=
  mapDomain_injective (signedExponent_injective n σ)
lemma chartMap_monomial (σ : Fin n → Bool) (e : Fin n →₀ ℕ) (r : R) :
    chartMap R n σ (MvPolynomial.monomial e r)=single (signedExponent n σ e) r :=
  mapDomain_single

def monomialUnit (e : Exponent n) : (Ring R n)ˣ where
  val := single e 1
  inv := single (-e) 1
  val_inv := by rw [single_mul_single,add_neg_cancel,one_mul,←one_def]
  inv_val := by rw [single_mul_single,neg_add_cancel,one_mul,←one_def]
abbrev variableUnit (i : Fin n) : (Ring R n)ˣ := monomialUnit R n (Finsupp.single i 1)
lemma monomialUnit_add (e f : Exponent n) : monomialUnit R n (e+f)=monomialUnit R n e*monomialUnit R n f := by
  apply Units.ext
  change single (e+f) (1:R)=single e 1*single f 1
  rw [single_mul_single,one_mul]
lemma monomialUnit_neg (e : Exponent n) : monomialUnit R n (-e)=(monomialUnit R n e)⁻¹ := by
  apply Units.ext
  rfl
lemma chartMap_X (σ : Fin n → Bool) (i : Fin n) :
    chartMap R n σ (MvPolynomial.X i)=(if σ i then (variableUnit R n i)⁻¹ else variableUnit R n i : (Ring R n)ˣ) := by
  rw [MvPolynomial.X,chartMap_monomial]
  have he : signedExponent n σ (Finsupp.single i 1)=if σ i then -Finsupp.single i 1 else Finsupp.single i 1 := by
    ext j
    by_cases hj : j=i
    · subst j; cases h : σ i <;> simp [signedExponent_apply,h]
    · cases h : σ i <;> simp [signedExponent_apply,hj]
  rw [he]
  cases h : σ i <;> simp only [Bool.false_eq_true,↓reduceIte] <;> rfl
 

def chartUnit (σ : Fin n → Bool) : (Ring R n)ˣ := ∏ i,if σ i then variableUnit R n i else 1
lemma chartMap_a (σ : Fin n → Bool) (i : Fin n) :
    chartMap R n σ (ProductLinearChart.a R n σ i)=
      (if σ i then (variableUnit R n i)⁻¹ else 1 : (Ring R n)ˣ)*(variableUnit R n i:Ring R n) := by
  cases hs : σ i
  · simp only [ProductLinearChart.a,hs,Bool.false_eq_true,↓reduceIte,chartMap_X,Units.val_one,one_mul]
  · simp only [ProductLinearChart.a,hs,↓reduceIte,map_one,Units.inv_mul]
lemma chartMap_b (σ : Fin n → Bool) (i : Fin n) :
    chartMap R n σ (ProductLinearChart.b R n σ i)=
      (if σ i then (variableUnit R n i)⁻¹ else 1 : (Ring R n)ˣ) := by
  cases hs : σ i <;> simp [ProductLinearChart.b,hs,chartMap_X]
 
def binaryForm : (Ring R n)[X] := ∏ i,(C (variableUnit R n i:Ring R n)*Polynomial.X+1)
lemma chartMap_factor (σ : Fin n → Bool) (i : Fin n) :
    (C (ProductLinearChart.a R n σ i)*Polynomial.X+C (ProductLinearChart.b R n σ i)).map
      (chartMap R n σ).toRingHom=
    C (if σ i then (↑((variableUnit R n i)⁻¹) : Ring R n) else 1)*
      (C (variableUnit R n i:Ring R n)*Polynomial.X+1) := by
  simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X]
  change C (chartMap R n σ (ProductLinearChart.a R n σ i))*Polynomial.X+
    C (chartMap R n σ (ProductLinearChart.b R n σ i))=_
  rw [chartMap_a,chartMap_b]
  cases hi : σ i <;> simp only [Bool.false_eq_true,↓reduceIte,Units.val_one,C_1,one_mul]
  rw [map_mul,mul_add,mul_one,mul_assoc]
lemma chartUnit_inv (σ : Fin n → Bool) :
    (chartUnit R n σ)⁻¹=∏ i,if σ i then (variableUnit R n i)⁻¹ else 1 := by
  rw [chartUnit,←Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases h : σ i <;> simp
lemma chartMap_product (σ : Fin n → Bool) :
    (ProductLinearChart.product R n σ).map (chartMap R n σ).toRingHom=
      C (↑((chartUnit R n σ)⁻¹) : Ring R n)*binaryForm R n := by
  unfold binaryForm
  rw [ProductLinearChart.product,Polynomial.map_prod]
  simp_rw [chartMap_factor]
  rw [Finset.prod_mul_distrib]
  have hunit : (∏ i,if σ i then (↑((variableUnit R n i)⁻¹) : Ring R n) else 1)=
      (↑((chartUnit R n σ)⁻¹) : Ring R n) := by
    rw [chartUnit_inv]
    rw [Units.coe_prod]
    apply Finset.prod_congr rfl
    intro i _
    cases h : σ i <;> rfl
  rw [←map_prod,hunit]
lemma chartMap_coefficient (σ : Fin n → Bool) (k : ℕ) :
    chartMap R n σ ((ProductLinearChart.product R n σ).coeff k)=
      (↑((chartUnit R n σ)⁻¹) : Ring R n)*(binaryForm R n).coeff k := by
  have h := congrArg (fun p : (Ring R n)[X] => p.coeff k) (chartMap_product R n σ)
  simpa only [Polynomial.coeff_map,Polynomial.coeff_C_mul,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using h


def uniformExponent (N : ℤ) : Exponent n := Finsupp.equivFunOnFinite.symm (fun _ => N)
lemma uniformExponent_apply (N : ℤ) (i : Fin n) : uniformExponent n N i=N := rfl
def naturalPart (e : Exponent n) : Fin n →₀ ℕ := e.mapRange Int.toNat (by rfl)
lemma naturalPart_lift (e : Exponent n) (h : ∀ i,0≤e i) :
    signedExponent n (fun _ => false) (naturalPart n e)=e := by
  ext i
  simp only [signedExponent_apply,Bool.false_eq_true,↓reduceIte,naturalPart,Finsupp.mapRange_apply,
    Int.toNat_of_nonneg (h i)]
def clearingBound (x : Ring R n) : ℕ :=
  x.coeff.support.sup (fun e => Finset.univ.sup (fun i : Fin n => (e i).natAbs))
lemma clearingBound_nonneg (x : Ring R n) (e : Exponent n) (he : e∈x.coeff.support) (i : Fin n) :
    0≤(uniformExponent n (clearingBound R n x)+e) i := by
  have hn : (e i).natAbs≤clearingBound R n x :=
    (Finset.le_sup (f:=fun i : Fin n => (e i).natAbs) (Finset.mem_univ i)).trans
      (Finset.le_sup (f:=fun e : Exponent n => Finset.univ.sup (fun i : Fin n => (e i).natAbs)) he)
  have hn' : |e i|≤(clearingBound R n x:ℤ) := by
    rw [←Int.natCast_natAbs];exact_mod_cast hn
  have hl := neg_le_abs (e i)
  simp only [Finsupp.add_apply,uniformExponent_apply]
  omega
 

def clearedPolynomial (x : Ring R n) : ProductLinearChart.Ring R n :=
  ∑ e∈x.coeff.support,MvPolynomial.monomial
    (naturalPart n (uniformExponent n (clearingBound R n x)+e)) (x.coeff e)
lemma clearing_identity (x : Ring R n) :
    chartMap R n (fun _ => false) (clearedPolynomial R n x)=
      (monomialUnit R n (uniformExponent n (clearingBound R n x)):Ring R n)*x := by
  rw [clearedPolynomial,map_sum]
  simp only [chartMap_monomial]
  calc
    _ = ∑ e∈x.coeff.support,single (uniformExponent n (clearingBound R n x)+e) (x.coeff e) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [naturalPart_lift n _ (clearingBound_nonneg R n x e he)]
    _ = single (uniformExponent n (clearingBound R n x)) (1:R)*
        (∑ e∈x.coeff.support,single e (x.coeff e)) := by
      rw [Finset.mul_sum]
      simp only [single_mul_single,one_mul]
    _ = _ := by
      change _ * x.coeff.sum single=_
      rw [AddMonoidAlgebra.sum_coeff_single]
      rfl
 

theorem chartMap_regular (p : ProductLinearChart.Ring R n) (hp : IsRegular p) :
    IsRegular (chartMap R n (fun _ => false) p) := by
  have hz (x : Ring R n) (hx : chartMap R n (fun _ => false) p*x=0) : x=0 := by
    let u := monomialUnit R n (uniformExponent n (clearingBound R n x))
    have hc : chartMap R n (fun _ => false) (p*clearedPolynomial R n x)=0 := by
      rw [map_mul,clearing_identity]
      change chartMap R n (fun _ => false) p*((u:Ring R n)*x)=0
      rw [mul_left_comm,hx,mul_zero]
    have hc' : p*clearedPolynomial R n x=0 :=
      (chartMap_injective R n (fun _ => false)) (hc.trans (map_zero _).symm)
    have hpoly : clearedPolynomial R n x=0 := hp.left (by simpa only [mul_zero] using hc')
    have heq : (u:Ring R n)*x=0 := by
      rw [←clearing_identity,hpoly,map_zero]
    exact u.isUnit.isRegular.left (by simpa only [mul_zero] using heq)
  rw [isRegular_iff_eq_zero_of_mul]
  exact ⟨hz,fun x hx => hz x (by simpa only [mul_comm] using hx)⟩
lemma binaryForm_coefficient_regular (k : Fin (n+1)) : IsRegular ((binaryForm R n).coeff k) := by
  have hf : chartUnit R n (fun _ => false)=1 := by simp [chartUnit]
  have hc := chartMap_regular R n ((ProductLinearChart.product R n (fun _ => false)).coeff k)
    (ProductLinearChart.coefficient_regular R n (fun _ => false) k)
  rwa [chartMap_coefficient,hf,inv_one,Units.val_one,one_mul] at hc
end Lech.ProductLaurent


namespace Lech.ProductSourceCover
open scoped BigOperators
universe u
abbrev Chart (n : ℕ) := Fin n → Bool
abbrev Exponent (n : ℕ) := Fin n →₀ ℤ
abbrev LaurentModule (R : Type u) [Zero R] (n : ℕ) := Exponent n →₀ R
variable (R : Type u) [CommRing R] (n : ℕ)
 

def allowed (m : Fin n → ℤ) (s : Finset (Chart n)) (e : Exponent n) : Prop :=
  ∀ i, ((∀ σ∈s,σ i=false) → 0≤e i) ∧ ((∀ σ∈s,σ i=true) → e i≤ m i)
def sections (m : Fin n → ℤ) (s : Finset (Chart n)) : Submodule R (LaurentModule R n) :=
  Finsupp.supported R R {e | allowed n m s e}
lemma allowed_mono (m : Fin n → ℤ) {s t : Finset (Chart n)} (hst : s⊆t) :
    ∀ e,allowed n m s e → allowed n m t e := by
  intro e he i
  exact ⟨fun h => (he i).1 (fun σ hs => h σ (hst hs)),fun h => (he i).2 (fun σ hs => h σ (hst hs))⟩
lemma sections_mono (m : Fin n → ℤ) : Monotone (sections R n m) := by
  intro s t hst
  exact Finsupp.supported_mono (allowed_mono n m hst)
 

def badVertex (m : Fin n → ℤ) (e : Exponent n) : Chart n := fun i => decide (m i<e i)
lemma badVertex_false (m : Fin n → ℤ) (e : Exponent n) (i : Fin n) (he : e i≤ m i) :
    badVertex n m e i=false := by simp [badVertex,not_lt_of_ge he]
lemma badVertex_true (m : Fin n → ℤ) (e : Exponent n) (i : Fin n) (he : m i<e i) :
    badVertex n m e i=true := by simp [badVertex,he]
lemma allowed_erase_bad (m : Fin n → ℤ) (hm : ∀ i,-1≤ m i) (s : Finset (Chart n))
    (e : Exponent n) (he : allowed n m (insert (badVertex n m e) s) e) : allowed n m s e := by
  intro i
  constructor
  · intro hs
    by_contra hneg
    have hv : badVertex n m e i=false := badVertex_false n m e i (by have:=hm i;omega)
    have hgood := (he i).1 (by intro σ hσ;rcases Finset.mem_insert.mp hσ with rfl|hσ;exact hv;exact hs σ hσ)
    exact hneg hgood
  · intro hs
    by_contra hneg
    have hv : badVertex n m e i=true := badVertex_true n m e i (by omega)
    have hgood := (he i).2 (by intro σ hσ;rcases Finset.mem_insert.mp hσ with rfl|hσ;exact hv;exact hs σ hσ)
    exact hneg hgood

def projector (m : Fin n → ℤ) (σ : Chart n) : LaurentModule R n →ₗ[R] LaurentModule R n where
  toFun x := x.filter (fun e => badVertex n m e=σ)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul
lemma projector_apply (m : Fin n → ℤ) (σ : Chart n) (x : LaurentModule R n) (e : Exponent n) :
    projector R n m σ x e=if badVertex n m e=σ then x e else 0 := Finsupp.filter_apply _ _ _
lemma projector_sum (m : Fin n → ℤ) (x : LaurentModule R n) : ∑ σ,projector R n m σ x=x := by
  ext e
  simp only [Finsupp.finsetSum_apply,projector_apply]
  rw [Finset.sum_eq_single (badVertex n m e)]
  · simp
  · intro σ _ hσ
    simp [Ne.symm hσ]
  · simp
lemma projector_mem (m : Fin n → ℤ) (hm : ∀ i,-1≤ m i) (s : Finset (Chart n))
    (σ : Chart n) (x : LaurentModule R n) (hx : x∈sections R n m (insert σ s)) :
    projector R n m σ x∈sections R n m s := by
  rw [sections,Finsupp.mem_supported] at hx ⊢
  intro e he
  have he' : projector R n m σ x e≠0 := Finsupp.mem_support_iff.mp he
  rw [projector_apply] at he'
  split_ifs at he' with hv
  · subst σ
    exact allowed_erase_bad n m hm s e (hx (Finsupp.mem_support_iff.mpr he'))
  · exact (he' rfl).elim
 

theorem augmented_acyclic (m : Fin n → ℤ) (hm : ∀ i,-1≤ m i) :
    (AlternatingCech.complex R (LaurentModule R n) (sections R n m) (sections_mono R n m)).Acyclic :=
  AlternatingCech.projection_complex_acyclic R (LaurentModule R n) (sections R n m)
    (sections_mono R n m) (projector R n m) (projector_sum R n m) (projector_mem R n m hm)
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
local instance endpointDecEq : DecidableEq (Chart n) := LinearOrder.toDecidableEq
def endpointVertex (j : Fin n) (b : Bool) (σ : Chart n) : Chart n := Function.update σ j b
omit [LinearOrder (Chart n)] in
lemma endpointVertex_idem (j : Fin n) (b : Bool) (σ : Chart n) :
    endpointVertex n j b (endpointVertex n j b σ)=endpointVertex n j b σ := by
  simp only [endpointVertex,Function.update_idem]
def endpointProjector (j : Fin n) (b : Bool) : LaurentModule R n →ₗ[R] LaurentModule R n where
  toFun x := x.filter (fun e => decide (0≤e j)=b)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul
omit [LinearOrder (Chart n)] in
lemma endpointProjector_apply (j : Fin n) (b : Bool) (x : LaurentModule R n) (e : Exponent n) :
    endpointProjector R n j b x e=if decide (0≤e j)=b then x e else 0 := Finsupp.filter_apply _ _ _
omit [LinearOrder (Chart n)] in
lemma endpointProjector_sum (j : Fin n) (x : LaurentModule R n) : ∑ b,endpointProjector R n j b x=x := by
  ext e
  simp only [Finsupp.finsetSum_apply,endpointProjector_apply]
  rw [Finset.sum_eq_single (decide (0≤e j))]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
lemma endpoint_allowed_carrier (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1)
    (s : Finset (Chart n)) (b : Bool) (e : Exponent n) (hb : decide (0≤e j)=b)
    (he : allowed n m (s∪s.image (endpointVertex n j b)) e) : allowed n m s e := by
  intro i
  by_cases hi : i=j
  · subst i
    cases b with
    | false =>
      have hneg : e j<0 := by have h := of_decide_eq_false hb; omega
      refine ⟨?_,fun _ => by omega⟩
      intro hs
      exact (he j).1 (by
        intro σ hσ
        rcases Finset.mem_union.mp hσ with hσ|hσ
        · exact hs σ hσ
        · obtain ⟨ρ,_,rfl⟩ := Finset.mem_image.mp hσ
          simp [endpointVertex])
    | true =>
      have hpos : 0≤e j := of_decide_eq_true hb
      refine ⟨fun _ => hpos,?_⟩
      intro hs
      exact (he j).2 (by
        intro σ hσ
        rcases Finset.mem_union.mp hσ with hσ|hσ
        · exact hs σ hσ
        · obtain ⟨ρ,_,rfl⟩ := Finset.mem_image.mp hσ
          simp [endpointVertex])
  · constructor
    · intro hs
      apply (he i).1
      intro σ hσ
      rcases Finset.mem_union.mp hσ with hσ|hσ
      · exact hs σ hσ
      · obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp hσ
        simpa only [endpointVertex,Function.update_of_ne hi] using hs ρ hρ
    · intro hs
      apply (he i).2
      intro σ hσ
      rcases Finset.mem_union.mp hσ with hσ|hσ
      · exact hs σ hσ
      · obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp hσ
        simpa only [endpointVertex,Function.update_of_ne hi] using hs ρ hρ
lemma endpointProjector_carrier (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1)
    (s : Finset (Chart n)) (b : Bool) (x : LaurentModule R n)
    (hx : x∈sections R n m (s∪s.image (endpointVertex n j b))) :
    endpointProjector R n j b x∈sections R n m s := by
  rw [sections,Finsupp.mem_supported] at hx ⊢
  intro e he
  have he' : endpointProjector R n j b x e≠0 := Finsupp.mem_support_iff.mp he
  rw [endpointProjector_apply] at he'
  split_ifs at he' with hb
  · exact endpoint_allowed_carrier n m j hj s b e hb (hx (Finsupp.mem_support_iff.mpr he'))
  · exact (he' rfl).elim
lemma endpointProjector_zero (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1)
    (s : Finset (Chart n)) (b : Bool) (x : LaurentModule R n)
    (hx : x∈sections R n m (s.image (endpointVertex n j b))) : endpointProjector R n j b x=0 := by
  rw [sections,Finsupp.mem_supported] at hx
  ext e
  rw [endpointProjector_apply,Finsupp.zero_apply]
  split_ifs with hb
  · by_contra he
    have ha := hx (Finsupp.mem_support_iff.mpr he) j
    cases b with
    | false =>
      have hneg : e j<0 := by have h := of_decide_eq_false hb; omega
      have hpos := ha.1 (by
        intro σ hσ
        obtain ⟨ρ,_,rfl⟩ := Finset.mem_image.mp hσ
        simp [endpointVertex])
      omega
    | true =>
      have hpos : 0≤e j := of_decide_eq_true hb
      have hneg := ha.2 (by
        intro σ hσ
        obtain ⟨ρ,_,rfl⟩ := Finset.mem_image.mp hσ
        simp [endpointVertex])
      omega
  · rfl
 

theorem endpoint_acyclic (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1) :
    (AlternatingCech.complex R (LaurentModule R n) (sections R n m) (sections_mono R n m)).Acyclic := by
  have hdec : endpointDecEq n = Classical.decEq (Chart n) := Subsingleton.elim _ _
  have hcarrier := endpointProjector_carrier R n m j hj
  have hzero := endpointProjector_zero R n m j hj
  rw [hdec] at hcarrier hzero ⊢
  exact AlternatingCech.projection_prism_acyclic R (LaurentModule R n) (sections R n m)
    (sections_mono R n m) (endpointProjector R n j) (endpointProjector_sum R n j)
    (endpointVertex n j) (endpointVertex_idem n j) hcarrier hzero
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
 
def outlier (m : Fin n → ℤ) (e : Exponent n) (i : Fin n) : Prop :=
  (0 ≤ e i ∧ m i < e i) ∨ (e i < 0 ∧ e i ≤ m i)
def chosenOutlier (m : Fin n → ℤ) (e : Exponent n) : Option (Fin n × Bool) := by
  classical
  exact if h : ∃ i,outlier n m e i then some (Classical.choose h,decide (0 ≤ e (Classical.choose h))) else none
lemma chosenOutlier_spec (m : Fin n → ℤ) (e : Exponent n) (j : Fin n) (b : Bool)
    (h : chosenOutlier n m e=some (j,b)) : outlier n m e j ∧ decide (0 ≤ e j)=b := by
  classical
  unfold chosenOutlier at h
  split_ifs at h with ho
  · have he := Option.some.inj h
    have hj : Classical.choose ho = j := congrArg Prod.fst he
    have hb : decide (0 ≤ e (Classical.choose ho)) = b := congrArg Prod.snd he
    rw [←hj]
    exact ⟨Classical.choose_spec ho,hb⟩
lemma chosenOutlier_none (m : Fin n → ℤ) (e : Exponent n) :
    chosenOutlier n m e=none ↔ ∀ i,¬outlier n m e i := by
  classical
  simp only [chosenOutlier]
  split_ifs with ho
  · simp only [false_iff,not_forall,not_not]
    exact ho
  · simp only [true_iff]
    exact not_exists.mp ho
 

def central (m : Fin n → ℤ) (e : Exponent n) : Prop :=
  ∀ i,min (m i+1) 0 ≤ e i ∧ e i ≤ max (m i) (-1)
lemma central_iff (m : Fin n → ℤ) (e : Exponent n) :
    central n m e ↔ chosenOutlier n m e=none := by
  rw [chosenOutlier_none]
  change (∀ i,min (m i+1) 0 ≤ e i ∧ e i ≤ max (m i) (-1)) ↔
    ∀ i,¬((0 ≤ e i ∧m i < e i)∨(e i < 0 ∧e i ≤ m i))
  apply forall_congr'
  intro i
  constructor  <;>  intro h
  · by_cases hm : 0 ≤ m i
    · rw [min_eq_right (by omega),max_eq_left (by omega)] at h
      omega
    · rw [min_eq_left (by omega),max_eq_right (by omega)] at h
      omega
  · by_cases hm : 0 ≤ m i
    · rw [min_eq_right (by omega),max_eq_left (by omega)]
      omega
    · rw [min_eq_left (by omega),max_eq_right (by omega)]
      omega
def centralProjector (m : Fin n → ℤ) : LaurentModule R n →ₗ[R] LaurentModule R n where
  toFun x := x.filter (fun e => chosenOutlier n m e=none)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul
def outlierProjector (m : Fin n → ℤ) (k : Fin n × Bool) : LaurentModule R n →ₗ[R] LaurentModule R n where
  toFun x := x.filter (fun e => chosenOutlier n m e=some k)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul
lemma centralProjector_apply (m : Fin n → ℤ) (x : LaurentModule R n) (e : Exponent n) :
    centralProjector R n m x e=if chosenOutlier n m e=none then x e else 0 := Finsupp.filter_apply _ _ _
lemma outlierProjector_apply (m : Fin n → ℤ) (k : Fin n × Bool) (x : LaurentModule R n) (e : Exponent n) :
    outlierProjector R n m k x e=if chosenOutlier n m e=some k then x e else 0 := Finsupp.filter_apply _ _ _
lemma outlierProjector_sum (m : Fin n → ℤ) (x : LaurentModule R n) :
    ∑ k,outlierProjector R n m k x=x-centralProjector R n m x := by
  ext e
  simp only [Finsupp.finsetSum_apply,Finsupp.sub_apply,outlierProjector_apply,centralProjector_apply]
  cases he : chosenOutlier n m e with
  | none => simp
  | some k =>
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · simp
lemma centralProjector_mem (m : Fin n → ℤ) (s : Finset (Chart n)) (x : LaurentModule R n)
    (hx : x∈sections R n m s) : centralProjector R n m x∈sections R n m s := by
  rw [sections,Finsupp.mem_supported] at hx ⊢
  intro e he
  have he' : centralProjector R n m x e ≠ 0 := Finsupp.mem_support_iff.mp he
  rw [centralProjector_apply] at he'
  split_ifs at he' with h
  · exact hx (Finsupp.mem_support_iff.mpr he')
  · exact (he' rfl).elim
lemma centralProjector_idem (m : Fin n → ℤ) (x : LaurentModule R n) :
    centralProjector R n m (centralProjector R n m x)=centralProjector R n m x := by
  ext e
  simp only [centralProjector_apply]
  split_ifs <;> rfl
variable [LinearOrder (Chart n)]
local instance centralDecEq : DecidableEq (Chart n) := LinearOrder.toDecidableEq
lemma outlier_allowed_carrier (m : Fin n → ℤ) (s : Finset (Chart n)) (k : Fin n × Bool)
    (e : Exponent n) (hk : chosenOutlier n m e=some k)
    (he : allowed n m (s∪s.image (endpointVertex n k.1 k.2)) e) : allowed n m s e := by
  obtain ⟨ho,hb⟩ := chosenOutlier_spec n m e k.1 k.2 hk
  intro i
  by_cases hi : i=k.1
  · subst i
    cases hbit : k.2 with
    | false =>
      have hneg : e k.1 < 0 := by rw [hbit] at hb;have h := of_decide_eq_false hb;omega
      have hle : e k.1 ≤ m k.1 := by unfold outlier at ho;omega
      refine ⟨?_,fun _ => hle⟩
      intro hs
      exact (he k.1).1 (by
        intro σ hσ
        rcases Finset.mem_union.mp hσ with hσ|hσ
        · exact hs σ hσ
        · obtain ⟨ρ,_,rfl⟩ := Finset.mem_image.mp hσ
          simp [endpointVertex,hbit])
    | true =>
      have hpos : 0 ≤ e k.1 := by rw [hbit] at hb;exact of_decide_eq_true hb
      refine ⟨fun _ => hpos,?_⟩
      intro hs
      exact (he k.1).2 (by
        intro σ hσ
        rcases Finset.mem_union.mp hσ with hσ|hσ
        · exact hs σ hσ
        · obtain ⟨ρ,_,rfl⟩ := Finset.mem_image.mp hσ
          simp [endpointVertex,hbit])
  · constructor
    · intro hs
      apply (he i).1
      intro σ hσ
      rcases Finset.mem_union.mp hσ with hσ|hσ
      · exact hs σ hσ
      · obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp hσ
        simpa only [endpointVertex,Function.update_of_ne hi] using hs ρ hρ
    · intro hs
      apply (he i).2
      intro σ hσ
      rcases Finset.mem_union.mp hσ with hσ|hσ
      · exact hs σ hσ
      · obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp hσ
        simpa only [endpointVertex,Function.update_of_ne hi] using hs ρ hρ
lemma outlierProjector_carrier (m : Fin n → ℤ) (s : Finset (Chart n)) (k : Fin n × Bool)
    (x : LaurentModule R n) (hx : x∈sections R n m (s∪s.image (endpointVertex n k.1 k.2))) :
    outlierProjector R n m k x∈sections R n m s := by
  rw [sections,Finsupp.mem_supported] at hx ⊢
  intro e he
  have he' : outlierProjector R n m k x e≠0 := Finsupp.mem_support_iff.mp he
  rw [outlierProjector_apply] at he'
  split_ifs at he' with hk
  · exact outlier_allowed_carrier n m s k e hk (hx (Finsupp.mem_support_iff.mpr he'))
  · exact (he' rfl).elim
lemma outlierProjector_zero (m : Fin n → ℤ) (s : Finset (Chart n)) (k : Fin n × Bool)
    (x : LaurentModule R n) (hx : x∈sections R n m (s.image (endpointVertex n k.1 k.2))) :
    outlierProjector R n m k x=0 := by
  rw [sections,Finsupp.mem_supported] at hx
  ext e
  rw [outlierProjector_apply,Finsupp.zero_apply]
  split_ifs with hk
  · by_contra he
    have ha := hx (Finsupp.mem_support_iff.mpr he) k.1
    obtain ⟨ho,hb⟩ := chosenOutlier_spec n m e k.1 k.2 hk
    cases hbit : k.2 with
    | false =>
      have hneg : e k.1 < 0 := by rw [hbit] at hb;have h := of_decide_eq_false hb;omega
      have hpos := ha.1 (by
        intro σ hσ
        obtain ⟨ρ,_,rfl⟩ := Finset.mem_image.mp hσ
        simp [endpointVertex,hbit])
      omega
    | true =>
      have hpos : 0 ≤ e k.1 := by rw [hbit] at hb;exact of_decide_eq_true hb
      have hgt : m k.1 < e k.1 := by unfold outlier at ho;omega
      have hneg := ha.2 (by
        intro σ hσ
        obtain ⟨ρ,_,rfl⟩ := Finset.mem_image.mp hσ
        simp [endpointVertex,hbit])
      omega
  · rfl
end Lech.ProductSourceCover
end

end OAI
