import Mathlib
import OAI.RingTheory.Multiplicity.PrincipalCoverRegularRegularMap

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
namespace Lech.AlternatingCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
variable {κ : Type} [Fintype κ]
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
variable (Q : M →ₗ[R] M) (P : κ → M →ₗ[R] M) (hP : ∀ x,∑ j,P j x=x-Q x)
  (τ : κ → ι → ι) (hτ : ∀ j i,τ j (τ j i)=τ j i)
  (hcarrier : ∀ s j x,x∈F (s∪s.image (τ j)) → P j x∈F s)
  (hzero : ∀ (s : Finset ι) j x,x∈F (s.image (τ j)) → P j x=0)
def prismPrimitive (p : ℕ) : cochains R M F (p+1) →ₗ[R] cochains R M F p :=
  ((∑ j,(post R M p (P j)).comp (prism R M (τ j) p)).comp (cochains R M F (p+1)).subtype).codRestrict
    (cochains R M F p) (fun f => by
      rcases f with ⟨value,hvalue⟩
      simp only [LinearMap.comp_apply,LinearMap.sum_apply,Submodule.subtype_apply]
      have hdec : (LinearOrder.toDecidableEq : DecidableEq ι) = Classical.decEq ι :=
        Subsingleton.elim _ _
      rw [hdec] at hcarrier hvalue ⊢
      exact Submodule.sum_mem _ (fun j _ => post_prism_mem R M (τ j) (hτ j) (P j) F hF
        (fun s x hx => hcarrier s j x hx) p value hvalue))
lemma prismPrimitive_apply (p : ℕ) (f : cochains R M F (p+1)) :
    (prismPrimitive R M F hF P τ hτ hcarrier p f).val=
      ∑ j,post R M p (P j) (prism R M (τ j) p f.val) := by
  simp only [prismPrimitive,LinearMap.codRestrict_apply,LinearMap.comp_apply,LinearMap.sum_apply,Submodule.subtype_apply]
include hP hzero in
 

lemma prism_reduction_identity (p : ℕ) (f : cochains R M F (p+1)) :
    (prismPrimitive R M F hF P τ hτ hcarrier (p+1) (differential R M F hF (p+1) f)).val+
      delta R M p (prismPrimitive R M F hF P τ hτ hcarrier p f).val=
        f.val-post R M (p+1) Q f.val := by
  rw [prismPrimitive_apply,prismPrimitive_apply,map_sum]
  change (∑ j,post R M (p+1) (P j) (prism R M (τ j) (p+1) (delta R M (p+1) f.val)))+
    (∑ j,delta R M p (post R M p (P j) (prism R M (τ j) p f.val)))=_
  simp only [delta_post]
  rw [←Finset.sum_add_distrib]
  have hj (j : κ) :
      post R M (p+1) (P j) (prism R M (τ j) (p+1) (delta R M (p+1) f.val))+
        post R M (p+1) (P j) (delta R M p (prism R M (τ j) p f.val))=
        post R M (p+1) (P j) f.val := by
    rcases f with ⟨value,hvalue⟩
    have hdec : (LinearOrder.toDecidableEq : DecidableEq ι) = Classical.decEq ι :=
      Subsingleton.elim _ _
    rw [hdec] at hzero hvalue
    rw [←map_add,prism_identity,map_sub,post_pullback_zero R M (τ j) (P j) F
      (fun s x hx => hzero s j x hx) (p+1) value hvalue,sub_zero]
  simp only [hj]
  apply evaluation_injective R M (p+1)
  ext a
  simp only [map_sum,Finset.sum_apply,evaluation_post,map_sub,Pi.sub_apply]
  exact hP _
include hP hzero in
lemma prism_reduction_cycle (p : ℕ) (f : cochains R M F (p+1))
    (hf : delta R M (p+1) f.val=0) :
    delta R M p (prismPrimitive R M F hF P τ hτ hcarrier p f).val =
      f.val-post R M (p+1) Q f.val := by
  have hd : differential R M F hF (p+1) f=0 := Subtype.ext hf
  have h := prism_reduction_identity R M F hF Q P hP τ hτ hcarrier hzero p f
  rwa [hd,map_zero,Submodule.coe_zero,zero_add] at h
end Lech.AlternatingCech


namespace Lech.ProductSourceCover
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
abbrev CentralIndex (m : Fin n → ℤ) := {e : Exponent n // central n m e}
def centralIndexEquiv (m : Fin n → ℤ) : CentralIndex n m ≃
    (∀ i : Fin n,Set.Icc (min (m i+1) 0) (max (m i) (-1))) where
  toFun e i := ⟨e.val i,e.property i⟩
  invFun e := ⟨Finsupp.equivFunOnFinite.symm (fun i => (e i).val),fun i => (e i).property⟩
  left_inv e := by apply Subtype.ext;ext i;rfl
  right_inv e := by funext i;apply Subtype.ext;rfl
instance centralIndexFintype (m : Fin n → ℤ) : Fintype (CentralIndex n m) :=
  Fintype.ofEquiv _ (centralIndexEquiv n m).symm
lemma centralIndex_card (m : Fin n → ℤ) :
    Fintype.card (CentralIndex n m)=∏ i,((m i+1).natAbs) := by
  rw [Fintype.card_congr (centralIndexEquiv n m),Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_ofFinset]
  simp only [Int.card_Icc]
  by_cases hm : -1 ≤ m i
  · rw [max_eq_left (by omega),min_eq_right (by omega)]
    omega
  · rw [max_eq_right (by omega),min_eq_left (by omega)]
    omega
 
def centralModule (m : Fin n → ℤ) : Submodule R (LaurentModule R n) :=
  Finsupp.supported R R {e | central n m e}
def centralBasis (m : Fin n → ℤ) : Module.Basis (CentralIndex n m) R (centralModule R n m) :=
  Finsupp.basisSingleOne.map (Finsupp.supportedEquivFinsupp {e | central n m e}).symm
instance centralModule_finite (m : Fin n → ℤ) : Module.Finite R (centralModule R n m) :=
  Module.Finite.of_basis (centralBasis R n m)
instance centralModule_free (m : Fin n → ℤ) : Module.Free R (centralModule R n m) :=
  Module.Free.of_basis (centralBasis R n m)
lemma centralModule_finrank [Nontrivial R] (m : Fin n → ℤ) :
    Module.finrank R (centralModule R n m)=∏ i,(m i+1).natAbs := by
  rw [Module.finrank_eq_card_basis (centralBasis R n m),centralIndex_card]
lemma centralProjector_mem_central (m : Fin n → ℤ) (x : LaurentModule R n) :
    centralProjector R n m x∈centralModule R n m := by
  rw [centralModule,Finsupp.mem_supported]
  intro e he
  have he' : centralProjector R n m x e ≠ 0 := Finsupp.mem_support_iff.mp he
  rw [centralProjector_apply] at he'
  split_ifs at he' with h
  · exact (central_iff n m e).mpr h
  · exact (he' rfl).elim
variable [LinearOrder (Chart n)]
local instance reductionDecEq : DecidableEq (Chart n) := LinearOrder.toDecidableEq
open AlternatingCech
 
def centralCochain (m : Fin n → ℤ) (p : ℕ) :
    cochains R (LaurentModule R n) (sections R n m) p →ₗ[R]
      cochains R (LaurentModule R n) (sections R n m) p :=
  ((post R (LaurentModule R n) p (centralProjector R n m)).comp
    (cochains R (LaurentModule R n) (sections R n m) p).subtype).codRestrict _ (fun f => by
      intro a
      change evaluation R _ p (post R _ p (centralProjector R n m) f.val) a∈_
      rw [evaluation_post]
      exact centralProjector_mem R n m _ _ (f.property a))
lemma centralCochain_val (m : Fin n → ℤ) (p : ℕ)
    (f : cochains R (LaurentModule R n) (sections R n m) p) :
    (centralCochain R n m p f).val=post R _ p (centralProjector R n m) f.val := rfl
 

theorem central_cycle_representative (m : Fin n → ℤ) (p : ℕ)
    (f : cochains R (LaurentModule R n) (sections R n m) (p+1))
    (hf : delta R _ (p+1) f.val=0) :
    ∃ g : cochains R (LaurentModule R n) (sections R n m) (p+1),
      delta R _ (p+1) g.val=0 ∧
      (∀ a,evaluation R _ (p+1) g.val a∈centralModule R n m) ∧
      ∃ b : cochains R (LaurentModule R n) (sections R n m) p,
        delta R _ p b.val=f.val-g.val := by
  refine ⟨centralCochain R n m (p+1) f,?_,?_,?_⟩
  · rw [centralCochain_val,delta_post,hf,map_zero]
  · intro a
    rw [centralCochain_val,evaluation_post]
    exact centralProjector_mem_central R n m _
  · refine ⟨prismPrimitive R (LaurentModule R n) (sections R n m) (sections_mono R n m)
      (outlierProjector R n m) (fun k => endpointVertex n k.1 k.2)
      (fun k => endpointVertex_idem n k.1 k.2) (outlierProjector_carrier R n m) p f,?_⟩
    exact prism_reduction_cycle R (LaurentModule R n) (sections R n m) (sections_mono R n m)
      (centralProjector R n m) (outlierProjector R n m) (outlierProjector_sum R n m)
      (fun k => endpointVertex n k.1 k.2) (fun k => endpointVertex_idem n k.1 k.2)
      (outlierProjector_carrier R n m) (outlierProjector_zero R n m) p f hf
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
 

def spanning (m : Fin n → ℤ) (s : Finset (Chart n)) : Prop :=
  ∀ i,m i < 0 → (∃ σ∈s,σ i=true) ∧ (∃ σ∈s,σ i=false)
lemma central_allowed_iff (m : Fin n → ℤ) (s : Finset (Chart n)) (e : Exponent n)
    (he : central n m e) : allowed n m s e ↔ spanning n m s := by
  classical
  constructor
  · intro ha i hi
    have h := he i
    rw [min_eq_left (by omega),max_eq_right (by omega)] at h
    constructor
    · by_contra ht
      have hh : ∀ σ∈s,σ i=false := by
        intro σ hσ
        have hn : σ i≠true := fun hh => ht ⟨σ,hσ,hh⟩
        exact Bool.eq_false_iff.mpr hn
      have hp := (ha i).1 hh
      omega
    · by_contra ht
      have hh : ∀ σ∈s,σ i=true := by
        intro σ hσ
        have hn : σ i≠false := fun hh => ht ⟨σ,hσ,hh⟩
        cases hσi : σ i <;> simp_all
      have hp := (ha i).2 hh
      omega
  · intro hs i
    by_cases hi : m i < 0
    · obtain ⟨⟨σ,hσ,hσ'⟩,⟨τ,hτ,hτ'⟩⟩ := hs i hi
      constructor
      · intro ha
        have := ha σ hσ
        simp only [hσ',Bool.true_eq_false] at this
      · intro ha
        have := ha τ hτ
        simp only [hτ',Bool.false_eq_true] at this
    · have h := he i
      rw [min_eq_right (by omega),max_eq_left (by omega)] at h
      exact ⟨fun _ => h.1,fun _ => h.2⟩
def centralSections (m : Fin n → ℤ) (s : Finset (Chart n)) : Submodule R (LaurentModule R n) :=
  sections R n m s ⊓ centralModule R n m
lemma centralSections_mono (m : Fin n → ℤ) : Monotone (centralSections R n m) :=
  fun _ _ h => inf_le_inf_right _ (sections_mono R n m h)
 

lemma centralSections_eq (m : Fin n → ℤ) (s : Finset (Chart n)) :
    centralSections R n m s=if spanning n m s then centralModule R n m else ⊥ := by
  classical
  by_cases hs : spanning n m s
  · rw [ite_eq_left hs]
    apply le_antisymm inf_le_right
    intro x hx
    refine ⟨?_,hx⟩
    change x∈Finsupp.supported R R {e | allowed n m s e}
    rw [Finsupp.mem_supported]
    rw [centralModule,Finsupp.mem_supported] at hx
    intro e he
    exact (central_allowed_iff n m s e (hx he)).mpr hs
  · rw [ite_eq_right hs]
    apply le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hx,hc⟩ := hx
    change x∈Finsupp.supported R R {e | allowed n m s e} at hx
    change x∈Finsupp.supported R R {e | central n m e} at hc
    rw [Finsupp.mem_supported] at hx hc
    change x=0
    ext e
    by_contra he
    have he' : e∈x.support := Finsupp.mem_support_iff.mpr he
    exact hs ((central_allowed_iff n m s e (hc he')).mp (hx he'))
lemma centralProjector_eq_self (m : Fin n → ℤ) (x : LaurentModule R n)
    (hx : x∈centralModule R n m) : centralProjector R n m x=x := by
  rw [centralModule,Finsupp.mem_supported] at hx
  ext e
  rw [centralProjector_apply]
  split_ifs with he
  · rfl
  · symm
    by_contra hh
    exact he ((central_iff n m e).mp (hx (Finsupp.mem_support_iff.mpr hh)))
variable [LinearOrder (Chart n)]
local instance relativeDecEq : DecidableEq (Chart n) := LinearOrder.toDecidableEq
open AlternatingCech
 

theorem central_exact_iff (m : Fin n → ℤ) (p : ℕ) :
    (∀ (f : cochains R (LaurentModule R n) (sections R n m) (p+1)),
      delta R _ (p+1) f.val=0 → ∃ b : cochains R (LaurentModule R n) (sections R n m) p,
        delta R _ p b.val=f.val) ↔
    (∀ (f : cochains R (LaurentModule R n) (centralSections R n m) (p+1)),
      delta R _ (p+1) f.val=0 → ∃ b : cochains R (LaurentModule R n) (centralSections R n m) p,
        delta R _ p b.val=f.val) := by
  constructor
  · intro h f hf
    let f' : cochains R (LaurentModule R n) (sections R n m) (p+1) :=
      ⟨f.val,fun a => (f.property a).1⟩
    obtain ⟨b,hb⟩ := h f' hf
    refine ⟨⟨(centralCochain R n m p b).val,?_⟩,?_⟩
    · intro a
      exact ⟨(centralCochain R n m p b).property a,by
        rw [centralCochain_val,evaluation_post]
        exact centralProjector_mem_central R n m _⟩
    · rw [centralCochain_val,delta_post,hb]
      apply evaluation_injective R _ (p+1)
      apply funext
      intro a
      rw [evaluation_post]
      exact centralProjector_eq_self R n m _ ((f.property a).2)
  · intro h f hf
    obtain ⟨g,hg,hgc,b,hb⟩ := central_cycle_representative R n m p f hf
    let g' : cochains R (LaurentModule R n) (centralSections R n m) (p+1) :=
      ⟨g.val,fun a => ⟨g.property a,hgc a⟩⟩
    obtain ⟨c,hc⟩ := h g' hg
    refine ⟨b+⟨c.val,fun a => (c.property a).1⟩,?_⟩
    change delta R _ p (b.val+c.val)=f.val
    rw [map_add,hb,hc]
    change f.val-g.val+g.val=f.val
    abel
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def exponentCons (k : ℤ) (e : Exponent n) : Exponent (n+1) :=
  Finsupp.equivFunOnFinite.symm (Fin.cons k (fun i => e i))
@[simp] lemma exponentCons_zero (k : ℤ) (e : Exponent n) : exponentCons n k e 0=k := rfl
@[simp] lemma exponentCons_succ (k : ℤ) (e : Exponent n) (i : Fin n) :
    exponentCons n k e i.succ=e i := rfl
lemma exponentCons_injective (k : ℤ) : Function.Injective (exponentCons n k) := by
  intro e f h
  ext i
  exact congrArg (fun z => z i.succ) h
def exponentTail (e : Exponent (n+1)) : Exponent n :=
  Finsupp.equivFunOnFinite.symm (fun i => e i.succ)
@[simp] lemma exponentTail_apply (e : Exponent (n+1)) (i : Fin n) : exponentTail n e i=e i.succ := rfl
lemma exponentCons_tail (e : Exponent (n+1)) : exponentCons n (e 0) (exponentTail n e)=e := by
  ext i
  exact Fin.cases rfl (fun _ => rfl) i
 

def exponentSlice (k : ℤ) : LaurentModule R (n+1) →ₗ[R] LaurentModule R n :=
  Finsupp.lcomapDomain (exponentCons n k) (exponentCons_injective n k)
def exponentInsert (k : ℤ) : LaurentModule R n →ₗ[R] LaurentModule R (n+1) :=
  Finsupp.lmapDomain R R (exponentCons n k)
@[simp] lemma exponentSlice_apply (k : ℤ) (x : LaurentModule R (n+1)) (e : Exponent n) :
    exponentSlice R n k x e=x (exponentCons n k e) := rfl
lemma exponentSlice_insert (k : ℤ) (x : LaurentModule R n) :
    exponentSlice R n k (exponentInsert R n k x)=x := by
  ext e
  exact Finsupp.mapDomain_apply_of_injective (exponentCons_injective n k) x e
lemma exponentInsert_support (k : ℤ) (x : LaurentModule R n) (e : Exponent (n+1))
    (he : e∈(exponentInsert R n k x).support) : ∃ f∈x.support,exponentCons n k f=e := by
  have h := Finsupp.mapDomain_support (f:=exponentCons n k) (s:=x)
  exact Finset.mem_image.mp (h he)
def trueFace (σ : Chart n) : Chart (n+1) := Fin.cons true σ
lemma trueFace_injective : Function.Injective (trueFace n) := by
  intro σ τ h
  funext i
  exact congrArg (fun z => z i.succ) h
@[simp] lemma trueFace_zero (σ : Chart n) : trueFace n σ 0=true := rfl
@[simp] lemma trueFace_succ (σ : Chart n) (i : Fin n) : trueFace n σ i.succ=σ i := rfl
lemma exponentSlice_mem (k : ℤ) (m : Fin n → ℤ) (s : Finset (Chart n))
    (x : LaurentModule R (n+1))
    (hx : x∈sections R (n+1) (Fin.cons k m) (s.image (trueFace n))) :
    exponentSlice R n k x∈sections R n m s := by
  rw [sections,Finsupp.mem_supported] at hx ⊢
  intro e he i
  have he' : exponentCons n k e∈x.support := Finsupp.mem_support_iff.mpr (by simpa only [exponentSlice_apply] using Finsupp.mem_support_iff.mp he)
  have ha := hx he' i.succ
  constructor
  · intro hs
    apply ha.1
    intro σ hσ
    obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hσ
    exact hs τ hτ
  · intro hs
    apply ha.2
    intro σ hσ
    obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hσ
    exact hs τ hτ
lemma exponentInsert_mem (k : ℤ) (m : Fin n → ℤ) (s : Finset (Chart (n+1)))
    (hs : s.Nonempty) (ht : ∀ σ∈s,σ 0=true) (x : LaurentModule R n)
    (hx : x∈sections R n m (s.image Fin.tail)) :
    exponentInsert R n k x∈sections R (n+1) (Fin.cons k m) s := by
  rw [sections,Finsupp.mem_supported] at hx ⊢
  intro e he
  obtain ⟨f,hf,rfl⟩ := exponentInsert_support R n k x e he
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ⟨?_,fun _ => le_refl k⟩
    intro hh
    obtain ⟨σ,hσ⟩ := hs
    have h0 := hh σ hσ
    rw [ht σ hσ] at h0
    cases h0
  · have ha := hx hf j
    constructor
    · intro hh
      apply ha.1
      intro σ hσ
      obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hσ
      exact hh τ hτ
    · intro hh
      apply ha.2
      intro σ hσ
      obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hσ
      exact hh τ hτ
 

lemma neighbor_mem_iff (k : ℤ) (m : Fin n → ℤ) (s : Finset (Chart (n+1)))
    (x : LaurentModule R (n+1)) (hx : x∈sections R (n+1) (Fin.cons k m) s) :
    x∈sections R (n+1) (Fin.cons (k-1) m) s ↔
      ((∀ σ∈s,σ 0=true) → exponentSlice R n k x=0) := by
  rw [sections,Finsupp.mem_supported] at hx ⊢
  constructor
  · intro hl ht
    ext e
    change x (exponentCons n k e)=0
    by_contra he
    have ha := hl (Finsupp.mem_support_iff.mpr he) 0
    have hh := ha.2 ht
    simp only [Fin.cons_zero,exponentCons_zero] at hh
    omega
  · intro hl e he i
    refine Fin.cases ?_ (fun j => hx he j.succ) i
    refine ⟨(hx he 0).1,?_⟩
    intro ht
    have ha := (hx he 0).2 ht
    change e 0 ≤ k at ha
    by_contra hneg
    have hek : e 0=k := by change ¬e 0 ≤ k-1 at hneg;omega
    have hh := congrArg (fun z => z (exponentTail n e)) (hl ht)
    simp only [exponentSlice_apply,Finsupp.zero_apply,←hek,exponentCons_tail] at hh
    exact Finsupp.mem_support_iff.mp he hh
lemma neighbor_sections_le (k : ℤ) (m : Fin n → ℤ) (s : Finset (Chart (n+1))) :
    sections R (n+1) (Fin.cons (k-1) m) s ≤ sections R (n+1) (Fin.cons k m) s := by
  intro x hx
  rw [sections,Finsupp.mem_supported] at hx ⊢
  intro e he i
  refine Fin.cases ?_ (fun j => hx he j.succ) i
  exact ⟨(hx he 0).1,fun ht => le_trans ((hx he 0).2 ht) (by simp)⟩
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AlternatingCech
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def faceVertexMap : (Chart n → R) →ₗ[R] (Chart (n+1) → R) :=
  (basis R).constr R (fun σ => basis R (trueFace n σ))
lemma faceVertexMap_basis (σ : Chart n) : faceVertexMap R n (basis R σ)=basis R (trueFace n σ) := by
  simp [faceVertexMap]
def faceProjection : (Chart (n+1) → R) →ₗ[R] (Chart n → R) :=
  (basis R).constr R (fun σ => if σ 0=true then basis R (Fin.tail σ) else 0)
lemma faceProjection_basis (σ : Chart (n+1)) :
    faceProjection R n (basis R σ)=if σ 0=true then basis R (Fin.tail σ) else 0 := by
  simp only [faceProjection,Module.Basis.constr_basis]
def faceSlice (k : ℤ) (p : ℕ) : Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p →ₗ[R]
    Alt R (LaurentModule R n) (ι:=Chart n) p where
  toFun f := (exponentSlice R n k).compAlternatingMap (f.compLinearMap (faceVertexMap R n))
  map_add' f g := by apply AlternatingMap.ext;intro v;exact map_add (exponentSlice R n k) _ _
  map_smul' r f := by apply AlternatingMap.ext;intro v;exact map_smul (exponentSlice R n k) r _
lemma faceSlice_eval (k : ℤ) (p : ℕ) (f : Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p)
    (a : Fin p → Chart n) : evaluation R (LaurentModule R n) p (faceSlice R n k p f) a=
    exponentSlice R n k (evaluation R (LaurentModule R (n+1)) p f (trueFace n ∘ a)) := by
  change exponentSlice R n k (f (fun i => faceVertexMap R n (basis R (a i))))=_
  simp only [faceVertexMap_basis]
  rfl
lemma faceSlice_delta (k : ℤ) (p : ℕ) (f : Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p) :
    faceSlice R n k (p+1) (delta R (LaurentModule R (n+1)) p f)=
    delta R (LaurentModule R n) p (faceSlice R n k p f) := by
  apply evaluation_injective R (LaurentModule R n) (p+1)
  apply funext;intro a
  rw [faceSlice_eval,evaluation_delta,evaluation_delta]
  simp only [FiniteCoverCech.delta,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [faceSlice_eval]
  rfl
def faceLift (k : ℤ) (p : ℕ) : Alt R (LaurentModule R n) (ι:=Chart n) p →ₗ[R]
    Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p where
  toFun f := (exponentInsert R n k).compAlternatingMap (f.compLinearMap (faceProjection R n))
  map_add' f g := by apply AlternatingMap.ext;intro v;exact map_add (exponentInsert R n k) _ _
  map_smul' r f := by apply AlternatingMap.ext;intro v;exact map_smul (exponentInsert R n k) r _
lemma faceLift_eval (k : ℤ) (p : ℕ) (f : Alt R (LaurentModule R n) (ι:=Chart n) p)
    (a : Fin p → Chart (n+1)) (ha : ∀ i,a i 0=true) :
    evaluation R (LaurentModule R (n+1)) p (faceLift R n k p f) a=
    exponentInsert R n k (evaluation R (LaurentModule R n) p f (Fin.tail ∘ a)) := by
  change exponentInsert R n k (f (fun i => faceProjection R n (basis R (a i))))=_
  simp only [faceProjection_basis,ha,ite_true]
  rfl
lemma faceLift_eval_zero (k : ℤ) (p : ℕ) (f : Alt R (LaurentModule R n) (ι:=Chart n) p)
    (a : Fin p → Chart (n+1)) (ha : ¬∀ i,a i 0=true) :
    evaluation R (LaurentModule R (n+1)) p (faceLift R n k p f) a=0 := by
  obtain ⟨i,hi⟩ := not_forall.mp ha
  change exponentInsert R n k (f (fun j => faceProjection R n (basis R (a j))))=0
  have hz : faceProjection R n (basis R (a i))=0 := by rw [faceProjection_basis,ite_eq_right hi]
  rw [f.map_coord_zero i hz,map_zero]
lemma faceSlice_lift (k : ℤ) (p : ℕ) (f : Alt R (LaurentModule R n) (ι:=Chart n) p) :
    faceSlice R n k p (faceLift R n k p f)=f := by
  apply evaluation_injective R (LaurentModule R n) p
  apply funext;intro a
  rw [faceSlice_eval,faceLift_eval R n k p f _ (fun _ => rfl),exponentSlice_insert]
  rfl
lemma faceSlice_mem (k : ℤ) (m : Fin n → ℤ) (p : ℕ)
    (f : Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p)
    (hf : f∈cochains R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons k m)) p) :
    faceSlice R n k p f∈cochains R (LaurentModule R n) (sections R n m) p := by
  intro a
  rw [faceSlice_eval]
  apply exponentSlice_mem R n k m
  have h := hf (trueFace n ∘ a)
  convert h using 1
  simp only [FiniteCoverCech.intersection,Finset.image_image,Function.comp_def]
lemma faceLift_mem (k : ℤ) (m : Fin n → ℤ) (p : ℕ) (hp : 0<p)
    (f : Alt R (LaurentModule R n) (ι:=Chart n) p)
    (hf : f∈cochains R (LaurentModule R n) (sections R n m) p) :
    faceLift R n k p f∈cochains R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons k m)) p := by
  intro a
  by_cases ha : ∀ i,a i 0=true
  · rw [faceLift_eval R n k p f a ha]
    apply exponentInsert_mem R n k m
    · exact ⟨a ⟨0,hp⟩,by simp [FiniteCoverCech.intersection]⟩
    · intro σ hσ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hσ
      exact ha i
    · have h := hf (Fin.tail ∘ a)
      convert h using 1
      simp only [FiniteCoverCech.intersection,Finset.image_image,Function.comp_def]
  · rw [faceLift_eval_zero R n k p f a ha]
    exact (sections R (n+1) (Fin.cons k m) _).zero_mem
end Lech.ProductSourceCover
end
end

end OAI
