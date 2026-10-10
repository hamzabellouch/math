import Mathlib
import OAI.RingTheory.Multiplicity.ProductSourceCoverHighThreshold

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
namespace Lech.ProductSourceCover

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
 

def cechNatCohomologyComparison (m : Fin n → ℤ) (q : ℕ) :
    (sourceCech R n m).homology q ≅ (targetCech R n m).homology q :=
  ((sourceCech R n m).extendHomologyIso ComplexShape.embeddingUpNat (j:=q) (j':=(q:ℤ)) rfl).symm ≪≫
    cechCohomologyComparison R n m (q:ℤ) ≪≫
    (targetCech R n m).extendHomologyIso ComplexShape.embeddingUpNat (j:=q) (j':=(q:ℤ)) rfl
 

theorem targetEndpoint_isZero (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1) (q : ℕ) :
    IsZero ((targetCech R n m).homology (q+1)) :=
  (endpointCohomology_isZero R n m j hj q).of_iso (cechNatCohomologyComparison R n m (q+1)).symm
 

def targetHighTwistH0 (m : Fin n → ℤ) (hm : ∀ i,-1 ≤ m i) :
    (targetCech R n m).homology 1 ≅ ModuleCat.of R (ringSections R n m ∅) :=
  (cechNatCohomologyComparison R n m 1).symm ≪≫ highTwistH0 R n m hm
lemma targetHighTwistHigher (m : Fin n → ℤ) (hm : ∀ i,-1 ≤ m i) (q : ℕ) :
    IsZero ((targetCech R n m).homology (q+2)) :=
  (highTwistHigher R n m hm q).of_iso (cechNatCohomologyComparison R n m (q+2)).symm
def targetHighTwistBasis (m : Fin n → ℤ) (hm : ∀ i,-1 ≤ m i) :
    Module.Basis (GlobalIndex n m) R ((targetCech R n m).homology 1) :=
  (globalBasis R n m).map (targetHighTwistH0 R n m hm).toLinearEquiv.symm
lemma targetHighTwist_finrank [Nontrivial R] (m : Fin n → ℤ) (hm : ∀ i,-1 ≤ m i) :
    Module.finrank R ((targetCech R n m).homology 1)=∏ i,(m i+1).toNat := by
  rw [Module.finrank_eq_card_basis (targetHighTwistBasis R n m hm),globalIndex_card]
 

theorem rootTarget_atRoot (r : Fin n → ℤ) (j : Fin n) (q : ℕ) :
    IsZero ((targetCech R n (fun i => r j-1-r i)).homology (q+1)) :=
  targetEndpoint_isZero R n _ j (by omega) q
 

lemma rootTarget_above_finrank [Nontrivial R] (r : Fin n → ℤ) (a : ℤ) (ha : ∀ i,r i<a) :
    Module.finrank R ((targetCech R n (fun i => a-1-r i)).homology 1)=∏ i,(a-r i).toNat := by
  rw [targetHighTwist_finrank R n _ (fun i => by have:=ha i;omega)]
  congr 1
  ext i
  congr 1
  omega
end


open scoped BigOperators Classical
lemma negativeCount_root (n : ℕ) (r : Fin n → ℤ) (a : ℤ) :
    negativeCount (fun i => a-1-r i)=(Finset.univ.filter (fun i => a<r i)).card := by
  have hi : ∀ i : Fin n,(a-1-r i < -1) ↔ a<r i := fun i => by omega
  simp [negativeCount,hi]
lemma signedRank_root (n : ℕ) (r : Fin n → ℤ) (a : ℤ) :
    signedRank (fun i => a-1-r i)=∏ i,(a-r i).natAbs := by
  unfold signedRank
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg Int.natAbs
  dsimp
  ring
end Lech.ProductSourceCover


namespace Lech

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
lemma pureCohomology_of_iso (K L : CochainComplex (ModuleCat.{u} R) ℕ)
    (e : ∀ p,K.homology p ≅ L.homology p) (d r : ℕ)
    (h : PureCohomology R K d r) : PureCohomology R L d r := by
  refine ⟨fun p hp => (h.1 p hp).of_iso (e p).symm,?_⟩
  obtain ⟨b⟩ := h.2
  exact ⟨b.map (e d).toLinearEquiv⟩
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R]
 

def finiteCechEuler (K : CochainComplex (ModuleCat.{u} R) ℕ) (N : ℕ) : ℤ :=
  ∑ q ∈ Finset.range (N+1), ((-1:ℤ)^q * (Module.finrank R (K.homology (q+1)):ℤ))
lemma pureCohomology_finrank [Nontrivial R] (K : CochainComplex (ModuleCat.{u} R) ℕ)
    (d r : ℕ) (h : PureCohomology R K d r) : Module.finrank R (K.homology d)=r := by
  obtain ⟨b⟩ := h.2
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
lemma pureCohomology_finrank_eq_zero [Nontrivial R] (K : CochainComplex (ModuleCat.{u} R) ℕ)
    (d r q : ℕ) (h : PureCohomology R K d r) (hq : q≠d) :
    Module.finrank R (K.homology q)=0 := by
  have : Subsingleton (K.homology q) := ModuleCat.isZero_iff_subsingleton.mp (h.1 q hq)
  exact Module.finrank_zero_of_subsingleton
lemma pureCohomology_finiteEuler [Nontrivial R] (K : CochainComplex (ModuleCat.{u} R) ℕ)
    (N d r : ℕ) (hd : d≤N) (h : PureCohomology R K (d+1) r) :
    finiteCechEuler R K N=(-1:ℤ)^d*(r:ℤ) := by
  unfold finiteCechEuler
  rw [Finset.sum_eq_single d]
  · rw [pureCohomology_finrank R K (d+1) r h]
  · intro q _ hq
    rw [pureCohomology_finrank_eq_zero R K (d+1) r (q+1) h (by omega)]
    simp
  · intro hd'
    exact (hd' (Finset.mem_range.mpr (by omega))).elim
end Lech


namespace Lech.ProductSourceCover

section

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
 

theorem sourceSigned_pure (m : Fin n → ℤ) :
    PureCohomology R (sourceCech R n m) (negativeCount m+1) (signedRank m) :=
  pureCohomology_of_iso R (ordinaryComplex R n m) (sourceCech R n m)
    (ordinaryCohomologyIso R n m) _ _ (ordinary_signed_pure R n m)
 

theorem targetSigned_pure (m : Fin n → ℤ) :
    PureCohomology R (targetCech R n m) (negativeCount m+1) (signedRank m) :=
  pureCohomology_of_iso R (sourceCech R n m) (targetCech R n m)
    (cechNatCohomologyComparison R n m) _ _ (sourceSigned_pure R n m)
 

theorem rootTarget_pure (r : Fin n → ℤ) (a : ℤ) :
    PureCohomology R (targetCech R n (fun i => a-1-r i))
      ((Finset.univ.filter (fun i => a<r i)).card+1) (∏ i,(a-r i).natAbs) := by
  simpa only [negativeCount_root,signedRank_root] using
    targetSigned_pure R n (fun i => a-1-r i)
 

theorem targetSigned_euler [Nontrivial R] (m : Fin n → ℤ) :
    finiteCechEuler R (targetCech R n m) n=∏ i,(m i+1) := by
  rw [pureCohomology_finiteEuler R _ n (negativeCount m) (signedRank m)
    (negativeCount_le m) (targetSigned_pure R n m),signedRank_euler]
 
theorem rootTarget_euler [Nontrivial R] (r : Fin n → ℤ) (a : ℤ) :
    finiteCechEuler R (targetCech R n (fun i => a-1-r i)) n=∏ i,(a-r i) := by
  rw [targetSigned_euler]
  apply Finset.prod_congr rfl
  intro i _
  ring
 

theorem targetSigned_above (m : Fin n → ℤ) (q : ℕ) (hq : n<q) :
    IsZero ((targetCech R n m).homology (q+1)) :=
  (targetSigned_pure R n m).1 (q+1) (by have:=negativeCount_le m;omega)
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
 
def RootPositions (s : ℕ) (r : Fin n → ℤ) : Prop :=
  ∀ j, -((j.val:ℤ)+2)*(s:ℤ) < r j ∧ r j < -((j.val:ℤ)+1)*(s:ℤ)
def rootDegree (r : Fin n → ℤ) (a : ℤ) : ℕ :=
  (Finset.univ.filter (fun j => a < r j)).card
omit [LinearOrder (Chart n)] in
lemma rootDegree_nonnegative_layer {s : ℕ} {r : Fin n → ℤ}
    (hr : RootPositions n s r) (i : ℕ) (l : ℤ) (hl : 0 ≤ l) :
    rootDegree n r (l-(i:ℤ)*(s:ℤ)) ≤ i := by
  have hsub : Finset.univ.filter (fun j : Fin n => l-(i:ℤ)*(s:ℤ) < r j) ⊆
      Finset.univ.filter (fun j : Fin n => j.val < i) := by
    intro j hj
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
    by_contra hn
    have ht : (i:ℤ) ≤ (j.val:ℤ)+1 := by omega
    have hm := mul_le_mul_of_nonneg_right ht (show (0:ℤ)≤(s:ℤ) by omega)
    have hp := (hr j).2
    nlinarith
  exact (Finset.card_le_card hsub).trans (by rw [Fin.card_filter_val_lt];exact min_le_right _ _)
omit [LinearOrder (Chart n)] in
lemma rootDegree_negative_layer {s : ℕ} {r : Fin n → ℤ}
    (hr : RootPositions n s r) (i : ℕ) (hi : i ≤ n+1) (l : ℤ) (hl : l < 0) :
    i-1 ≤ rootDegree n r (l-(i:ℤ)*(s:ℤ)) := by
  have hsub : Finset.univ.filter (fun j : Fin n => j.val < i-1) ⊆
      Finset.univ.filter (fun j : Fin n => l-(i:ℤ)*(s:ℤ) < r j) := by
    intro j hj
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
    have ht : (j.val:ℤ)+2 ≤ (i:ℤ) := by omega
    have hm := mul_le_mul_of_nonneg_right ht (show (0:ℤ)≤(s:ℤ) by omega)
    have hp := (hr j).1
    nlinarith
  have hcard := Finset.card_le_card hsub
  rw [Fin.card_filter_val_lt,min_eq_right (by omega)] at hcard
  exact hcard
 

theorem rootLayer_nonnegative_isZero {s : ℕ} {r : Fin n → ℤ}
    (hr : RootPositions n s r) (i : ℕ) (l : ℤ) (hl : 0 ≤ l)
    (q : ℕ) (hq : i < q) :
    IsZero ((targetCech R n (fun j => (l-(i:ℤ)*(s:ℤ))-1-r j)).homology (q+1)) := by
  have hd := rootDegree_nonnegative_layer n hr i l hl
  apply (rootTarget_pure R n r (l-(i:ℤ)*(s:ℤ))).1
  change q+1≠rootDegree n r (l-(i:ℤ)*(s:ℤ))+1
  omega
 

theorem rootLayer_negative_isZero {s : ℕ} {r : Fin n → ℤ}
    (hr : RootPositions n s r) (i : ℕ) (hi : i ≤ n+1) (l : ℤ) (hl : l < 0)
    (q : ℕ) (hq : q+1 < i) :
    IsZero ((targetCech R n (fun j => (l-(i:ℤ)*(s:ℤ))-1-r j)).homology (q+1)) := by
  have hd := rootDegree_negative_layer n hr i hi l hl
  apply (rootTarget_pure R n r (l-(i:ℤ)*(s:ℤ))).1
  change q+1≠rootDegree n r (l-(i:ℤ)*(s:ℤ))+1
  omega
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
 

def rootTwistRow (r : Fin n → ℤ) (a : ℤ) : BicomplexTotal.Row (R:=R) :=
  ((targetCech R n (fun j => a-1-r j)).extend ComplexShape.embeddingUpNat)⟦(1:ℤ)⟧
def rootTwistRowHomologyIso (r : Fin n → ℤ) (a q : ℤ) :
    (rootTwistRow R n r a).homology q ≅
      ((targetCech R n (fun j => a-1-r j)).extend ComplexShape.embeddingUpNat).homology (1+q) :=
  (((homologyFunctor (ModuleCat.{u} R) (.up ℤ) (0:ℤ)).shiftIso (1:ℤ) q _ rfl).app _)
 

lemma rootTwistRow_isZero (r : Fin n → ℤ) (a q : ℤ)
    (hq : q ≠ (rootDegree n r a:ℤ)) :
    IsZero ((rootTwistRow R n r a).homology q) := by
  apply IsZero.of_iso _ (rootTwistRowHomologyIso R n r a q)
  by_cases hp : 0 ≤ 1+q
  · obtain ⟨p,hp⟩ := Int.eq_ofNat_of_zero_le hp
    have hz := (rootTarget_pure R n r a).1 p (by
      change p≠rootDegree n r a+1
      omega)
    exact hz.of_iso ((targetCech R n (fun j => a-1-r j)).extendHomologyIso
      ComplexShape.embeddingUpNat (j:=p) (by exact hp.symm))
  · apply HomologicalComplex.ExactAt.isZero_homology
    apply HomologicalComplex.extend_exactAt
    intro p hp'
    change (p:ℤ)=1+q at hp'
    omega
end Lech.ProductSourceCover


namespace Lech.ComplexPi

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
variable {R : Type u} [CommRing R]
  {α β γ : Type v}
  {C D E : CochainComplex (ModuleCat.{max u v} R) ℤ}


def copies (α : Type v) (C : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    CochainComplex (ModuleCat.{max u v} R) ℤ where
  X q := ModuleCat.of R (α → C.X q)
  d q r := ModuleCat.ofHom ((C.d q r).hom.compLeft α)
  shape q r hqr := by rw [C.shape q r hqr]; rfl
  d_comp_d' q r s _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext; intro x; funext a
    exact congrArg (fun f : C.X q ⟶ C.X s => f.hom (x a)) (C.d_comp_d q r s)

 
def matrixMap [Fintype α] (A : β → α → (C ⟶ D)) : copies α C ⟶ copies β D where
  f q := ModuleCat.ofHom
    { toFun x b := ∑ a, (A b a).f q (x a)
      map_add' x y := by ext b; simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
      map_smul' r x := by ext b; simp only [map_smul,Finset.smul_sum,Pi.smul_apply,RingHom.id_apply] }
  comm' q r _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext; intro x; funext b
    change (D.d q r) (∑ a, (A b a).f q (x a)) = (∑ a, (A b a).f r ((C.d q r) (x a)))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun f : C.X q ⟶ D.X r => f (x a)) ((A b a).comm q r)

@[simp] lemma matrixMap_f [Fintype α] (A : β → α → (C ⟶ D)) (q : ℤ)
    (x : α → C.X q) (b : β) : (matrixMap A).f q x b=∑ a, (A b a).f q (x a) := rfl

lemma matrixMap_zero [Fintype α] : matrixMap (fun (_ : β) (_ : α) => (0 : C ⟶ D))=0 := by
  apply Hom.ext; funext q; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; funext b
  change (∑ a : α, (0 : C.X q ⟶ D.X q) (x a))=0
  simp

lemma matrixMap_add [Fintype α] (A B : β → α → (C ⟶ D)) :
    matrixMap (fun b a => A b a+B b a)=matrixMap A+matrixMap B := by
  apply Hom.ext; funext q; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; funext b
  change (∑ a, ((A b a).f q + (B b a).f q) (x a)) =
    (∑ a, (A b a).f q (x a)) + ∑ a, (B b a).f q (x a)
  simp [Finset.sum_add_distrib]

lemma sum_f_apply [Fintype α] (A : α → (C ⟶ D)) (q : ℤ) (x : C.X q) :
    (∑ a, A a).f q x=∑ a, (A a).f q x := by
  let e : (C ⟶ D) →+ D.X q :=
    { toFun f := f.f q x
      map_zero' := rfl
      map_add' _ _ := rfl }
  exact map_sum e A Finset.univ

lemma matrixMap_comp [Fintype α] [Fintype β]
    (A : β → α → (C ⟶ D)) (B : γ → β → (D ⟶ E)) :
    matrixMap A ≫ matrixMap B=matrixMap (fun c a => ∑ b, A b a ≫ B c b) := by
  apply Hom.ext; funext q; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; funext c
  change (∑ b, (B c b).f q (∑ a, (A b a).f q (x a)))=
    ∑ a, ((∑ b, A b a ≫ B c b).f q) (x a)
  simp only [map_sum,sum_f_apply,comp_f,ModuleCat.comp_apply]
  exact Finset.sum_comm

 
def map (α : Type v) (f : C ⟶ D) : copies α C ⟶ copies α D where
  f q := ModuleCat.ofHom ((f.f q).hom.compLeft α)
  comm' q r _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext; intro x; funext a
    exact congrArg (fun f : C.X q ⟶ D.X r => f (x a)) (f.comm q r)

@[simp] lemma map_f (α : Type v) (f : C ⟶ D) (q : ℤ) (x : α → C.X q) (a : α) :
    (map α f).f q x a=f.f q (x a) := rfl

lemma map_id (α : Type v) : map α (𝟙 C)=𝟙 _ := by apply Hom.ext; funext q; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; funext a; rfl
lemma map_comp (α : Type v) (f : C ⟶ D) (g : D ⟶ E) :
    map α (f≫g)=map α f≫map α g := by apply Hom.ext; funext q; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; funext a; rfl
lemma matrixMap_map [Fintype α] (A : β → α → (C ⟶ D)) (f : D ⟶ E) :
    matrixMap A ≫ map β f=matrixMap (fun b a => A b a≫f) := by
  apply Hom.ext; funext q; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; funext b
  exact map_sum (f.f q).hom _ _
lemma map_matrixMap [Fintype α] (f : C ⟶ D) (A : β → α → (D ⟶ E)) :
    map α f ≫ matrixMap A=matrixMap (fun b a => f≫ A b a) := by
  apply Hom.ext; funext q; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; funext b
  rfl

instance map_mono (α : Type v) (f : C ⟶ D) [Mono f] : Mono (map α f) := by
  apply mono_of_mono_f
  intro q
  apply (ModuleCat.mono_iff_injective _).mpr
  intro x y hxy
  funext a
  exact (ModuleCat.mono_iff_injective (f.f q)).mp inferInstance (congrFun hxy a)

lemma isZero_copies (α : Type v) (hC : IsZero C) : IsZero (copies α C) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Hom.ext; funext q; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; funext a
  have hq := (HomologicalComplex.eval _ _ q).map_isZero hC
  have : Subsingleton (C.X q) := (ModuleCat.isZero_iff_subsingleton).mp hq
  exact Subsingleton.elim _ _
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
variable {R : Type u} [CommRing R] (α : Type v)
variable (C : CochainComplex (ModuleCat.{max u v} R) ℤ)
lemma copies_exactAt (q : ℤ) (hC : C.ExactAt q) : (copies α C).ExactAt q := by
  apply ((copies α C).exactAt_iff' (i:=q-1) (j:=q) (k:=q+1)
    (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change ((copies α C).d q (q+1)).hom x=0 at hx
  have he := (C.exactAt_iff' (i:=q-1) (j:=q) (k:=q+1)
    (by simp) (by simp)).mp hC
  rw [ShortComplex.moduleCat_exact_iff] at he
  have hy (a : α) : ∃ y : C.X (q-1), (C.d (q-1) q).hom y=x a := by
    exact he (x a) (congrFun hx a)
  choose y hy using hy
  exact ⟨y,funext hy⟩
lemma copies_homology_isZero (q : ℤ) (hC : IsZero (C.homology q)) :
    IsZero ((copies α C).homology q) :=
  (copies_exactAt α C q ((C.exactAt_iff_isZero_homology q).mpr hC)).isZero_homology
end Lech.ComplexPi


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators Classical ZeroObject
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
 

def rootLayerTerm (r : Fin n → ℤ) (s : ℕ) (l : ℤ) (b : ℕ → ℕ)
    (j : ℤ) : BicomplexTotal.Row (R:=R) :=
  if -(n+1:ℤ) ≤ j ∧ j ≤ 0 then
    ComplexPi.copies (Fin (b (-j).toNat))
      (rootTwistRow R n r (l-((-j).toNat:ℤ)*(s:ℤ)))
  else 0
variable (r : Fin n → ℤ) (s : ℕ) (l : ℤ) (b : ℕ → ℕ)
variable (d : ∀ j:ℤ,rootLayerTerm R n r s l b j ⟶ rootLayerTerm R n r s l b (j+1))
variable (hd : ∀ j:ℤ,d j ≫ d (j+1)=0)
 

def rootLayerDouble : BicomplexTotal.Double (R:=R) :=
  CochainComplex.of (rootLayerTerm R n r s l b) d hd
omit [LinearOrder (Chart n)] in
lemma rootLayerDouble_bounded (j : ℤ) (hj : j < -(n+1:ℤ) ∨ 1 ≤ j) :
    IsZero ((rootLayerDouble R n r s l b d hd).X j) := by
  change IsZero (rootLayerTerm R n r s l b j)
  simp only [rootLayerTerm,show ¬ (-(n+1:ℤ) ≤ j ∧ j≤0) by omega,ite_false]
  exact isZero_zero _
 

theorem rootLayerTotal_nonnegative (hr : RootPositions n s r) (hl : 0 ≤ l)
    (k : ℤ) (hk : 0 < k) :
    IsZero ((total (rootLayerDouble R n r s l b d hd) (.up ℤ)).homology k) := by
  apply BicomplexTotal.devissage (IsZero (C:=ModuleCat.{u} R))
    (-(n+1:ℤ)) (n+2) (rootLayerDouble R n r s l b d hd) k
  · intro j hj
    exact rootLayerDouble_bounded R n r s l b d hd j (by omega)
  intro j
  apply IsZero.of_iso _ (BicomplexTotal.singleHomologyIso
    ((rootLayerDouble R n r s l b d hd).X j) j k)
  change IsZero ((rootLayerTerm R n r s l b j).homology (-j+k))
  by_cases hj : -(n+1:ℤ) ≤ j ∧ j≤0
  · simp only [rootLayerTerm,hj]
    apply ComplexPi.copies_homology_isZero
    apply rootTwistRow_isZero
    have he : ((-j).toNat:ℤ) = -j := Int.toNat_of_nonneg (by omega)
    have hcount := rootDegree_nonnegative_layer n hr (-j).toNat l hl
    omega
  · simp only [rootLayerTerm,hj,ite_false]
    exact (homologyFunctor (ModuleCat.{u} R) (.up ℤ) (-j+k)).map_isZero (isZero_zero _)
 

theorem rootLayerTotal_negative (hr : RootPositions n s r) (hl : l < 0)
    (k : ℤ) (hk : k < -1) :
    IsZero ((total (rootLayerDouble R n r s l b d hd) (.up ℤ)).homology k) := by
  apply BicomplexTotal.devissage (IsZero (C:=ModuleCat.{u} R))
    (-(n+1:ℤ)) (n+2) (rootLayerDouble R n r s l b d hd) k
  · intro j hj
    exact rootLayerDouble_bounded R n r s l b d hd j (by omega)
  intro j
  apply IsZero.of_iso _ (BicomplexTotal.singleHomologyIso
    ((rootLayerDouble R n r s l b d hd).X j) j k)
  change IsZero ((rootLayerTerm R n r s l b j).homology (-j+k))
  by_cases hj : -(n+1:ℤ) ≤ j ∧ j≤0
  · simp only [rootLayerTerm,hj]
    apply ComplexPi.copies_homology_isZero
    apply rootTwistRow_isZero
    have he : ((-j).toNat:ℤ) = -j := Int.toNat_of_nonneg (by omega)
    have hcount := rootDegree_negative_layer n hr (-j).toNat (by omega) l hl
    omega
  · simp only [rootLayerTerm,hj,ite_false]
    exact (homologyFunctor (ModuleCat.{u} R) (.up ℤ) (-j+k)).map_isZero (isZero_zero _)
end Lech.ProductSourceCover

end

end OAI
