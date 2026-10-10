import Mathlib
import OAI.RingTheory.Multiplicity.ProductSourceCoverFaceSlice

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
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
lemma connecting_isoModSerre (P : ObjectProperty C) [P.IsSerreClass]
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact)
    (i j : ι) (hij : c.Rel i j)
    (hi : P (S.X₂.homology i)) (hj : P (S.X₂.homology j)) :
    P.isoModSerre (hS.δ i j hij) := by
  constructor
  · have : Epi (kernel.lift (hS.δ i j hij) (homologyMap S.g i)
        (hS.comp_δ i j hij)) := (hS.homology_exact₃ i j hij).epi_kernelLift
    exact P.prop_of_epi (kernel.lift (hS.δ i j hij) (homologyMap S.g i) (hS.comp_δ i j hij)) hi
  · have : Mono (cokernel.desc (hS.δ i j hij) (homologyMap S.f j)
        (hS.δ_comp i j hij)) := (hS.homology_exact₁ i j hij).mono_cokernelDesc
    exact P.prop_of_mono (cokernel.desc (hS.δ i j hij) (homologyMap S.f j) (hS.δ_comp i j hij)) hj
end Lech


namespace Lech.BicomplexTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable (K : Double (R := R)) (N : ℕ)
  (hb : ∀ j, j < 0 ∨ (N:ℤ) ≤ j → IsZero (K.X j))
  (hr : ∀ j, 0<j → ∀ i, IsZero ((K.X j).homology i))
def positiveRows : Double (R := R) :=
  FiniteComplex.dropBottom K 0 (fun j hj => hb j (Or.inl hj))
lemma positiveRows_bounded (j : ℤ) (hj : j<0 ∨ (N:ℤ)≤j) :
    IsZero ((positiveRows K N hb).X j) := by
  by_cases hj0 : j=0
  · subst j
    exact FiniteComplex.dropBottom_X_bottom K 0 _
  · exact (hb j hj).of_iso (FiniteComplex.dropBottomXIso K 0 _ j hj0)
include hr in
lemma positiveRows_acyclic (j i : ℤ) :
    IsZero (((positiveRows K N hb).X j).homology i) := by
  by_cases hj : j≤0
  · apply (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).map_isZero
    exact FiniteComplex.dropBottom_boundedBelow K 0 _ j (by omega)
  · exact (hr j (by omega) i).of_iso
      ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
        (FiniteComplex.dropBottomXIso K 0 _ j (by omega)))
include hr in
lemma positiveRows_total_acyclic (i : ℤ) :
    IsZero ((total (positiveRows K N hb) (.up ℤ)).homology i) := by
  apply acyclic_of_rows 0 N (positiveRows K N hb)
  · intro j hj
    exact positiveRows_bounded K N hb j (by simpa only [zero_add] using hj)
  · exact positiveRows_acyclic K N hb hr
lemma bottom_total_shortExact :
    ((FiniteComplex.bottomShortComplex K 0 (fun j hj => hb j (Or.inl hj))).map
      (functor (R := R))).ShortExact :=
  shortExact_of_degreewise_shortExact _ (fun i =>
    (splitting _ (FiniteComplex.bottomSplitting K 0 _) i).shortExact)
include hr in
lemma bottom_total_homology_isIso (i : ℤ) :
    IsIso (homologyMap ((functor (R := R)).map
      (FiniteComplex.bottomProjection K 0 (fun j hj => hb j (Or.inl hj)))) i) := by
  let S := (FiniteComplex.bottomShortComplex K 0 (fun j hj => hb j (Or.inl hj))).map
    (functor (R := R))
  have hS : S.ShortExact := bottom_total_shortExact K N hb
  have h0 (j : ℤ) : IsZero (S.X₁.homology j) := positiveRows_total_acyclic K N hb hr j
  have : Mono (homologyMap S.g i) :=
    (hS.homology_exact₂ i).mono_g ((h0 i).eq_of_src _ _)
  have : Epi (homologyMap S.g i) :=
    (hS.homology_exact₃ i (i+1) rfl).epi_f ((h0 (i+1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi (homologyMap S.g i)
 

def bottomHomologyIso (i : ℤ) :
    (total K (.up ℤ)).homology i ≅ (K.X 0).homology i := by
  exact @asIso _ _ _ _ (homologyMap ((functor (R := R)).map
    (FiniteComplex.bottomProjection K 0 (fun j hj => hb j (Or.inl hj)))) i)
      (bottom_total_homology_isIso K N hb hr i) ≪≫
      (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso (singleZeroIso (K.X 0)).symm
 

def doubleCoverIso (M : ℕ)
    (hc : ∀ j, j<0 ∨ (M:ℤ)≤j → IsZero ((flip K).X j))
    (hcExact : ∀ j,0<j → ∀ i,IsZero (((flip K).X j).homology i)) (i : ℤ) :
    (K.X 0).homology i ≅ ((flip K).X 0).homology i :=
  (bottomHomologyIso K N hb hr i).symm ≪≫
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso (totalFlipIso K (.up ℤ)).symm ≪≫
      bottomHomologyIso (flip K) M hc hcExact i
end Lech.BicomplexTotal


namespace Lech.ComplexExtension
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
abbrev NatDouble := CochainComplex (CochainComplex (ModuleCat.{u} R) ℕ) ℕ
variable (K : NatDouble (R := R))
 
def doubleExtend : BicomplexTotal.Double (R := R) :=
  ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).obj
    (K.extend ComplexShape.embeddingUpNat)
def rowIso (n : ℕ) : (doubleExtend K).X (n:ℤ) ≅ (K.X n).extend ComplexShape.embeddingUpNat :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso
    (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
def columnEvalIso (n : ℕ) : (flip (doubleExtend K)).X (n:ℤ) ≅
    ((eval (ModuleCat.{u} R) (.up ℕ) n).mapHomologicalComplex (.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat) :=
  Hom.isoOfComponents (fun i => ((K.extend ComplexShape.embeddingUpNat).X i).extendXIso
    ComplexShape.embeddingUpNat (i := n) rfl) (fun i j _ => by
      change _ = (extendMap ((K.extend ComplexShape.embeddingUpNat).d i j)
        ComplexShape.embeddingUpNat).f (n:ℤ) ≫ _
      erw [extendMap_f _ ComplexShape.embeddingUpNat (i := n) (show ComplexShape.embeddingUpNat.f n=(n:ℤ) from rfl)]
      simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
      rfl)
def columnIso (n : ℕ) : (flip (doubleExtend K)).X (n:ℤ) ≅
    ((flip K).X n).extend ComplexShape.embeddingUpNat :=
  columnEvalIso K n ≪≫ mapExtendIso (eval (ModuleCat.{u} R) (.up ℕ) n) K
lemma row_negative (i : ℤ) (hi : i < 0) : IsZero ((doubleExtend K).X i) := by
  apply (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).map_isZero
  apply K.isZero_extend_X
  intro n hn
  change (n:ℤ)=i at hn
  omega
lemma column_negative (i : ℤ) (hi : i < 0) : IsZero ((flip (doubleExtend K)).X i) := by
  apply FiniteComplex.isZero_of_X
  intro j
  apply ((K.extend ComplexShape.embeddingUpNat).X j).isZero_extend_X
  intro n hn
  change (n:ℤ)=i at hn
  omega
lemma extended_acyclic (L : CochainComplex (ModuleCat.{u} R) ℕ) (hL : L.Acyclic) :
    (L.extend ComplexShape.embeddingUpNat).Acyclic := by
  intro i
  by_cases hi : 0 ≤ i
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact (L.extend_exactAt_iff ComplexShape.embeddingUpNat (j := n) rfl).mpr (hL n)
  · apply L.extend_exactAt
    intro n hn
    change (n:ℤ)=i at hn
    omega
variable (N M : ℕ) (hrb : ∀ n,N≤n → IsZero (K.X n))
  (hcb : ∀ n,M≤n → IsZero ((flip K).X n))
  (hr : ∀ n,0<n → (K.X n).Acyclic) (hc : ∀ n,0<n → ((flip K).X n).Acyclic)
include hrb in
lemma row_bounded (i : ℤ) (hi : i < 0 ∨ (N:ℤ) ≤ i) : IsZero ((doubleExtend K).X i) := by
  by_cases hi0 : i < 0
  · exact row_negative K i hi0
  obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
  exact ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).map_isZero
    (hrb n (by omega))).of_iso (rowIso K n)
include hcb in
lemma column_bounded (i : ℤ) (hi : i < 0 ∨ (M:ℤ) ≤ i) : IsZero ((flip (doubleExtend K)).X i) := by
  by_cases hi0 : i < 0
  · exact column_negative K i hi0
  obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
  exact ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).map_isZero
    (hcb n (by omega))).of_iso (columnIso K n)
include hr in
lemma row_positive (i : ℤ) (hi : 0 < i) (j : ℤ) : IsZero (((doubleExtend K).X i).homology j) := by
  obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
  exact ((extended_acyclic (K.X n) (hr n (by omega)) j).isZero_homology).of_iso
    ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) j).mapIso (rowIso K n))
include hc in
lemma column_positive (i : ℤ) (hi : 0 < i) (j : ℤ) : IsZero (((flip (doubleExtend K)).X i).homology j) := by
  obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
  exact ((extended_acyclic ((flip K).X n) (hc n (by omega)) j).isZero_homology).of_iso
    ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) j).mapIso (columnIso K n))
 

def natDoubleCoverIso (i : ℤ) :
    ((K.X 0).extend ComplexShape.embeddingUpNat).homology i ≅
      (((flip K).X 0).extend ComplexShape.embeddingUpNat).homology i :=
  ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso (rowIso K 0)).symm ≪≫
    BicomplexTotal.doubleCoverIso (doubleExtend K) N (row_bounded K N hrb)
      (row_positive K hr) M (column_bounded K M hcb) (column_positive K hc) i ≪≫
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso (columnIso K 0)
end Lech.ComplexExtension


namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
local instance connectingSortedDecEq : DecidableEq ι := Classical.decEq ι
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
 
def sortedComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (sorted R M F n))
    (fun n => ModuleCat.ofHom (sortedDelta R M F hF n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact sortedDelta_square R M F hF n)
lemma sortedComplex_d (n : ℕ) : (sortedComplex R M F hF).d n (n+1)=
    ModuleCat.ofHom (sortedDelta R M F hF n) := by
  change CochainComplex.of.d (fun n => ModuleCat.of R (sorted R M F n))
    (fun n => ModuleCat.ofHom (sortedDelta R M F hF n)) n (n+1)=_
  exact CochainComplex.of_d _ _ n
 

def cochainsSortedIso : complex R M F hF ≅ sortedComplex R M F hF :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (cochainsSorted R M F n).toModuleIso)
    (fun n m h => by
      obtain rfl : n+1=m := h
      rw [complex_d,sortedComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (cochainsSorted_delta R M F hF n f).symm)
variable (q : ι → R) (hq : Ideal.span (Set.range q)=⊤)
include hq in
lemma sortedDelta_injective : Function.Injective (sortedDelta R M F hF 0) := by
  intro f g h
  obtain ⟨x,rfl⟩ := (cochainsSorted R M F 0).surjective f
  obtain ⟨y,rfl⟩ := (cochainsSorted R M F 0).surjective g
  congr 1
  apply differential_injective R M F hF q hq
  apply (cochainsSorted R M F 1).injective
  simpa only [cochainsSorted_delta] using h
variable (hclear : ∀ (s : Finset ι) (j : ι) (x : M),x∈F (insert j s) → ∃ N : ℕ,q j^N • x∈F s)
include hq hclear in
lemma sortedComplex_acyclic : (sortedComplex R M F hF).Acyclic := by
  intro n
  exact (complex_acyclic R M F hF q hq hclear n).of_iso (cochainsSortedIso R M F hF)
lemma sortedComplex_bounded (n : ℕ) (hn : Fintype.card ι<n) :
    IsZero ((sortedComplex R M F hF).X n) := by
  have : Subsingleton (sorted R M F n) := ⟨fun f g => funext fun s => by
    have hs : s.val.card=n := s.property
    have h := Finset.card_le_univ s.val
    omega⟩
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (sorted R M F n))
end Lech.AlternatingCech


namespace Lech.DoubleCech

section
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))
omit [Fintype ι] [LinearOrder ι] in
lemma row_exact (p : ℕ)
    (h : ∀ s : powersetCard ι p,(AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).Acyclic) :
    (row R M F h₂ p).Acyclic := by
  intro q
  cases q with
  | zero =>
    apply ((row R M F h₂ p).exactAt_iff' (i:=0) (j:=0) (k:=1) (by simp) (by simp)).mpr
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    change ((row R M F h₂ p).d 0 1).hom x=0 at hx
    rw [row_d] at hx
    have hx0 : x=0 := by
      funext s
      have hs := ((AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).exactAt_iff'
        (i:=0) (j:=0) (k:=1) (by simp) (by simp)).mp (h s 0)
      rw [ShortComplex.moduleCat_exact_iff] at hs
      obtain ⟨y,hy⟩ := hs (x s) (by
        change ((AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).d 0 1).hom (x s)=0
        rw [AlternatingCech.sortedComplex_d]
        exact congrFun hx s)
      have hd := (AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).shape 0 0 (by simp)
      change ((AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).d 0 0).hom y=x s at hy
      rw [hd] at hy
      exact hy.symm
    exact ⟨0,by simp [hx0]⟩
  | succ q =>
    apply ((row R M F h₂ p).exactAt_iff' (i:=q) (j:=q+1) (k:=q+2) (by simp) (by simp)).mpr
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    change ((row R M F h₂ p).d (q+1) (q+2)).hom x=0 at hx
    rw [row_d] at hx
    have hs (s : powersetCard ι p) : ∃ y : AlternatingCech.sorted R M (F s.val) q,
        AlternatingCech.sortedDelta R M (F s.val) (h₂ s.val) q y=x s := by
      have he := ((AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).exactAt_iff'
        (i:=q) (j:=q+1) (k:=q+2) (by simp) (by simp)).mp (h s (q+1))
      rw [ShortComplex.moduleCat_exact_iff] at he
      obtain ⟨y,hy⟩ := he (x s) (by
        change ((AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).d (q+1) (q+2)).hom (x s)=0
        rw [AlternatingCech.sortedComplex_d]
        exact congrFun hx s)
      refine ⟨y,?_⟩
      change ((AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).d q (q+1)).hom y=x s at hy
      rw [AlternatingCech.sortedComplex_d] at hy
      exact hy
    choose y hy using hs
    refine ⟨y,?_⟩
    change ((row R M F h₂ p).d q (q+1)).hom y=x
    rw [row_d]
    exact funext hy
lemma complex_d (p : ℕ) : (complex R M F h₁ h₂).d p (p+1)=rowMap R M F h₁ h₂ p := by
  change CochainComplex.of.d (row R M F h₂) (rowMap R M F h₁ h₂) p (p+1)=_
  exact CochainComplex.of_d _ _ p
def switch (p q : ℕ) : term R M F p q ≃ₗ[R] term R M (fun t s => F s t) q p where
  toFun x t s := x s t
  invFun x s t := x t s
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
 
def columnIso (q : ℕ) : ((flip (complex R M F h₁ h₂)).X q) ≅
    row R M (fun t s => F s t) h₁ q :=
  Hom.isoOfComponents (fun p =>
    (switch R M F p q).toModuleIso)
    (fun p r h => by
      obtain rfl : p+1=r := h
      change _ ≫ (row R M (fun t s => F s t) h₁ q).d p (p+1)=
        ((complex R M F h₁ h₂).d p (p+1)).f q ≫ _
      rw [complex_d,row_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)
lemma row_bounded (p : ℕ) (hp : Fintype.card ι<p) : IsZero ((complex R M F h₁ h₂).X p) := by
  rw [IsZero.iff_id_eq_zero]
  apply Hom.ext
  funext q
  let : Subsingleton (term R M F p q) := term_zero_horizontal R M F p q hp
  exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (term R M F p q))).eq_of_src _ _
lemma column_bounded (q : ℕ) (hq : Fintype.card κ<q) : IsZero ((flip (complex R M F h₁ h₂)).X q) :=
  (row_bounded R M (fun t s => F s t) h₂ h₁ q hq).of_iso (columnIso R M F h₁ h₂ q)
 

def coverComparison
    (hr : ∀ p,0<p → ∀ s : powersetCard ι p,
      (AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).Acyclic)
    (hc : ∀ q,0<q → ∀ t : powersetCard κ q,
      (AlternatingCech.sortedComplex R M (fun s => F s t.val) (h₁ t.val)).Acyclic)
    (i : ℤ) :
    (((complex R M F h₁ h₂).X 0).extend ComplexShape.embeddingUpNat).homology i ≅
      (((flip (complex R M F h₁ h₂)).X 0).extend ComplexShape.embeddingUpNat).homology i :=
  ComplexExtension.natDoubleCoverIso (complex R M F h₁ h₂)
    (Fintype.card ι+1) (Fintype.card κ+1)
    (fun p hp => row_bounded R M F h₁ h₂ p (by omega))
    (fun q hq => column_bounded R M F h₁ h₂ q (by omega))
    (fun p hp => row_exact R M F h₂ p (hr p hp))
    (fun q hq j => (row_exact R M (fun t s => F s t) h₁ q (hc q hq) j).of_iso
      (columnIso R M F h₁ h₂ q).symm) i
end


open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))
def emptyIndex : powersetCard ι 0 := ⟨∅,Finset.card_empty⟩
omit [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ] in
lemma zeroIndex_eq (s : powersetCard ι 0) : s=emptyIndex := by
  apply Subtype.ext
  exact Finset.card_eq_zero.mp s.property
 

def rowZeroEquiv (q : ℕ) : term R M F 0 q ≃ₗ[R] AlternatingCech.sorted R M (F ∅) q where
  toFun f := f emptyIndex
  invFun f s := (zeroIndex_eq s).symm ▸ f
  left_inv f := by funext s;cases zeroIndex_eq s;rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' r f := rfl
def rowZeroIso : ((complex R M F h₁ h₂).X 0) ≅
    AlternatingCech.sortedComplex R M (F ∅) (h₂ ∅) :=
  HomologicalComplex.Hom.isoOfComponents (fun q => (rowZeroEquiv R M F q).toModuleIso)
    (fun q r h => by
      obtain rfl : q+1=r := h
      rw [AlternatingCech.sortedComplex_d]
      change (ModuleCat.ofHom (rowZeroEquiv R M F q).toLinearMap) ≫ _ =
        (row R M F h₂ 0).d q (q+1) ≫ _
      rw [row_d]
      rfl)
def columnZeroIso : ((flip (complex R M F h₁ h₂)).X 0) ≅
    AlternatingCech.sortedComplex R M (fun s => F s ∅) (h₁ ∅) :=
  (columnIso R M F h₁ h₂ 0) ≪≫ rowZeroIso R M (fun t s => F s t) h₂ h₁
end Lech.DoubleCech


namespace Lech.AlternatingCech
universe u v
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type v} [DecidableEq ι]
 

def zeroAugmentation (F : Finset ι → Submodule R M) (s : Finset ι) : Submodule R M :=
  if s=∅ then ⊥ else F s
lemma zeroAugmentation_mono (F : Finset ι → Submodule R M) (hF : Monotone F) :
    Monotone (zeroAugmentation R M F) := by
  intro s t hst
  by_cases hs : s=∅
  · simp [zeroAugmentation,hs]
  · have ht : t≠∅ := fun ht => hs (Finset.subset_empty.mp (ht ▸ hst))
    simpa only [zeroAugmentation,ite_eq_right hs,ite_eq_right ht] using hF hst
end Lech.AlternatingCech


namespace Lech.DoubleCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))
 

def puncture (s : Finset ι) (t : Finset κ) : Submodule R M :=
  if s=∅ ∧ t=∅ then ⊥ else F s t
include h₁ in
omit [Fintype ι] [Fintype κ] in
lemma puncture_left_mono (t : Finset κ) : Monotone (fun s => puncture R M F s t) := by
  intro s s' hs
  by_cases he : s=∅ ∧ t=∅
  · simp only [puncture,ite_eq_left he,bot_le]
  · have he' : ¬(s'=∅ ∧ t=∅) := by
      rintro ⟨rfl,ht⟩
      exact he ⟨Finset.subset_empty.mp hs,ht⟩
    simpa only [puncture,ite_eq_right he,ite_eq_right he'] using h₁ t hs
include h₂ in
omit [Fintype ι] [Fintype κ] in
lemma puncture_right_mono (s : Finset ι) : Monotone (puncture R M F s) := by
  intro t t' ht
  by_cases he : s=∅ ∧ t=∅
  · simp only [puncture,ite_eq_left he,bot_le]
  · have he' : ¬(s=∅ ∧ t'=∅) := by
      rintro ⟨hs,rfl⟩
      exact he ⟨hs,Finset.subset_empty.mp ht⟩
    simpa only [puncture,ite_eq_right he,ite_eq_right he'] using h₂ s ht
omit [Fintype ι] [Fintype κ] in
lemma puncture_row (s : Finset ι) (hs : s.Nonempty) : puncture R M F s=F s := by
  funext t
  simp only [puncture,hs.ne_empty,false_and,ite_false]
omit [Fintype ι] [Fintype κ] in
lemma puncture_column (t : Finset κ) (ht : t.Nonempty) :
    (fun s => puncture R M F s t)=(fun s => F s t) := by
  funext s
  simp only [puncture,ht.ne_empty,and_false,ite_false]
 

def unaugmentedCoverComparison
    (hr : ∀ p,0<p → ∀ s : powersetCard ι p,
      (AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).Acyclic)
    (hc : ∀ q,0<q → ∀ t : powersetCard κ q,
      (AlternatingCech.sortedComplex R M (fun s => F s t.val) (h₁ t.val)).Acyclic)
    (i : ℤ) :
    ((AlternatingCech.sortedComplex R M (AlternatingCech.zeroAugmentation R M (F ∅))
      (AlternatingCech.zeroAugmentation_mono R M (F ∅) (h₂ ∅))).extend ComplexShape.embeddingUpNat).homology i ≅
    ((AlternatingCech.sortedComplex R M (AlternatingCech.zeroAugmentation R M (fun s => F s ∅))
      (AlternatingCech.zeroAugmentation_mono R M (fun s => F s ∅) (h₁ ∅))).extend ComplexShape.embeddingUpNat).homology i := by
  let G := puncture R M F
  let g₁ := puncture_left_mono R M F h₁
  let g₂ := puncture_right_mono R M F h₂
  have gr : ∀ p,0<p → ∀ s : powersetCard ι p,(AlternatingCech.sortedComplex R M (G s.val) (g₂ s.val)).Acyclic := by
    intro p hp s
    have he := puncture_row R M F s.val (Finset.card_pos.mp (s.property.symm ▸ hp))
    simpa only [G,he] using hr p hp s
  have gc : ∀ q,0<q → ∀ t : powersetCard κ q,(AlternatingCech.sortedComplex R M (fun s => G s t.val) (g₁ t.val)).Acyclic := by
    intro q hq t
    have he := puncture_column R M F t.val (Finset.card_pos.mp (t.property.symm ▸ hq))
    simpa only [G,he] using hc q hq t
  have e := (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
    ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso (rowZeroIso R M G g₁ g₂).symm) ≪≫
      coverComparison R M G g₁ g₂ gr gc i ≪≫
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
      ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso (columnZeroIso R M G g₁ g₂))
  change ((AlternatingCech.sortedComplex R M (G ∅) (g₂ ∅)).extend ComplexShape.embeddingUpNat).homology i ≅
    ((AlternatingCech.sortedComplex R M (fun s => G s ∅) (g₁ ∅)).extend ComplexShape.embeddingUpNat).homology i at e
  have e₁ : G ∅=AlternatingCech.zeroAugmentation R M (F ∅) := by
    funext t
    simp only [G,puncture,AlternatingCech.zeroAugmentation,true_and]
  have e₂ : (fun s => G s ∅)=AlternatingCech.zeroAugmentation R M (fun s => F s ∅) := by
    funext s
    simp only [G,puncture,AlternatingCech.zeroAugmentation,and_true]
  simpa only [e₁,e₂] using e
end Lech.DoubleCech

end

end OAI
