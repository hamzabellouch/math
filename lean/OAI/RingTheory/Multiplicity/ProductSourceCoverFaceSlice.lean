import Mathlib
import OAI.RingTheory.Multiplicity.AlternatingCechPrismPrimitive

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
open AlternatingCech
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma faceSlice_kernel (k : ℤ) (m : Fin n → ℤ) (p : ℕ)
    (f : Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p)
    (hf : f∈cochains R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons k m)) p) :
    faceSlice R n k p f=0 ↔
      f∈cochains R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons (k-1) m)) p := by
  constructor
  · intro hz a
    apply (neighbor_mem_iff R n k m _ _ (hf a)).mpr
    intro ht
    have ha : trueFace n ∘ (Fin.tail ∘ a)=a := by
      funext i j
      refine Fin.cases ?_ (fun _ => rfl) j
      exact (ht (a i) (by simp [FiniteCoverCech.intersection])).symm
    have hh := congrArg (fun g => evaluation R (LaurentModule R n) p g (Fin.tail ∘ a)) hz
    rw [faceSlice_eval,ha,map_zero] at hh
    exact hh
  · intro hl
    apply evaluation_injective R (LaurentModule R n) p
    apply funext;intro a
    rw [faceSlice_eval,map_zero]
    apply (neighbor_mem_iff R n k m _ _ (hf (trueFace n ∘ a))).mp (hl (trueFace n ∘ a))
    intro σ hσ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hσ
    rfl
abbrev divisorCochains (m : Fin n → ℤ) (p : ℕ) :=
  cochains R (LaurentModule R n) (sections R n m) p
def divisorInclusion (k : ℤ) (m : Fin n → ℤ) (p : ℕ) :
    divisorCochains R (n+1) (Fin.cons (k-1) m) p →ₗ[R] divisorCochains R (n+1) (Fin.cons k m) p :=
  Submodule.inclusion (by
    intro f hf a
    exact neighbor_sections_le R n k m _ (hf a))
def divisorRestriction (k : ℤ) (m : Fin n → ℤ) (p : ℕ) :
    divisorCochains R (n+1) (Fin.cons k m) p →ₗ[R] divisorCochains R n m p :=
  (faceSlice R n k p).restrict (fun _ h => faceSlice_mem R n k m p _ h)
def divisorSection (k : ℤ) (m : Fin n → ℤ) (p : ℕ) (hp : 0<p) :
    divisorCochains R n m p →ₗ[R] divisorCochains R (n+1) (Fin.cons k m) p :=
  (faceLift R n k p).restrict (fun _ h => faceLift_mem R n k m p hp _ h)
lemma divisorRestriction_section (k : ℤ) (m : Fin n → ℤ) (p : ℕ) (hp : 0<p)
    (f : divisorCochains R n m p) :
    divisorRestriction R n k m p (divisorSection R n k m p hp f)=f := by
  exact Subtype.ext (faceSlice_lift R n k p f.val)
lemma divisorInclusion_injective (k : ℤ) (m : Fin n → ℤ) (p : ℕ) :
    Function.Injective (divisorInclusion R n k m p) := by
  intro f g h
  apply Subtype.ext
  exact congrArg (fun z : divisorCochains R (n+1) (Fin.cons k m) p => z.val) h
lemma divisorRestriction_surjective (k : ℤ) (m : Fin n → ℤ) (p : ℕ) (hp : 0<p) :
    Function.Surjective (divisorRestriction R n k m p) := by
  intro f
  exact ⟨divisorSection R n k m p hp f,divisorRestriction_section R n k m p hp f⟩
lemma divisorRestriction_comp (k : ℤ) (m : Fin n → ℤ) (p : ℕ) :
    (divisorRestriction R n k m p).comp (divisorInclusion R n k m p)=0 := by
  apply LinearMap.ext;intro f
  apply Subtype.ext
  exact (faceSlice_kernel R n k m p f.val
    (divisorInclusion R n k m p f).property).mpr f.property
lemma divisorCochains_exact (k : ℤ) (m : Fin n → ℤ) (p : ℕ)
    (f : divisorCochains R (n+1) (Fin.cons k m) p)
    (hf : divisorRestriction R n k m p f=0) :
    ∃ g, divisorInclusion R n k m p g=f := by
  have hm := (faceSlice_kernel R n k m p f.val f.property).mp (congrArg Subtype.val hf)
  exact ⟨⟨f.val,hm⟩,rfl⟩

end Lech.ProductSourceCover


namespace Lech.AlternatingCech
open scoped BigOperators
open Set
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
local instance faceSliceSortedDecEq : DecidableEq ι := Classical.decEq ι
def delete {n : ℕ} (s : powersetCard ι (n+1)) (i : Fin (n+1)) : powersetCard ι n :=
  powersetCard.ofFinEmbEquiv ((Fin.succAboveOrderEmb i).trans
    (powersetCard.ofFinEmbEquiv.symm s))
omit [Fintype ι] in
lemma delete_sorted {n : ℕ} (s : powersetCard ι (n+1)) (i : Fin (n+1)) :
    powersetCard.ofFinEmbEquiv.symm (delete s i)=
      (Fin.succAboveOrderEmb i).trans (powersetCard.ofFinEmbEquiv.symm s) :=
  powersetCard.ofFinEmbEquiv.symm_apply_apply _
omit [Fintype ι] in
lemma delete_subset {n : ℕ} (s : powersetCard ι (n+1)) (i : Fin (n+1)) :
    (delete s i).val ⊆ s.val := by
  intro j hj
  have hj' : j∈Set.range (powersetCard.ofFinEmbEquiv.symm (delete s i)) :=
    (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ _).mpr hj
  rw [delete_sorted] at hj'
  obtain ⟨k,rfl⟩ := hj'
  exact (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨i.succAbove k,rfl⟩
lemma sortedCoordinates_delta (n : ℕ) (f : Alt R M (ι := ι) n) (s : powersetCard ι (n+1)) :
    sortedCoordinates R M (n+1) (delta R M n f) s=
      ∑ i : Fin (n+1),(-1:ℤ)^i.val • sortedCoordinates R M n f (delete s i) := by
  rw [sortedCoordinates_apply]
  simp only [delta,LinearMap.coe_mk,AddHom.coe_mk,AlternatingMap.alternatizeUncurryFin_apply,
    LinearMap.smulRight_apply,epsilon_basis,one_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [sortedCoordinates_apply]
  change f (fun j => basis R (powersetCard.ofFinEmbEquiv.symm s (i.succAbove j)))=
    f (fun j => basis R (powersetCard.ofFinEmbEquiv.symm (delete s i) j))
  rw [delete_sorted]
  rfl
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
abbrev sorted (n : ℕ) := ∀ s : powersetCard ι n,F s.val
 
def sortedDelta (n : ℕ) : sorted R M F n →ₗ[R] sorted R M F (n+1) where
  toFun f s := ∑ i : Fin (n+1),(-1:ℤ)^i.val •
    Submodule.inclusion (hF (delete_subset s i)) (f (delete s i))
  map_add' f g := by ext s;simp [Finset.sum_add_distrib,smul_add]
  map_smul' r f := by
    funext s
    simp only [Pi.smul_apply,map_smul,Finset.smul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
lemma cochainsSorted_delta (n : ℕ) (f : cochains R M F n) :
    cochainsSorted R M F (n+1) (differential R M F hF n f)=
      sortedDelta R M F hF n (cochainsSorted R M F n f) := by
  ext s
  change sortedCoordinates R M (n+1) (delta R M n f.val) s=_
  rw [sortedCoordinates_delta]
  simp only [sortedDelta,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum]
  rfl
lemma sortedDelta_square (n : ℕ) (f : sorted R M F n) :
    sortedDelta R M F hF (n+1) (sortedDelta R M F hF n f)=0 := by
  obtain ⟨g,rfl⟩ := (cochainsSorted R M F n).surjective f
  rw [←cochainsSorted_delta,←cochainsSorted_delta,differential_square,map_zero]
variable (q : ι → R) (hq : Ideal.span (Set.range q)=⊤)
variable (hclear : ∀ (s : Finset ι) (j : ι) (x : M),x∈F (insert j s) → ∃ N : ℕ,q j^N • x∈F s)
include hq hclear in
theorem sortedExact (n : ℕ) :
    Function.Exact (sortedDelta R M F hF n) (sortedDelta R M F hF (n+1)) := by
  intro f
  constructor
  · intro hf
    obtain ⟨g,rfl⟩ := (cochainsSorted R M F (n+1)).surjective f
    rw [←cochainsSorted_delta] at hf
    have hg : differential R M F hF (n+1) g=0 :=
      (cochainsSorted R M F (n+2)).injective (hf.trans (map_zero _).symm)
    obtain ⟨x,hx⟩ := exact R M F q hq hclear n g (congrArg Subtype.val hg)
    exact ⟨cochainsSorted R M F n x,by rw [←cochainsSorted_delta];exact congrArg _ (Subtype.ext hx)⟩
  · rintro ⟨g,rfl⟩
    exact sortedDelta_square R M F hF n g
end Lech.AlternatingCech


namespace Lech.DoubleCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))
abbrev term (p q : ℕ) := ∀ s : powersetCard ι p,∀ t : powersetCard κ q,F s.val t.val
 
def vertical (p q : ℕ) : term R M F p q →ₗ[R] term R M F p (q+1) where
  toFun f s := AlternatingCech.sortedDelta R M (F s.val) (h₂ s.val) q (f s)
  map_add' f g := by funext s;exact map_add _ (f s) (g s)
  map_smul' r f := by funext s;exact map_smul _ r (f s)
def horizontal (p q : ℕ) : term R M F p q →ₗ[R] term R M F (p+1) q where
  toFun f s t := AlternatingCech.sortedDelta R M (fun s => F s t.val) (h₁ t.val) p
    (fun s => f s t) s
  map_add' f g := by funext s t; exact congrFun (map_add _ (fun s => f s t) (fun s => g s t)) s
  map_smul' r f := by funext s t;exact congrFun ((AlternatingCech.sortedDelta R M (fun s => F s t.val) (h₁ t.val) p).map_smul r (fun s => f s t)) s
omit [Fintype ι] [LinearOrder ι] in
lemma vertical_square (p q : ℕ) (f : term R M F p q) :
    vertical R M F h₂ p (q+1) (vertical R M F h₂ p q f)=0 := by
  funext s
  exact AlternatingCech.sortedDelta_square R M (F s.val) (h₂ s.val) q (f s)
omit [Fintype κ] [LinearOrder κ] in
lemma horizontal_square (p q : ℕ) (f : term R M F p q) :
    horizontal R M F h₁ (p+1) q (horizontal R M F h₁ p q f)=0 := by
  funext s t
  exact congrFun (AlternatingCech.sortedDelta_square R M (fun s => F s t.val) (h₁ t.val)
    p (fun s => f s t)) s
omit [Fintype ι] [Fintype κ] in
lemma horizontal_vertical (p q : ℕ) (f : term R M F p q) :
    vertical R M F h₂ (p+1) q (horizontal R M F h₁ p q f)=
      horizontal R M F h₁ p (q+1) (vertical R M F h₂ p q f) := by
  ext s t
  simp only [vertical,horizontal,AlternatingCech.sortedDelta,LinearMap.coe_mk,AddHom.coe_mk,
    map_sum,map_zsmul,Finset.smul_sum,Submodule.coe_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _
 
def row (p : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun q => ModuleCat.of R (term R M F p q))
    (fun q => ModuleCat.ofHom (vertical R M F h₂ p q)) (fun q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact vertical_square R M F h₂ p q)
omit [Fintype ι] [LinearOrder ι] in
lemma row_d (p q : ℕ) : (row R M F h₂ p).d q (q+1)=ModuleCat.ofHom (vertical R M F h₂ p q) := by
  change CochainComplex.of.d (fun q => ModuleCat.of R (term R M F p q))
    (fun q => ModuleCat.ofHom (vertical R M F h₂ p q)) q (q+1)=_
  exact CochainComplex.of_d _ _ q
 
def rowMap (p : ℕ) : row R M F h₂ p ⟶ row R M F h₂ (p+1) :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom (horizontal R M F h₁ p q)) (fun q => by
    rw [row_d,row_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact horizontal_vertical R M F h₁ h₂ p q f)
lemma rowMap_square (p : ℕ) : rowMap R M F h₁ h₂ p ≫ rowMap R M F h₁ h₂ (p+1)=0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact horizontal_square R M F h₁ p q
 

def complex : CochainComplex (CochainComplex (ModuleCat.{u} R) ℕ) ℕ :=
  CochainComplex.of (row R M F h₂) (rowMap R M F h₁ h₂) (rowMap_square R M F h₁ h₂)
omit [LinearOrder ι] [Fintype κ] [LinearOrder κ] in
lemma term_zero_horizontal (p q : ℕ) (hp : Fintype.card ι<p) :
    Subsingleton (term R M F p q) := by
  refine ⟨fun f g => funext fun s => ?_⟩
  have hh := Finset.card_le_univ s.val
  have hs : s.val.card=p := s.property
  omega
end Lech.DoubleCech


namespace Lech.ComplexExtension
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
variable (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ)
lemma negative_zero (n : ℕ) : IsZero ((K.extend ComplexShape.embeddingUpNat).X (Int.negSucc n)) := by
  apply K.isZero_extend_X
  intro m hm
  change (m:ℤ)=Int.negSucc n at hm
  omega
 

def mapExtendXIso (i : ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)).X i ≅
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat).X i :=
  match i with
  | .ofNat n => F.mapIso (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl) ≪≫
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).symm
  | .negSucc n => (F.map_isZero (negative_zero K n)).isoZero ≪≫
      (negative_zero ((F.mapHomologicalComplex (.up ℕ)).obj K) n).isoZero.symm

omit [Preadditive C] [HasZeroObject C] [Preadditive D] [HasZeroObject D] [F.Additive] in
private lemma map_conjugation_square {X₁ X₂ Y₁ Y₂ : C} {Z₁ Z₂ : D}
    (e₁ : X₁ ≅ X₂) (e₂ : Y₁ ≅ Y₂) (g₁ : Z₁ ≅ F.obj X₂) (g₂ : Z₂ ≅ F.obj Y₂)
    (f : X₂ ⟶ Y₂) :
    (F.mapIso e₁ ≪≫ g₁.symm).hom ≫ (g₁.hom ≫ F.map f ≫ g₂.inv) =
      F.map (e₁.hom ≫ f ≫ e₂.inv) ≫ (F.mapIso e₂ ≪≫ g₂.symm).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]

lemma mapExtendXIso_comm (i j : ℤ) :
    (mapExtendXIso F K i).hom ≫ (((F.mapHomologicalComplex (.up ℕ)).obj K).extend
      ComplexShape.embeddingUpNat).d i j =
    ((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)).d i j ≫
      (mapExtendXIso F K j).hom := by
  cases i with
  | negSucc n => exact (F.map_isZero (negative_zero K n)).eq_of_src _ _
  | ofNat n =>
    cases j with
    | negSucc m => exact (negative_zero ((F.mapHomologicalComplex (.up ℕ)).obj K) m).eq_of_tgt _ _
    | ofNat m =>
      dsimp only [mapExtendXIso,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom]
      erw [extend_d_eq _ ComplexShape.embeddingUpNat (i := n) (j := m)
        (show ComplexShape.embeddingUpNat.f n=(n:ℤ) from rfl)
        (show ComplexShape.embeddingUpNat.f m=(m:ℤ) from rfl)]
      change _ = F.map ((K.extend ComplexShape.embeddingUpNat).d (n:ℤ) (m:ℤ)) ≫ _
      erw [extend_d_eq _ ComplexShape.embeddingUpNat (i := n) (j := m)
        (show ComplexShape.embeddingUpNat.f n=(n:ℤ) from rfl)
        (show ComplexShape.embeddingUpNat.f m=(m:ℤ) from rfl)]
      exact map_conjugation_square F
        (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
        (K.extendXIso ComplexShape.embeddingUpNat (i := m) rfl)
        (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso
          ComplexShape.embeddingUpNat (i := n) rfl)
        (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso
          ComplexShape.embeddingUpNat (i := m) rfl)
        (K.d n m)
def mapExtendIso :
    (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat :=
  Hom.isoOfComponents (mapExtendXIso F K) (fun i j _ => mapExtendXIso_comm F K i j)
end Lech.ComplexExtension


namespace Lech.BicomplexTotal

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable (F : Row (R := R))
abbrev singleZero := (single (Row (R := R)) (.up ℤ) 0).obj F
abbrev totalSingleZero := total (singleZero F) (.up ℤ)
def intoSingle (i : ℤ) : F.X i ⟶ (totalSingleZero F).X i :=
  (singleObjXSelf (.up ℤ) 0 F).inv.f i ≫ ιTotal (singleZero F) (.up ℤ) 0 i i (by simp)
def outOfSingle (i : ℤ) : (totalSingleZero F).X i ⟶ F.X i :=
  totalDesc (singleZero F) (fun p q hpq => if hp : p=0 then
    have hq : q=i := by change p+q=i at hpq; omega
    (singleObjXIsoOfEq (.up ℤ) 0 F p hp).hom.f q ≫ (F.XIsoOfEq hq).hom
    else 0)
lemma into_out_single (i : ℤ) : intoSingle F i ≫ outOfSingle F i=𝟙 _ := by
  simp only [intoSingle,outOfSingle,Category.assoc,ι_totalDesc,dite_true,
    XIsoOfEq_rfl,Iso.refl_hom,Category.comp_id]
  rw [←HomologicalComplex.comp_f]
  simp only [singleObjXSelf,Iso.inv_hom_id,HomologicalComplex.id_f]
lemma out_into_single (i : ℤ) : outOfSingle F i ≫ intoSingle F i=𝟙 _ := by
  apply total.hom_ext
  intro p q hpq
  by_cases hp : p=0
  · subst p
    have hq : q=i := by change 0+q=i at hpq; omega
    subst q
    simp only [outOfSingle,ι_totalDesc_assoc,dite_true,XIsoOfEq_rfl,
      Iso.refl_hom,Category.comp_id]
    dsimp only [intoSingle]
    rw [←Category.assoc,←HomologicalComplex.comp_f]
    simp only [singleObjXSelf,Iso.hom_inv_id,HomologicalComplex.id_f,Category.id_comp]
  · have hzero := (eval (ModuleCat.{u} R) (.up ℤ) q).map_isZero
      (isZero_single_obj_X (.up ℤ) 0 F p hp)
    exact hzero.eq_of_src _ _
def singleXIso (i : ℤ) : F.X i ≅ (totalSingleZero F).X i where
  hom := intoSingle F i
  inv := outOfSingle F i
  hom_inv_id := into_out_single F i
  inv_hom_id := out_into_single F i
lemma single_d₁ (p q j : ℤ) : d₁ (singleZero F) (.up ℤ) p q j=0 := by
  by_cases h : (p+1)+q=j
  · rw [d₁_eq _ _ (show (ComplexShape.up ℤ).Rel p (p+1) from rfl) q j h]
    simp
  · rw [d₁_eq_zero' _ _ (show (ComplexShape.up ℤ).Rel p (p+1) from rfl) q j h]
lemma into_single_comm (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    intoSingle F i ≫ (totalSingleZero F).d i j=F.d i j ≫ intoSingle F j := by
  simp only [intoSingle,Category.assoc,total_d,Preadditive.comp_add,
    ι_D₁,ι_D₂,single_d₁,comp_zero,zero_add]
  rw [d₂_eq _ _ 0 hij j (by simp)]
  dsimp
  simp only [one_smul]
  rw [←Category.assoc,HomologicalComplex.Hom.comm,Category.assoc]
 

def singleZeroIso : F ≅ totalSingleZero F :=
  Hom.isoOfComponents (singleXIso F) (fun _ _ hij => into_single_comm F _ _ hij)
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable (F : Row (R := R))
 
def singleIso (j : ℤ) :
    total ((single (Row (R := R)) (.up ℤ) j).obj F) (.up ℤ) ≅ F⟦-j⟧ :=
  (functor (R := R)).mapIso
    (((CochainComplex.singleFunctors (Row (R := R))).shiftIso (-j) j 0 (by omega)).app F).symm ≪≫
    totalShift₁Iso (singleZero F) (-j) ≪≫
    (shiftFunctor (Row (R := R)) (-j)).mapIso (singleZeroIso F).symm

def singleHomologyIso (j i : ℤ) :
    (total ((single (Row (R := R)) (.up ℤ) j).obj F) (.up ℤ)).homology i ≅
      F.homology (-j+i) :=
  (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso (singleIso F j) ≪≫
    (((homologyFunctor (ModuleCat.{u} R) (.up ℤ) (0:ℤ)).shiftIso (-j) i _ rfl).app F)


theorem acyclic_of_rows (m : ℤ) (N : ℕ) (K : Double (R := R))
    (hb : ∀ j, j < m ∨ m + N ≤ j → IsZero (K.X j))
    (hr : ∀ j i, IsZero ((K.X j).homology i)) (i : ℤ) :
    IsZero ((total K (.up ℤ)).homology i) := by
  apply devissage (IsZero (C := ModuleCat.{u} R)) m N K i hb
  intro j
  exact (hr j (-j+i)).of_iso (singleHomologyIso (K.X j) j i)
end Lech.BicomplexTotal


namespace Lech.FiniteComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]
variable (F : CochainComplex C ℤ) (n : ℤ)
  (hn : ∀ i, i < n → IsZero (F.X i))

noncomputable def bottomProjection : F ⟶ (single C (.up ℤ) n).obj (F.X n) :=
  mkHomToSingle (𝟙 _) (by
    intro i hi
    have hi' : i+1=n := hi
    exact (hn i (by omega)).eq_of_src _ _)

instance bottomProjection_epi : Epi (bottomProjection F n hn) := by
  apply epi_of_epi_f
  intro i
  by_cases hi : i=n
  · subst i
    dsimp [bottomProjection]
    rw [mkHomToSingle_f,Category.id_comp]
    infer_instance
  · exact (isZero_single_obj_X _ _ _ _ hi).epi _

noncomputable def dropBottom : CochainComplex C ℤ := kernel (bottomProjection F n hn)

noncomputable def bottomShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (kernel.ι _) (bottomProjection F n hn) (kernel.condition _)

lemma bottomShortExact : (bottomShortComplex F n hn).ShortExact where
  exact := ShortComplex.exact_kernel _
  mono_f := inferInstanceAs (Mono (kernel.ι (bottomProjection F n hn)))
  epi_g := bottomProjection_epi F n hn

lemma bottomShortExact_eval (i : ℤ) :
    ((bottomShortComplex F n hn).map (eval C (.up ℤ) i)).ShortExact :=
  (bottomShortExact F n hn).map_of_exact _

lemma bottomProjection_f_isIso : IsIso ((bottomProjection F n hn).f n) := by
  dsimp [bottomProjection]
  rw [mkHomToSingle_f,Category.id_comp]
  infer_instance

lemma dropBottom_X_bottom : IsZero ((dropBottom F n hn).X n) := by
  apply (bottomShortExact_eval F n hn n).isIso_g_iff.mp
  exact bottomProjection_f_isIso F n hn

lemma dropBottom_ι_isIso (i : ℤ) (hi : i ≠ n) :
    IsIso ((kernel.ι (bottomProjection F n hn)).f i) := by
  apply (bottomShortExact_eval F n hn i).isIso_f_iff.mpr
  exact isZero_single_obj_X (.up ℤ) n (F.X n) i hi

noncomputable def dropBottomXIso (i : ℤ) (hi : i ≠ n) :
    (dropBottom F n hn).X i ≅ F.X i := by
  exact @asIso _ _ _ _ ((kernel.ι (bottomProjection F n hn)).f i)
    (dropBottom_ι_isIso F n hn i hi)

noncomputable def bottomSplitting (i : ℤ) :
    ((bottomShortComplex F n hn).map (eval C (.up ℤ) i)).Splitting := by
  let S := (bottomShortComplex F n hn).map (eval C (.up ℤ) i)
  have hS : S.ShortExact := bottomShortExact_eval F n hn i
  by_cases hi : i=n
  · subst i
    haveI : IsIso S.g := bottomProjection_f_isIso F n hn
    exact ShortComplex.Splitting.ofExactOfSection S hS.exact (inv S.g)
      (by simp) hS.mono_f
  · haveI : IsIso S.f := dropBottom_ι_isIso F n hn i hi
    exact ShortComplex.Splitting.ofExactOfRetraction S hS.exact (inv S.f)
      (by simp) hS.epi_g

lemma dropBottom_boundedBelow : ∀ i, i < n+1 → IsZero ((dropBottom F n hn).X i) := by
  intro i hi
  by_cases hin : i=n
  · subst i
    exact dropBottom_X_bottom F n hn
  · exact (hn i (by omega)).of_iso (dropBottomXIso F n hn i hin)

variable {G : CochainComplex C ℤ} (hg : ∀ i, i < n → IsZero (G.X i))
  (f : F ⟶ G)

@[reassoc] lemma bottomProjection_naturality :
    bottomProjection F n hn ≫ (single C (.up ℤ) n).map (f.f n) =
      f ≫ bottomProjection G n hg := by
  apply Hom.ext
  funext i
  by_cases hi : i=n
  · subst i
    simp [bottomProjection,single_map_f_self]
  · exact (isZero_single_obj_X (.up ℤ) n (G.X n) i hi).eq_of_tgt _ _

noncomputable def dropBottomMap : dropBottom F n hn ⟶ dropBottom G n hg :=
  kernel.map _ _ f ((single C (.up ℤ) n).map (f.f n))
    (bottomProjection_naturality F n hn hg f)

@[reassoc (attr := simp)] lemma dropBottomMap_ι :
    dropBottomMap F n hn hg f ≫ kernel.ι (bottomProjection G n hg) =
      kernel.ι (bottomProjection F n hn) ≫ f := by
  exact kernel.lift_ι _ _ _

noncomputable def bottomShortComplexMap :
    bottomShortComplex F n hn ⟶ bottomShortComplex G n hg where
  τ₁ := dropBottomMap F n hn hg f
  τ₂ := f
  τ₃ := (single C (.up ℤ) n).map (f.f n)
  comm₁₂ := dropBottomMap_ι F n hn hg f
  comm₂₃ := (bottomProjection_naturality F n hn hg f).symm
end Lech.FiniteComplex

end

end OAI
