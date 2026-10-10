import Mathlib
import OAI.RingTheory.Multiplicity.LechConnectingIso

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
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
abbrev unaugmentedComplex := sortedComplex R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF)
def unaugmentedInclusion (p : ℕ) : sorted R M (zeroAugmentation R M F) p →ₗ[R] sorted R M F p where
  toFun f s := ⟨f s,by
    have h := (f s).property
    by_cases hs : s.val=∅
    · have hz : (f s:M)=0 := by simpa only [zeroAugmentation,ite_eq_left hs,Submodule.mem_bot] using h
      rw [hz];exact (F s.val).zero_mem
    · simpa only [zeroAugmentation,ite_eq_right hs] using h⟩
  map_add' f g := rfl
  map_smul' r f := rfl
omit [Fintype ι] in
lemma unaugmentedInclusion_injective (p : ℕ) : Function.Injective (unaugmentedInclusion R M F p) := by
  intro f g h
  ext s
  exact congrArg (fun f : sorted R M F p => (f s:M)) h
omit [Fintype ι] in
lemma unaugmentedInclusion_delta (p : ℕ) (f : sorted R M (zeroAugmentation R M F) p) :
    unaugmentedInclusion R M F (p+1) (sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) p f)=
      sortedDelta R M F hF p (unaugmentedInclusion R M F p f) := by
  ext s
  simp only [unaugmentedInclusion,sortedDelta,LinearMap.coe_mk,AddHom.coe_mk,
    Submodule.coe_sum,Submodule.coe_smul_of_tower]
  rfl
omit [Fintype ι] in
lemma unaugmentedInclusion_surjective (p : ℕ) (hp : 0<p) : Function.Surjective (unaugmentedInclusion R M F p) := by
  intro f
  refine ⟨(fun s => ⟨f s,?_⟩),rfl⟩
  have hs : s.val≠∅ := (Finset.card_pos.mp (s.property.symm ▸ hp)).ne_empty
  simpa only [zeroAugmentation,ite_eq_right hs] using (f s).property
def unaugmentedEquiv (p : ℕ) (hp : 0<p) : sorted R M (zeroAugmentation R M F) p ≃ₗ[R] sorted R M F p :=
  LinearEquiv.ofBijective (unaugmentedInclusion R M F p)
    ⟨unaugmentedInclusion_injective R M F p,unaugmentedInclusion_surjective R M F p hp⟩
lemma unaugmented_isZero_zero : IsZero ((unaugmentedComplex R M F hF).X 0) := by
  have : Subsingleton (sorted R M (zeroAugmentation R M F) 0) := ⟨fun f g => by
    ext s
    rw [DoubleCech.zeroIndex_eq s]
    have hf : (f DoubleCech.emptyIndex:M)=0 := by simpa [DoubleCech.emptyIndex, zeroAugmentation] using (f DoubleCech.emptyIndex).property
    have hg : (g DoubleCech.emptyIndex:M)=0 := by simpa [DoubleCech.emptyIndex, zeroAugmentation] using (g DoubleCech.emptyIndex).property
    exact hf.trans hg.symm⟩
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (sorted R M (zeroAugmentation R M F) 0))
 

lemma unaugmented_exactAt (p : ℕ) (h : (sortedComplex R M F hF).ExactAt (p+2)) :
    (unaugmentedComplex R M F hF).ExactAt (p+2) := by
  apply ((unaugmentedComplex R M F hF).exactAt_iff' (i:=p+1) (j:=p+2) (k:=p+3) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change sorted R M (zeroAugmentation R M F) (p+2) at f
  change ((unaugmentedComplex R M F hF).d (p+2) (p+3)).hom f=0 at hf
  rw [sortedComplex_d] at hf
  change sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) (p+2) f=0 at hf
  have he := ((sortedComplex R M F hF).exactAt_iff' (i:=p+1) (j:=p+2) (k:=p+3) (by simp) (by simp)).mp h
  rw [ShortComplex.moduleCat_exact_iff] at he
  obtain ⟨g,hg⟩ := he (unaugmentedInclusion R M F (p+2) f) (by
    change ((sortedComplex R M F hF).d (p+2) (p+3)).hom _=0
    rw [sortedComplex_d]
    change sortedDelta R M F hF (p+2) (unaugmentedInclusion R M F (p+2) f)=0
    rw [←unaugmentedInclusion_delta R M F hF,hf,map_zero])
  change sorted R M F (p+1) at g
  change ((sortedComplex R M F hF).d (p+1) (p+2)).hom g = _ at hg
  rw [sortedComplex_d] at hg
  obtain ⟨g',rfl⟩ := unaugmentedInclusion_surjective R M F (p+1) (by omega) g
  refine ⟨g',?_⟩
  change ((unaugmentedComplex R M F hF).d (p+1) (p+2)).hom g'=f
  rw [sortedComplex_d]
  change sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) (p+1) g'=f
  apply unaugmentedInclusion_injective R M F (p+2)
  rw [unaugmentedInclusion_delta R M F hF]
  exact hg
 

def sortedZeroEquiv : sorted R M F 0 ≃ₗ[R] F ∅ where
  toFun f := f DoubleCech.emptyIndex
  invFun x s := (DoubleCech.zeroIndex_eq s).symm ▸ x
  left_inv f := by funext s;cases DoubleCech.zeroIndex_eq s;rfl
  right_inv x := rfl
  map_add' f g := rfl
  map_smul' r f := rfl
variable [Nonempty ι]
omit [Fintype ι] in
lemma sorted_zero_injective : Function.Injective (sortedDelta R M F hF 0) := by
  intro f g h
  apply (sortedZeroEquiv R M F).injective
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  let s : powersetCard ι 1 := ⟨{i},Finset.card_singleton _⟩
  have hv := congrArg (fun z : sorted R M F 1 => (z s:M)) h
  apply Subtype.ext
  change (∑ j : Fin 1,(-1:ℤ)^j.val • (f (delete s j):M))=(∑ j : Fin 1,(-1:ℤ)^j.val • (g (delete s j):M)) at hv
  simp only [Fin.sum_univ_one,Fin.val_zero,pow_zero,one_zsmul] at hv
  rw [DoubleCech.zeroIndex_eq (delete s 0)] at hv
  exact hv

def unaugmentedAugmentation : sorted R M F 0 →ₗ[R] sorted R M (zeroAugmentation R M F) 1 :=
  (unaugmentedEquiv R M F 1 (by omega)).symm.toLinearMap.comp (sortedDelta R M F hF 0)
omit [Nonempty ι] in
lemma unaugmentedAugmentation_square :
    (sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) 1).comp
      (unaugmentedAugmentation R M F hF)=0 := by
  apply LinearMap.ext
  intro f
  change sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) 1 (unaugmentedAugmentation R M F hF f)=0
  apply unaugmentedInclusion_injective R M F 2
  rw [map_zero,unaugmentedInclusion_delta R M F hF]
  change sortedDelta R M F hF 1 ((unaugmentedEquiv R M F 1 (by omega))
    ((unaugmentedEquiv R M F 1 (by omega)).symm (sortedDelta R M F hF 0 f)))=0
  rw [LinearEquiv.apply_symm_apply,sortedDelta_square]
def augmentationShortComplex := ShortComplex.moduleCatMk (unaugmentedAugmentation R M F hF)
    (sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) 1)
    (unaugmentedAugmentation_square R M F hF)
omit [Nonempty ι] in
lemma augmentationShortComplex_exact (h : (sortedComplex R M F hF).ExactAt 1) :
    (augmentationShortComplex R M F hF).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change sorted R M (zeroAugmentation R M F) 1 at f
  change sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) 1 f=0 at hf
  have he := ((sortedComplex R M F hF).exactAt_iff' (i:=0) (j:=1) (k:=2) (by simp) (by simp)).mp h
  rw [ShortComplex.moduleCat_exact_iff] at he
  obtain ⟨g,hg⟩ := he (unaugmentedInclusion R M F 1 f) (by
    change ((sortedComplex R M F hF).d 1 2).hom _=0
    rw [sortedComplex_d]
    change sortedDelta R M F hF 1 (unaugmentedInclusion R M F 1 f)=0
    rw [←unaugmentedInclusion_delta R M F hF,hf,map_zero])
  change sorted R M F 0 at g
  change ((sortedComplex R M F hF).d 0 1).hom g = _ at hg
  rw [sortedComplex_d] at hg
  refine ⟨g,?_⟩
  apply (unaugmentedEquiv R M F 1 (by omega)).injective
  change (unaugmentedEquiv R M F 1 (by omega))
    ((unaugmentedEquiv R M F 1 (by omega)).symm (sortedDelta R M F hF 0 g))=_
  rw [LinearEquiv.apply_symm_apply]
  exact hg
instance augmentationShortComplex_mono : Mono (augmentationShortComplex R M F hF).f := by
  apply (ModuleCat.mono_iff_injective _).mpr
  exact (unaugmentedEquiv R M F 1 (by omega)).symm.injective.comp (sorted_zero_injective R M F hF)
 

def unaugmented_homology_one (h : (sortedComplex R M F hF).ExactAt 1) :
    (unaugmentedComplex R M F hF).homology 1 ≅ ModuleCat.of R (F ∅) := by
  let U := unaugmentedComplex R M F hF
  let S := U.sc' 0 1 2
  have hf : S.f=0 := (unaugmented_isZero_zero R M F hF).eq_of_src _ _
  let T := augmentationShortComplex R M F hF
  let c : KernelFork S.g := KernelFork.ofι T.f (by
    exact T.zero)
  have hc : IsLimit c := (augmentationShortComplex_exact R M F hF h).fIsKernel
  exact U.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    (ShortComplex.LeftHomologyData.ofIsLimitKernelFork S hf c hc).homologyIso ≪≫
    (sortedZeroEquiv R M F).toModuleIso
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (F : Finset ι → Submodule R M)
lemma zeroAug_cochains_le (p : ℕ) : cochains R M (zeroAugmentation R M F) p ≤ cochains R M F p := by
  intro f hf a
  have h := hf a
  by_cases hs : FiniteCoverCech.intersection a=∅
  · have hz : evaluation R M p f a=0 := by
      simpa [zeroAugmentation,hs] using h
    rw [hz]
    exact (F _).zero_mem
  · simpa only [zeroAugmentation,ite_eq_right hs] using h
lemma zeroAug_cochains_pos (p : ℕ) (hp : 0<p) :
    cochains R M (zeroAugmentation R M F) p=cochains R M F p := by
  apply le_antisymm (zeroAug_cochains_le R M F p)
  intro f hf a
  have hs : FiniteCoverCech.intersection a≠∅ := by
    intro he
    have hm : a ⟨0,hp⟩∈FiniteCoverCech.intersection a := by simp [FiniteCoverCech.intersection]
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  simpa only [zeroAugmentation,ite_eq_right hs] using hf a
lemma zeroAug_cochains_zero (f : Alt R M (ι:=ι) 0)
    (hf : f∈cochains R M (zeroAugmentation R M F) 0) : f=0 := by
  apply evaluation_injective R M 0
  apply funext;intro a
  have he : FiniteCoverCech.intersection a=∅ := by simp [FiniteCoverCech.intersection]
  have h := hf a
  simpa [zeroAugmentation,he] using h
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
variable (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (F : Finset ι → Submodule R M) (G : Finset κ → Submodule R N)
variable (hF : Monotone F) (hG : Monotone G)
variable (t : ∀ p,Alt R M (ι:=ι) p →ₗ[R] Alt R N (ι:=κ) p)
variable (ht : ∀ p f,f∈cochains R M F p → t p f∈cochains R N G p)
variable (hc : ∀ p f,t (p+1) (delta R M p f)=delta R N p (t p f))
 

def complexMap : complex R M F hF ⟶ complex R N G hG :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom ((t p).restrict (ht p))) (fun p => by
    rw [complex_d,complex_d]
    apply ModuleCat.hom_ext;apply LinearMap.ext;intro f
    exact Subtype.ext (hc p f.val).symm)
lemma complexMap_apply (p : ℕ) (f : cochains R M F p) :
    ((complexMap R M N F G hF hG t ht hc).f p).hom f=⟨t p f.val,ht p f.val f.property⟩ := rfl
end Lech.AlternatingCech


namespace Lech.ProductSourceCover
open AlternatingCech CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
abbrev ordinarySections (m : Fin n → ℤ) := zeroAugmentation R (LaurentModule R n) (sections R n m)
lemma ordinarySections_mono (m : Fin n → ℤ) : Monotone (ordinarySections R n m) :=
  zeroAugmentation_mono R (LaurentModule R n) (sections R n m) (sections_mono R n m)
abbrev ordinaryCochains (m : Fin n → ℤ) (p : ℕ) :=
  cochains R (LaurentModule R n) (ordinarySections R n m) p
lemma ordinaryCochains_pos (m : Fin n → ℤ) (p : ℕ) (hp : 0<p) :
    ordinaryCochains R n m p=divisorCochains R n m p :=
  zeroAug_cochains_pos R (LaurentModule R n) (sections R n m) p hp
lemma ordinaryCochains_zero (m : Fin n → ℤ) (f : ordinaryCochains R n m 0) : f=0 :=
  Subtype.ext (zeroAug_cochains_zero R (LaurentModule R n) (sections R n m) f.val f.property)
lemma ordinary_slice_mem (k : ℤ) (m : Fin n → ℤ) (p : ℕ)
    (f : ordinaryCochains R (n+1) (Fin.cons k m) p) :
    faceSlice R n k p f.val∈ordinaryCochains R n m p := by
  cases p with
  | zero =>
    rw [ordinaryCochains_zero R (n+1) (Fin.cons k m) f]
    change faceSlice R n k 0 0∈ordinaryCochains R n m 0
    rw [map_zero]
    exact (ordinaryCochains R n m 0).zero_mem
  | succ p =>
    rw [ordinaryCochains_pos R n m (p+1) (by omega)]
    apply faceSlice_mem R n k m
    exact zeroAug_cochains_le R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons k m)) (p+1) f.property
lemma ordinary_lift_mem (k : ℤ) (m : Fin n → ℤ) (p : ℕ)
    (f : ordinaryCochains R n m p) : faceLift R n k p f.val∈ordinaryCochains R (n+1) (Fin.cons k m) p := by
  cases p with
  | zero =>
    rw [ordinaryCochains_zero R n m f]
    change faceLift R n k 0 0∈ordinaryCochains R (n+1) (Fin.cons k m) 0
    rw [map_zero]
    exact (ordinaryCochains R (n+1) (Fin.cons k m) 0).zero_mem
  | succ p =>
    rw [ordinaryCochains_pos R (n+1) (Fin.cons k m) (p+1) (by omega)]
    apply faceLift_mem R n k m (p+1) (by omega)
    exact zeroAug_cochains_le R (LaurentModule R n) (sections R n m) (p+1) f.property
lemma ordinary_neighbor_le (k : ℤ) (m : Fin n → ℤ) (p : ℕ) :
    ordinaryCochains R (n+1) (Fin.cons (k-1) m) p ≤ ordinaryCochains R (n+1) (Fin.cons k m) p := by
  intro f hf
  cases p with
  | zero => rw [zeroAug_cochains_zero R (LaurentModule R (n+1)) _ f hf];exact (ordinaryCochains R (n+1) _ 0).zero_mem
  | succ p =>
    rw [ordinaryCochains_pos R (n+1) (Fin.cons (k-1) m) (p+1) (by omega)] at hf
    rw [ordinaryCochains_pos R (n+1) (Fin.cons k m) (p+1) (by omega)]
    exact (divisorInclusion R n k m (p+1) ⟨f,hf⟩).property
def ordinaryInclusion (k : ℤ) (m : Fin n → ℤ) (p : ℕ) :
    ordinaryCochains R (n+1) (Fin.cons (k-1) m) p →ₗ[R] ordinaryCochains R (n+1) (Fin.cons k m) p :=
  Submodule.inclusion (ordinary_neighbor_le R n k m p)
def ordinaryRestriction (k : ℤ) (m : Fin n → ℤ) (p : ℕ) :
    ordinaryCochains R (n+1) (Fin.cons k m) p →ₗ[R] ordinaryCochains R n m p :=
  (faceSlice R n k p).restrict (fun f hf => ordinary_slice_mem R n k m p ⟨f,hf⟩)
def ordinarySection (k : ℤ) (m : Fin n → ℤ) (p : ℕ) :
    ordinaryCochains R n m p →ₗ[R] ordinaryCochains R (n+1) (Fin.cons k m) p :=
  (faceLift R n k p).restrict (fun f hf => ordinary_lift_mem R n k m p ⟨f,hf⟩)
def ordinaryComplex (m : Fin n → ℤ) :=
  complex R (LaurentModule R n) (ordinarySections R n m) (ordinarySections_mono R n m)
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AddMonoidAlgebra
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
abbrev Ambient := ProductLaurent.Ring R n
 

def ringSections (m : Fin n → ℤ) (s : Finset (Chart n)) : Submodule R (Ambient R n) :=
  (sections R n m s).comap (coeffLinearEquiv R).toLinearMap
lemma ringSections_mem (m : Fin n → ℤ) (s : Finset (Chart n)) (x : Ambient R n) :
    x∈ringSections R n m s ↔ ∀ e∈x.coeff.support,allowed n m s e := by
  exact Finsupp.mem_supported R x.coeff
lemma single_mem (m : Fin n → ℤ) (s : Finset (Chart n)) (e : Exponent n) (r : R)
    (he : allowed n m s e) : single e r∈ringSections R n m s := by
  rw [ringSections_mem]
  intro f hf
  have hfe : f=e := Finset.mem_singleton.mp (Finsupp.support_single_subset hf)
  exact hfe ▸ he
lemma allowed_add (m k : Fin n → ℤ) (s : Finset (Chart n)) (e f : Exponent n)
    (he : allowed n m s e) (hf : allowed n k s f) : allowed n (m+k) s (e+f) := by
  intro i
  exact ⟨fun h => add_nonneg ((he i).1 h) ((hf i).1 h),fun h => add_le_add ((he i).2 h) ((hf i).2 h)⟩
lemma mul_mem (m k : Fin n → ℤ) (s : Finset (Chart n)) (x y : Ambient R n)
    (hx : x∈ringSections R n m s) (hy : y∈ringSections R n k s) :
    x*y∈ringSections R n (m+k) s := by
  rw [mul_def]
  apply (ringSections R n (m+k) s).sum_mem
  intro e he
  apply (ringSections R n (m+k) s).sum_mem
  intro f hf
  exact single_mem R n (m+k) s (e+f) _
    (allowed_add n m k s e f ((ringSections_mem R n m s x).mp hx e he)
      ((ringSections_mem R n k s y).mp hy f hf))
lemma one_mem (s : Finset (Chart n)) : (1:Ambient R n)∈ringSections R n 0 s := by
  rw [one_def]
  apply single_mem
  intro i
  exact ⟨fun _ => le_refl _,fun _ => le_refl _⟩
lemma pow_mem (m : Fin n → ℤ) (s : Finset (Chart n)) (x : Ambient R n)
    (hx : x∈ringSections R n m s) (N : ℕ) : x^N∈ringSections R n (N • m) s := by
  induction N with
  | zero => simpa only [pow_zero,zero_smul] using one_mem R n s
  | succ N ih =>
    simpa only [pow_succ,succ_nsmul] using mul_mem R n (N • m) m s (x^N) x ih hx
lemma ringSections_mono (m : Fin n → ℤ) : Monotone (ringSections R n m) := by
  intro s t hst
  exact Submodule.comap_mono (sections_mono R n m hst)
lemma twist_mono (m k : Fin n → ℤ) (hmk : m≤k) (s : Finset (Chart n)) :
    ringSections R n m s≤ringSections R n k s := by
  intro x hx
  rw [ringSections_mem] at hx ⊢
  intro e he i
  exact ⟨(hx e he i).1,fun h => ((hx e he i).2 h).trans (hmk i)⟩

 
def twistExponent (m : Fin n → ℤ) (σ : Chart n) : Exponent n :=
  Finsupp.equivFunOnFinite.symm (fun i => if σ i then m i else 0)
lemma twistExponent_apply (m : Fin n → ℤ) (σ : Chart n) (i : Fin n) :
    twistExponent n m σ i=(if σ i then m i else 0) := rfl
def affineExponent (m : Fin n → ℤ) (σ : Chart n) (e : Fin n →₀ ℕ) : Exponent n :=
  twistExponent n m σ+ProductLaurent.signedExponent n σ e
lemma affineExponent_allowed (m : Fin n → ℤ) (σ : Chart n) (e : Fin n →₀ ℕ) :
    allowed n m {σ} (affineExponent n m σ e) := by
  intro i
  simp only [affineExponent,Finsupp.add_apply,twistExponent_apply,ProductLaurent.signedExponent_apply]
  cases hs : σ i <;> simp [hs]
def affineCoordinates (m : Fin n → ℤ) (σ : Chart n) (e : Exponent n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => if σ i then (m i-e i).toNat else (e i).toNat)
lemma affineExponent_coordinates (m : Fin n → ℤ) (σ : Chart n) (e : Exponent n)
    (he : allowed n m {σ} e) : affineExponent n m σ (affineCoordinates n m σ e)=e := by
  ext i
  have hi := he i
  simp only [Finset.mem_singleton,forall_eq] at hi
  simp only [affineExponent,Finsupp.add_apply,twistExponent_apply,ProductLaurent.signedExponent_apply]
  change (if σ i then m i else 0)+(if σ i then -(↑(if σ i then (m i-e i).toNat else (e i).toNat):ℤ)
    else (↑(if σ i then (m i-e i).toNat else (e i).toNat):ℤ))=e i
  cases hs : σ i <;> simp only [hs,Bool.false_eq_true,↓reduceIte] at hi ⊢
  · rw [Int.toNat_of_nonneg (hi.1 trivial),zero_add]
  · rw [Int.toNat_of_nonneg (sub_nonneg.mpr (hi.2 trivial))];omega
 

def chartLine (m : Fin n → ℤ) (σ : Chart n) : ProductLinearChart.Ring R n →ₗ[R] Ambient R n :=
  (LinearMap.mulLeft R (ProductLaurent.monomialUnit R n (twistExponent n m σ):Ambient R n)).comp
    (ProductLaurent.chartMap R n σ).toLinearMap
lemma chartLine_monomial (m : Fin n → ℤ) (σ : Chart n) (e : Fin n →₀ ℕ) (r : R) :
    chartLine R n m σ (MvPolynomial.monomial e r)=single (affineExponent n m σ e) r := by
  change single (twistExponent n m σ) 1 * ProductLaurent.chartMap R n σ (MvPolynomial.monomial e r)=_
  rw [ProductLaurent.chartMap_monomial,single_mul_single,one_mul]
  rfl
lemma chartLine_mem (m : Fin n → ℤ) (σ : Chart n) (p : ProductLinearChart.Ring R n) :
    chartLine R n m σ p∈ringSections R n m {σ} := by
  rw [MvPolynomial.as_sum p,map_sum]
  apply (ringSections R n m {σ}).sum_mem
  intro e _
  rw [chartLine_monomial]
  exact single_mem R n m {σ} _ _ (affineExponent_allowed n m σ e)
 

theorem chartLine_range (m : Fin n → ℤ) (σ : Chart n) :
    (chartLine R n m σ).range=ringSections R n m {σ} := by
  apply le_antisymm
  · rintro _ ⟨p,rfl⟩;exact chartLine_mem R n m σ p
  · intro x hx
    refine ⟨∑ e∈x.coeff.support,MvPolynomial.monomial (affineCoordinates n m σ e) (x.coeff e),?_⟩
    rw [map_sum]
    calc
      _ = ∑ e∈x.coeff.support,single e (x.coeff e) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [chartLine_monomial,affineExponent_coordinates n m σ e ((ringSections_mem R n m {σ} x).mp hx e he)]
      _ = x := AddMonoidAlgebra.sum_coeff_single x
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AddMonoidAlgebra CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def ringProjector (m : Fin n → ℤ) (σ : Chart n) : Ambient R n →ₗ[R] Ambient R n :=
  (coeffLinearEquiv R).symm.toLinearMap.comp
    ((projector R n m σ).comp (coeffLinearEquiv R).toLinearMap)
lemma ringProjector_coeff (m : Fin n → ℤ) (σ : Chart n) (x : Ambient R n) :
    (ringProjector R n m σ x).coeff=projector R n m σ x.coeff := by
  change (coeffLinearEquiv R) ((coeffLinearEquiv R).symm _)=_
  exact (coeffLinearEquiv R).apply_symm_apply _
lemma ringProjector_sum (m : Fin n → ℤ) (x : Ambient R n) : ∑ σ,ringProjector R n m σ x=x := by
  apply (coeffLinearEquiv R).injective
  change (coeffLinearEquiv R) (∑ σ,ringProjector R n m σ x)=x.coeff
  rw [map_sum]
  simpa only [coeffLinearEquiv_apply,ringProjector_coeff] using projector_sum R n m x.coeff
lemma ringProjector_mem (m : Fin n → ℤ) (hm : ∀ i,-1≤ m i) (s : Finset (Chart n))
    (σ : Chart n) (x : Ambient R n) (hx : x∈ringSections R n m (insert σ s)) :
    ringProjector R n m σ x∈ringSections R n m s := by
  change (ringProjector R n m σ x).coeff∈sections R n m s
  rw [ringProjector_coeff]
  exact projector_mem R n m hm s σ x.coeff hx
 

theorem ring_augmented_acyclic (m : Fin n → ℤ) (hm : ∀ i,-1≤ m i) :
    (AlternatingCech.complex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)).Acyclic :=
  AlternatingCech.projection_complex_acyclic R (Ambient R n) (ringSections R n m)
    (ringSections_mono R n m) (ringProjector R n m) (ringProjector_sum R n m)
      (ringProjector_mem R n m hm)
theorem ring_sorted_acyclic [LinearOrder (Chart n)] (m : Fin n → ℤ) (hm : ∀ i,-1≤ m i) :
    (AlternatingCech.sortedComplex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)).Acyclic := by
  intro j
  apply (ring_augmented_acyclic R n m hm j).of_iso
  convert AlternatingCech.cochainsSortedIso R (Ambient R n) (ringSections R n m) (ringSections_mono R n m) using 1
  congr 1
end Lech.ProductSourceCover
end
end

end OAI
