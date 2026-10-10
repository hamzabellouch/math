import Mathlib
import OAI.RingTheory.Multiplicity.AlternatingCechUnaugmentedComplex

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
open AddMonoidAlgebra
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma allowed_empty (m : Fin n → ℤ) (e : Exponent n) :
    allowed n m ∅ e ↔ ∀ i,0≤e i ∧ e i ≤ m i := by
  simp [allowed]
 
abbrev GlobalIndex (m : Fin n → ℤ) := {e : Exponent n // allowed n m ∅ e}
def globalIndexEquiv (m : Fin n → ℤ) : GlobalIndex n m ≃ (∀ i : Fin n,Set.Icc (0:ℤ) (m i)) where
  toFun e i := ⟨e.val i,(allowed_empty n m e.val).mp e.property i⟩
  invFun e := ⟨Finsupp.equivFunOnFinite.symm (fun i => (e i).val),
    (allowed_empty n m _).mpr (fun i => (e i).property)⟩
  left_inv e := by apply Subtype.ext;ext i;rfl
  right_inv e := by funext i;apply Subtype.ext;rfl
instance globalIndexFintype (m : Fin n → ℤ) : Fintype (GlobalIndex n m) :=
  Fintype.ofEquiv _ (globalIndexEquiv n m).symm
lemma globalIndex_card (m : Fin n → ℤ) : Fintype.card (GlobalIndex n m)=∏ i,(m i+1).toNat := by
  rw [Fintype.card_congr (globalIndexEquiv n m),Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_ofFinset]
  simp only [Int.card_Icc,sub_zero]
 

def globalCoefficientEquiv (m : Fin n → ℤ) : ringSections R n m ∅ ≃ₗ[R] (GlobalIndex n m →₀ R) :=
  ((coeffLinearEquiv R : Ambient R n ≃ₗ[R] LaurentModule R n).ofSubmodule' (sections R n m ∅)).trans
    (Finsupp.supportedEquivFinsupp {e | allowed n m ∅ e})

def globalBasis (m : Fin n → ℤ) : Module.Basis (GlobalIndex n m) R (ringSections R n m ∅) :=
  Finsupp.basisSingleOne.map (globalCoefficientEquiv R n m).symm
instance globalSections_finite (m : Fin n → ℤ) : Module.Finite R (ringSections R n m ∅) :=
  Module.Finite.of_basis (globalBasis R n m)
instance globalSections_free (m : Fin n → ℤ) : Module.Free R (ringSections R n m ∅) :=
  Module.Free.of_basis (globalBasis R n m)
lemma globalSections_finrank [Nontrivial R] (m : Fin n → ℤ) :
    Module.finrank R (ringSections R n m ∅)=∏ i,(m i+1).toNat := by
  rw [Module.finrank_eq_card_basis (globalBasis R n m),globalIndex_card]
lemma globalSections_isZero (m : Fin n → ℤ) (i : Fin n) (hi : m i<0) :
    CategoryTheory.Limits.IsZero (ModuleCat.of R (ringSections R n m ∅)) := by
  have : IsEmpty (GlobalIndex n m) := ⟨fun e => by
    have he := (allowed_empty n m e.val).mp e.property i
    omega⟩
  have : Subsingleton (ringSections R n m ∅) := (globalCoefficientEquiv R n m).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
abbrev unaugmentedSource (m : Fin n → ℤ) :=
  AlternatingCech.unaugmentedComplex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)
 

def highTwistH0 (m : Fin n → ℤ) (hm : ∀ i,-1 ≤ m i) :
    (unaugmentedSource R n m).homology 1 ≅ ModuleCat.of R (ringSections R n m ∅) :=
  AlternatingCech.unaugmented_homology_one R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)
    (ring_sorted_acyclic R n m hm 1)
 

lemma highTwistHigher (m : Fin n → ℤ) (hm : ∀ i,-1 ≤ m i) (q : ℕ) :
    IsZero ((unaugmentedSource R n m).homology (q+2)) := by
  apply (exactAt_iff_isZero_homology _ _).mp
  exact AlternatingCech.unaugmented_exactAt R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)
    q (ring_sorted_acyclic R n m hm (q+2))
 
lemma highTwistH0_isZero (m : Fin n → ℤ) (hm : ∀ i,-1 ≤ m i)
    (i : Fin n) (hi : m i=-1) : IsZero ((unaugmentedSource R n m).homology 1) :=
  (globalSections_isZero R n m i (by omega)).of_iso (highTwistH0 R n m hm)
def highTwistH0Basis (m : Fin n → ℤ) (hm : ∀ i,-1 ≤ m i) :
    Module.Basis (GlobalIndex n m) R ((unaugmentedSource R n m).homology 1) :=
  (globalBasis R n m).map (highTwistH0 R n m hm).toLinearEquiv.symm
lemma highTwistH0_finrank [Nontrivial R] (m : Fin n → ℤ) (hm : ∀ i,-1 ≤ m i) :
    Module.finrank R ((unaugmentedSource R n m).homology 1)=∏ i,(m i+1).toNat := by
  rw [Module.finrank_eq_card_basis (highTwistH0Basis R n m hm),globalIndex_card]
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AddMonoidAlgebra CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
local instance endpointRingDecEq : DecidableEq (Chart n) := LinearOrder.toDecidableEq
def ringEndpointProjector (j : Fin n) (b : Bool) : Ambient R n →ₗ[R] Ambient R n :=
  (coeffLinearEquiv R).symm.toLinearMap.comp
    ((endpointProjector R n j b).comp (coeffLinearEquiv R).toLinearMap)
omit [LinearOrder (Chart n)] in
lemma ringEndpointProjector_coeff (j : Fin n) (b : Bool) (x : Ambient R n) :
    (ringEndpointProjector R n j b x).coeff=endpointProjector R n j b x.coeff := by
  change (coeffLinearEquiv R) ((coeffLinearEquiv R).symm _)=_
  exact (coeffLinearEquiv R).apply_symm_apply _
omit [LinearOrder (Chart n)] in
lemma ringEndpointProjector_sum (j : Fin n) (x : Ambient R n) : ∑ b,ringEndpointProjector R n j b x=x := by
  apply (coeffLinearEquiv R).injective
  change (coeffLinearEquiv R) (∑ b,ringEndpointProjector R n j b x)=x.coeff
  rw [map_sum]
  simpa only [coeffLinearEquiv_apply,ringEndpointProjector_coeff] using endpointProjector_sum R n j x.coeff
lemma ringEndpointProjector_carrier (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1)
    (s : Finset (Chart n)) (b : Bool) (x : Ambient R n)
    (hx : x∈ringSections R n m (s∪s.image (endpointVertex n j b))) :
    ringEndpointProjector R n j b x∈ringSections R n m s := by
  change (ringEndpointProjector R n j b x).coeff∈sections R n m s
  rw [ringEndpointProjector_coeff]
  exact endpointProjector_carrier R n m j hj s b x.coeff hx
lemma ringEndpointProjector_zero (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1)
    (s : Finset (Chart n)) (b : Bool) (x : Ambient R n)
    (hx : x∈ringSections R n m (s.image (endpointVertex n j b))) :
    ringEndpointProjector R n j b x=0 := by
  apply (coeffLinearEquiv R).injective
  change (ringEndpointProjector R n j b x).coeff = _
  rw [ringEndpointProjector_coeff,map_zero]
  exact endpointProjector_zero R n m j hj s b x.coeff hx
theorem ring_endpoint_acyclic (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1) :
    (AlternatingCech.complex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)).Acyclic := by
  have hdec : endpointRingDecEq n = Classical.decEq (Chart n) := Subsingleton.elim _ _
  have hcarrier := ringEndpointProjector_carrier R n m j hj
  have hzero := ringEndpointProjector_zero R n m j hj
  rw [hdec] at hcarrier hzero ⊢
  exact AlternatingCech.projection_prism_acyclic R (Ambient R n) (ringSections R n m)
    (ringSections_mono R n m) (ringEndpointProjector R n j) (ringEndpointProjector_sum R n j)
    (endpointVertex n j) (endpointVertex_idem n j) hcarrier hzero
theorem ring_endpoint_sorted_acyclic (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1) :
    (AlternatingCech.sortedComplex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)).Acyclic := by
  intro q
  apply (ring_endpoint_acyclic R n m j hj q).of_iso
  convert AlternatingCech.cochainsSortedIso R (Ambient R n) (ringSections R n m) (ringSections_mono R n m) using 1
  congr 1
 

theorem endpointCohomology_isZero (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1) (q : ℕ) :
    IsZero ((unaugmentedSource R n m).homology (q+1)) := by
  cases q with
  | zero =>
    exact (globalSections_isZero R n m j (by omega)).of_iso
      (AlternatingCech.unaugmented_homology_one R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)
        (ring_endpoint_sorted_acyclic R n m j hj 1))
  | succ q =>
    apply (exactAt_iff_isZero_homology _ _).mp
    exact AlternatingCech.unaugmented_exactAt R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)
      q (ring_endpoint_sorted_acyclic R n m j hj (q+2))
end Lech.ProductSourceCover


namespace Lech.AlternatingCech
open Set
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R]
variable {ι : Type} [LinearOrder ι]
variable (M : Type u) [AddCommGroup M] [Module R M]
def rawDelta (n : ℕ) : (powersetCard ι n → M) →ₗ[R] (powersetCard ι (n+1) → M) where
  toFun f s := ∑ i : Fin (n+1),(-1:ℤ)^i.val • f (delete s i)
  map_add' f g := by ext s;simp [smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    ext s
    simp only [Pi.smul_apply,Finset.smul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
lemma rawDelta_sorted (n : ℕ) (f : sorted R M F n) :
    rawDelta R M n (fun s => (f s:M))=(fun s => (sortedDelta R M F hF n f s:M)) := by
  ext s
  simp only [rawDelta,sortedDelta,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum]
  rfl
variable (N : Type u) [AddCommGroup N] [Module R N]
lemma rawDelta_post (φ : M →ₗ[R] N) (n : ℕ) (f : powersetCard ι n → M) :
    rawDelta R N n (fun s => φ (f s))=(fun s => φ (rawDelta R M n f s)) := by
  ext s
  change (∑ i : Fin (n+1),(-1:ℤ)^i.val • φ (f (delete s i))) =
    φ (∑ i : Fin (n+1),(-1:ℤ)^i.val • f (delete s i))
  rw [map_sum]
  simp only [map_zsmul]
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
variable (M : Type u) [AddCommGroup M] [Module R M]
variable (N : Type u) [AddCommGroup N] [Module R N]
variable {ι : Type}
variable (F : Finset ι → Submodule R M) (G : Finset ι → Submodule R N)
variable (φ : M →ₗ[R] N) (hφ : Function.Injective φ) (hFG : ∀ s,(F s).map φ=G s)
def familyMap (s : Finset ι) : F s →ₗ[R] G s :=
  (φ.comp (F s).subtype).codRestrict (G s) (fun x => hFG s ▸ Submodule.mem_map.mpr ⟨x,x.property,rfl⟩)
include hφ in
lemma familyMap_injective (s : Finset ι) : Function.Injective (familyMap R M N F G φ hFG s) := by
  intro x y h
  apply Subtype.ext
  exact hφ (congrArg Subtype.val h)
lemma familyMap_surjective (s : Finset ι) : Function.Surjective (familyMap R M N F G φ hFG s) := by
  rintro ⟨y,hy⟩
  obtain ⟨x,hx,rfl⟩ := Submodule.mem_map.mp ((hFG s).symm ▸ hy)
  exact ⟨⟨x,hx⟩,rfl⟩
def familyEquiv (s : Finset ι) : F s ≃ₗ[R] G s :=
  LinearEquiv.ofBijective (familyMap R M N F G φ hFG s)
    ⟨familyMap_injective R M N F G φ hφ hFG s,familyMap_surjective R M N F G φ hFG s⟩
variable [Fintype ι] [LinearOrder ι]
def sortedFamilyEquiv (p : ℕ) : sorted R M F p ≃ₗ[R] sorted R N G p :=
  LinearEquiv.piCongrRight (fun s => familyEquiv R M N F G φ hφ hFG s.val)
omit [Fintype ι] [LinearOrder ι] in
lemma sortedFamilyEquiv_apply (p : ℕ) (f : sorted R M F p) (s : powersetCard ι p) :
    (sortedFamilyEquiv R M N F G φ hφ hFG p f s:N)=φ (f s:M) := rfl
variable (hF : Monotone F) (hG : Monotone G)
omit [Fintype ι] in
lemma sortedFamilyEquiv_delta (p : ℕ) (f : sorted R M F p) :
    sortedFamilyEquiv R M N F G φ hφ hFG (p+1) (sortedDelta R M F hF p f)=
      sortedDelta R N G hG p (sortedFamilyEquiv R M N F G φ hφ hFG p f) := by
  ext s
  simp only [sortedFamilyEquiv_apply,sortedDelta,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum,
    Submodule.coe_smul_of_tower,map_sum,map_zsmul]
  rfl
 

def sortedFamilyIso : sortedComplex R M F hF ≅ sortedComplex R N G hG :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (sortedFamilyEquiv R M N F G φ hφ hFG p).toModuleIso) (fun p q hpq => by
      obtain rfl : p+1=q := hpq
      rw [sortedComplex_d,sortedComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (sortedFamilyEquiv_delta R M N F G φ hφ hFG hF hG p f).symm)
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open CategoryTheory
universe u
variable (R : Type u) [CommRing R]
variable (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
def sortedUnaugmentedFamilyIso (F : Finset ι → Submodule R M) (G : Finset ι → Submodule R N)
    (f : M →ₗ[R] N) (hf : Function.Injective f) (hfg : ∀ s,(F s).map f=G s)
    (hF : Monotone F) (hG : Monotone G) :
    unaugmentedComplex R M F hF ≅ unaugmentedComplex R N G hG :=
  sortedFamilyIso R M N (zeroAugmentation R M F) (zeroAugmentation R N G) f hf
    (fun s => by
      by_cases hs : s=∅
      · simp [zeroAugmentation,hs]
      · simpa only [zeroAugmentation,ite_eq_right hs] using hfg s)
    (zeroAugmentation_mono R M F hF) (zeroAugmentation_mono R N G hG)
end Lech.AlternatingCech


namespace Lech.ProductSourceCover
open AddMonoidAlgebra AlternatingCech CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
local instance ordinaryDecEq : DecidableEq (Chart n) := LinearOrder.toDecidableEq
omit [LinearOrder (Chart n)] in
lemma ringSections_coeff_map (m : Fin n → ℤ) (s : Finset (Chart n)) :
    (ringSections R n m s).map (coeffLinearEquiv R).toLinearMap=sections R n m s := by
  exact Submodule.map_comap_eq_of_surjective (coeffLinearEquiv R).surjective _
 

def ordinaryRingIso (m : Fin n → ℤ) : ordinaryComplex R n m ≅ unaugmentedSource R n m :=
  by
    letI ordinaryRingIsoDecEq : DecidableEq (Chart n) := Classical.decEq _
    have hh : ordinaryComplex R n m = complex R (LaurentModule R n)
        (ordinarySections R n m) (ordinarySections_mono R n m) := by
      unfold ordinaryComplex
      congr 1
    have hs : sortedComplex R (LaurentModule R n) (ordinarySections R n m) (ordinarySections_mono R n m) =
        unaugmentedComplex R (LaurentModule R n) (sections R n m) (sections_mono R n m) := by
      unfold unaugmentedComplex
      congr 1
      unfold ordinarySections
      congr 1
      exact Subsingleton.elim _ _
    exact eqToIso hh ≪≫
      cochainsSortedIso R (LaurentModule R n) (ordinarySections R n m) (ordinarySections_mono R n m) ≪≫ eqToIso hs ≪≫
      (sortedUnaugmentedFamilyIso R (Ambient R n) (LaurentModule R n) (ringSections R n m) (sections R n m)
        (coeffLinearEquiv R).toLinearMap (coeffLinearEquiv R).injective (ringSections_coeff_map R n m)
        (ringSections_mono R n m) (sections_mono R n m)).symm
def ordinaryCohomologyIso (m : Fin n → ℤ) (p : ℕ) :
    (ordinaryComplex R n m).homology p ≅ (unaugmentedSource R n m).homology p :=
  (homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) p).mapIso (ordinaryRingIso R n m)
omit [LinearOrder (Chart n)] in
lemma ordinary_zero_isZero (m : Fin n → ℤ) : IsZero ((ordinaryComplex R n m).X 0) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton (ordinaryCochains R n m 0)
  exact subsingleton_of_forall_eq 0 (ordinaryCochains_zero R n m)
omit [LinearOrder (Chart n)] in
lemma ordinary_homology_zero (m : Fin n → ℤ) : IsZero ((ordinaryComplex R n m).homology 0) := by
  exact (HomologicalComplex.ExactAt.of_isZero (ordinary_zero_isZero R n m)).isZero_homology
 

theorem ordinary_endpoint_acyclic (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1) :
    (ordinaryComplex R n m).Acyclic := by
  intro p
  apply (exactAt_iff_isZero_homology _ _).mpr
  cases p with
  | zero => exact ordinary_homology_zero R n m
  | succ p => exact (endpointCohomology_isZero R n m j hj p).of_iso (ordinaryCohomologyIso R n m (p+1))
end Lech.ProductSourceCover


namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
variable (M N P : Type u) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
variable (F : Finset ι → Submodule R M) (G : Finset κ → Submodule R N) (H : Finset μ → Submodule R P)
variable (hF : Monotone F) (hG : Monotone G) (hH : Monotone H)
variable (s : ∀ p,Alt R M (ι:=ι) p →ₗ[R] Alt R N (ι:=κ) p)
variable (t : ∀ p,Alt R N (ι:=κ) p →ₗ[R] Alt R P (ι:=μ) p)
variable (hs : ∀ p f,f∈cochains R M F p → s p f∈cochains R N G p)
variable (ht : ∀ p f,f∈cochains R N G p → t p f∈cochains R P H p)
variable (hsc : ∀ p f,s (p+1) (delta R M p f)=delta R N p (s p f))
variable (htc : ∀ p f,t (p+1) (delta R N p f)=delta R P p (t p f))
variable (hzero : ∀ p f,f∈cochains R M F p → t p (s p f)=0)
def complexSequence : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (complexMap R M N F G hF hG s hs hsc) (complexMap R N P G H hG hH t ht htc) (by
    ext p : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact Subtype.ext (hzero p f.val f.property))
lemma complexSequence_shortExact
    (hinj : ∀ p,Function.Injective ((s p).restrict (hs p)))
    (hexa : ∀ p f,f∈cochains R N G p → t p f=0 → ∃ g,g∈cochains R M F p ∧ s p g=f)
    (hsur : ∀ p f,f∈cochains R P H p → ∃ g,g∈cochains R N G p ∧ t p g=f) :
    (complexSequence R M N P F G H hF hG hH s t hs ht hsc htc hzero).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro p
  refine CategoryTheory.ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro f hf
    have hf' : t p f.val=0 := congrArg Subtype.val hf
    obtain ⟨g,hg,hgf⟩ := hexa p f.val f.property hf'
    exact ⟨⟨g,hg⟩,Subtype.ext hgf⟩
  · exact (ModuleCat.mono_iff_injective _).mpr (hinj p)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro f
    obtain ⟨g,hg,hgf⟩ := hsur p f.val f.property
    exact ⟨⟨g,hg⟩,Subtype.ext hgf⟩
lemma complexSequence_shortExact_injective
    (hinj : ∀ p,Function.Injective (s p))
    (hexa : ∀ p f,f∈cochains R N G p → t p f=0 → ∃ g,g∈cochains R M F p ∧ s p g=f)
    (hsur : ∀ p f,f∈cochains R P H p → ∃ g,g∈cochains R N G p ∧ t p g=f) :
    (complexSequence R M N P F G H hF hG hH s t hs ht hsc htc hzero).ShortExact := by
  apply complexSequence_shortExact R M N P F G H hF hG hH s t hs ht hsc htc hzero _ hexa hsur
  intro p f g h
  exact Subtype.ext (hinj p (congrArg Subtype.val h))
end Lech.AlternatingCech


namespace Lech.ProductSourceCover
open AlternatingCech CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma ordinary_slice_zero (k : ℤ) (m : Fin n → ℤ) (p : ℕ)
    (f : Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p)
    (hf : f∈ordinaryCochains R (n+1) (Fin.cons (k-1) m) p) : faceSlice R n k p f=0 := by
  apply (faceSlice_kernel R n k m p f
    (zeroAug_cochains_le R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons k m)) p
      (ordinary_neighbor_le R n k m p hf))).mpr
  exact zeroAug_cochains_le R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons (k-1) m)) p hf
 

def ordinaryDivisorSequence (k : ℤ) (m : Fin n → ℤ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  complexSequence R (LaurentModule R (n+1)) (LaurentModule R (n+1)) (LaurentModule R n)
    (ordinarySections R (n+1) (Fin.cons (k-1) m)) (ordinarySections R (n+1) (Fin.cons k m)) (ordinarySections R n m)
    (ordinarySections_mono R (n+1) (Fin.cons (k-1) m)) (ordinarySections_mono R (n+1) (Fin.cons k m)) (ordinarySections_mono R n m)
    (fun _ => LinearMap.id) (faceSlice R n k)
    (fun p _ hf => ordinary_neighbor_le R n k m p hf) (fun p f hf => ordinary_slice_mem R n k m p ⟨f,hf⟩)
    (fun _ _ => rfl) (faceSlice_delta R n k) (ordinary_slice_zero R n k m)
theorem ordinaryDivisorSequence_shortExact (k : ℤ) (m : Fin n → ℤ) :
    (ordinaryDivisorSequence R n k m).ShortExact := by
  unfold ordinaryDivisorSequence
  apply complexSequence_shortExact_injective
  · intro p
    exact Function.injective_id
  · intro p f hf hz
    refine ⟨f,?_,rfl⟩
    cases p with
    | zero =>
      rw [zeroAug_cochains_zero R (LaurentModule R (n+1)) _ f hf]
      exact (ordinaryCochains R (n+1) _ 0).zero_mem
    | succ p =>
      change f∈ordinaryCochains R (n+1) (Fin.cons (k-1) m) (p+1)
      rw [ordinaryCochains_pos R (n+1) (Fin.cons (k-1) m) (p+1) (by omega)]
      exact (faceSlice_kernel R n k m (p+1) f
        (zeroAug_cochains_le R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons k m)) (p+1) hf)).mp hz
  · intro p f hf
    exact ⟨faceLift R n k p f,ordinary_lift_mem R n k m p ⟨f,hf⟩,faceSlice_lift R n k p f⟩
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
@[simp] lemma ordinaryDivisorSequence_X1 (k : ℤ) (m : Fin n → ℤ) :
    (ordinaryDivisorSequence R n k m).X₁=ordinaryComplex R (n+1) (Fin.cons (k-1) m) := rfl
@[simp] lemma ordinaryDivisorSequence_X2 (k : ℤ) (m : Fin n → ℤ) :
    (ordinaryDivisorSequence R n k m).X₂=ordinaryComplex R (n+1) (Fin.cons k m) := rfl
@[simp] lemma ordinaryDivisorSequence_X3 (k : ℤ) (m : Fin n → ℤ) :
    (ordinaryDivisorSequence R n k m).X₃=ordinaryComplex R n m := rfl
end Lech.ProductSourceCover


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
 

def PureCohomology (K : CochainComplex (ModuleCat.{u} R) ℕ) (d r : ℕ) : Prop :=
  (∀ i,i≠d → IsZero (K.homology i)) ∧ Nonempty (Module.Basis (Fin r) R (K.homology d))
variable {R}
lemma pureCohomology_acyclic (K : CochainComplex (ModuleCat.{u} R) ℕ) (h : K.Acyclic) (d : ℕ) :
    PureCohomology R K d 0 := by
  refine ⟨fun i _ => (exactAt_iff_isZero_homology _ _).mp (h i),?_⟩
  have hi := (exactAt_iff_isZero_homology _ _).mp (h d)
  have : Subsingleton (K.homology d) := ModuleCat.isZero_iff_subsingleton.mp hi
  exact ⟨Module.Basis.empty _⟩
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact)
def cohomologyShortComplex (d : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (homologyMap S.f d) (homologyMap S.g d) (by
    rw [←homologyMap_comp,S.zero,homologyMap_zero])
include hS in
lemma cohomologyShortComplex_shortExact (d : ℕ) (hd : 0<d)
    (hprev : IsZero (S.X₃.homology (d-1))) (hnext : IsZero (S.X₁.homology (d+1))) :
    (cohomologyShortComplex S d).ShortExact := by
  refine ShortComplex.ShortExact.mk' (hS.homology_exact₂ d) ?_ ?_
  · exact (hS.homology_exact₁ (d-1) d (by change d-1+1=d;omega)).mono_g (hprev.eq_of_src _ _)
  · exact (hS.homology_exact₃ d (d+1) rfl).epi_f (hnext.eq_of_tgt _ _)
include hS in
lemma pureCohomology_middle {d a b : ℕ} (hd : 0<d)
    (h₁ : PureCohomology R S.X₁ d a) (h₃ : PureCohomology R S.X₃ d b) :
    PureCohomology R S.X₂ d (a+b) := by
  refine ⟨fun i hi => (hS.homology_exact₂ i).isZero_X₂
    ((h₁.1 i hi).eq_of_src _ _) ((h₃.1 i hi).eq_of_tgt _ _),?_⟩
  obtain ⟨b₁⟩ := h₁.2
  obtain ⟨b₃⟩ := h₃.2
  let h := cohomologyShortComplex_shortExact S hS d hd (h₃.1 (d-1) (by omega)) (h₁.1 (d+1) (by omega))
  exact ⟨(ModuleCat.Basis.ofShortExact h b₁ b₃).reindex (finSumFinEquiv)⟩
def boundaryShortComplex (d : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (hS.δ d (d+1) rfl) (homologyMap S.f (d+1)) (hS.δ_comp d (d+1) rfl)
lemma boundaryShortComplex_shortExact (d : ℕ)
    (h₂ : IsZero (S.X₂.homology d)) (h₃ : IsZero (S.X₃.homology (d+1))) :
    (boundaryShortComplex S hS d).ShortExact := by
  refine ShortComplex.ShortExact.mk' (hS.homology_exact₁ d (d+1) rfl) (hS.mono_δ d (d+1) rfl h₂) ?_
  exact (hS.homology_exact₂ (d+1)).epi_f (h₃.eq_of_tgt _ _)
include hS in
lemma pureCohomology_left {d a b : ℕ}
    (hzero : IsZero (S.X₁.homology 0))
    (h₂ : PureCohomology R S.X₂ (d+1) a) (h₃ : PureCohomology R S.X₃ d b) :
    PureCohomology R S.X₁ (d+1) (b+a) := by
  refine ⟨?_,?_⟩
  · intro i hi
    cases i with
    | zero => exact hzero
    | succ i =>
      exact (hS.homology_exact₁ i (i+1) rfl).isZero_X₂
        ((h₃.1 i (by omega)).eq_of_src _ _) ((h₂.1 (i+1) hi).eq_of_tgt _ _)
  · obtain ⟨b₂⟩ := h₂.2
    obtain ⟨b₃⟩ := h₃.2
    let h := boundaryShortComplex_shortExact S hS d (h₂.1 d (by omega)) (h₃.1 (d+1) (by omega))
    exact ⟨(ModuleCat.Basis.ofShortExact h b₃ b₂).reindex finSumFinEquiv⟩
end Lech
end

end OAI
