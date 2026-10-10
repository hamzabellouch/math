import Mathlib
import OAI.RingTheory.Multiplicity.SignedCechBicRow

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R]

def baseChangeLocalizationIso (U : Submonoid R) :
    baseChangeFunctor R (Localization U) ≅ ModuleCat.localizedModuleFunctor U :=
  NatIso.ofComponents (fun M =>
    (IsLocalizedModule.isBaseChange U (Localization U) (M.localizedModuleMkLinearMap U)).equiv.toModuleIso)
    (by
      intro M N f
      apply ModuleCat.hom_ext
      change (IsLocalizedModule.isBaseChange U (Localization U)
        (N.localizedModuleMkLinearMap U)).equiv.toLinearMap.comp (f.hom.baseChange (Localization U))=
        (ModuleCat.localizedModuleMap U f).hom.comp
          (IsLocalizedModule.isBaseChange U (Localization U) (M.localizedModuleMkLinearMap U)).equiv.toLinearMap
      apply LinearMap.restrictScalars_injective R
      apply TensorProduct.ext'
      intro s m
      change (IsLocalizedModule.isBaseChange U (Localization U) (N.localizedModuleMkLinearMap U)).equiv
        (s ⊗ₜ[R] f.hom m)=
        (ModuleCat.localizedModuleMap U f).hom
          ((IsLocalizedModule.isBaseChange U (Localization U) (M.localizedModuleMkLinearMap U)).equiv
            (s ⊗ₜ[R] m))
      simp only [IsBaseChange.equiv_tmul,map_smul]
      congr 1
      exact (IsLocalizedModule.map_apply U (M.localizedModuleMkLinearMap U)
        (N.localizedModuleMkLinearMap U) f.hom m).symm)

instance baseChangeLocalization_preservesFiniteLimits (U : Submonoid R) :
    PreservesFiniteLimits (baseChangeFunctor R (Localization U)) :=
  preservesFiniteLimits_of_natIso (baseChangeLocalizationIso U).symm

instance baseChangeLocalization_preservesFiniteColimits (U : Submonoid R) :
    PreservesFiniteColimits (baseChangeFunctor R (Localization U)) :=
  preservesFiniteColimits_of_natIso (baseChangeLocalizationIso U).symm

def localizationHomologyIso (U : Submonoid R) (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (((baseChangeFunctor R (Localization U)).mapHomologicalComplex _).obj F).homology i ≅
      ModuleCat.of (Localization U) (Localization U ⊗[R] F.homology i) :=
  (F.sc i).mapHomologyIso (baseChangeFunctor R (Localization U))

lemma localizationHomology_subsingleton_iff (U : Submonoid R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    IsZero ((((baseChangeFunctor R (Localization U)).mapHomologicalComplex _).obj F).homology i) ↔
      Subsingleton (LocalizedModule U (F.homology i)) := by
  let e := (localizationHomologyIso U F i).toLinearEquiv
  let e' := (IsLocalizedModule.isBaseChange U (Localization U)
    (LocalizedModule.mkLinearMap U (F.homology i))).equiv
  rw [ModuleCat.isZero_iff_subsingleton]
  exact (e.toEquiv.trans e'.toEquiv).subsingleton_congr

lemma acyclic_of_contractible {A : Type u} [CommRing A]
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (H : Homotopy (𝟙 F) 0) : F.Acyclic := by
  intro i
  rw [F.exactAt_iff_isZero_homology i]
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have he := H.homologyMap_eq i
  rw [homologyMap_id,homologyMap_zero] at he
  refine ⟨fun x y => ?_⟩
  have hx := ConcreteCategory.congr_hom he x
  have hy := ConcreteCategory.congr_hom he y
  exact hx.trans hy.symm

 

def ContractibleOff (I : Ideal R) (F : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  ∀ p : PrimeSpectrum R, ¬ I≤p.asIdeal → Nonempty (Homotopy
    (𝟙 (((baseChangeFunctor R (Localization.AtPrime p.asIdeal)).mapHomologicalComplex _).obj F)) 0)

lemma ContractibleOff.acyclicAway {I : Ideal R} {F : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : ContractibleOff I F) (z : R) (hz : z∈I) :
    (((baseChangeFunctor R (Localization.Away z)).mapHomologicalComplex _).obj F).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    localizationHomology_subsingleton_iff,LocalizedModule.subsingleton_iff_support_subset]
  intro p hp
  have hi : I≤p.asIdeal := by
    by_contra hn
    obtain ⟨H⟩ := h p hn
    have ha := acyclic_of_contractible _ H i
    rw [HomologicalComplex.exactAt_iff_isZero_homology,
      localizationHomology_subsingleton_iff] at ha
    exact (Module.notMem_support_iff.mpr ha) hp
  intro a ha
  exact (Set.mem_singleton_iff.mp ha) ▸ hi hz

 

def LocallyContractibleOff (I : Ideal R) (F : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  ∀ p : PrimeSpectrum R, ¬ I≤p.asIdeal → ∃ f : R,f∉p.asIdeal ∧ Nonempty (Homotopy
    (𝟙 (((baseChangeFunctor R (Localization.Away f)).mapHomologicalComplex _).obj F)) 0)

lemma LocallyContractibleOff.acyclicAway {I : Ideal R} {F : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : LocallyContractibleOff I F) (z : R) (hz : z∈I) :
    (((baseChangeFunctor R (Localization.Away z)).mapHomologicalComplex _).obj F).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    localizationHomology_subsingleton_iff,LocalizedModule.subsingleton_iff_support_subset]
  intro p hp
  have hi : I≤p.asIdeal := by
    by_contra hn
    obtain ⟨f,hf,⟨H⟩⟩ := h p hn
    have ha := acyclic_of_contractible _ H i
    rw [HomologicalComplex.exactAt_iff_isZero_homology,
      localizationHomology_subsingleton_iff,LocalizedModule.subsingleton_iff_support_subset] at ha
    exact hf (ha hp (Set.mem_singleton f))
  intro a ha
  exact (Set.mem_singleton_iff.mp ha) ▸ hi hz
end Lech

end

end OAI
