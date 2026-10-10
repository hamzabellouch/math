import Mathlib
import OAI.RingTheory.Multiplicity.DuttaFrobeniusShift
import OAI.RingTheory.Multiplicity.FlatLocalSupport

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex IsLocalRing
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def frobeniusBaseChangeIso (p : ℕ) [Fact p.Prime] [CharP R p] [CharP S p]
    (φ : R →+* S) (F : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj
      (frobeniusComplex R p n F)) ≅
      frobeniusComplex S p n (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj F) := by
  have he : φ.comp (iterateFrobenius R p n)=(iterateFrobenius S p n).comp φ := by
    ext x
    change φ (x^(p^n))=(φ x)^(p^n)
    exact map_pow φ x _
  have e := ((NatIso.mapHomologicalComplex
    (ModuleCat.extendScalarsComp (iterateFrobenius R p n) φ) (.up ℤ)).app F).symm
  rw [he] at e
  exact e ≪≫ (NatIso.mapHomologicalComplex
    (ModuleCat.extendScalarsComp φ (iterateFrobenius S p n)) (.up ℤ)).app F

variable [IsLocalRing R] [IsLocalRing S] [Algebra R S]
  [Module.Flat R S] [IsLocalHom (algebraMap R S)]

lemma flat_homology_length (hmax : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Module.length S ((((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex
      (.up ℤ)).obj F).homology i)=Module.length R (F.homology i) := by
  let E := ModuleCat.extendScalars (algebraMap R S)
  let : PreservesFiniteLimits E := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  rw [(flatExtensionHomologyIso (algebraMap R S)
    (RingHom.flat_algebraMap_iff.mpr inferInstance) F i).toLinearEquiv.length_eq]
  let φ := algebraMap R S
  have hflat : φ.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let := φ.toAlgebra
  let : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  change Module.length S (S ⊗[R] (F.homology i))=_
  rw [IsLocalRing.length_baseChange R S (F.homology i)]
  change Module.length R (F.homology i) * Module.length S (S ⧸ (maximalIdeal R).map φ)=_
  have hm : (maximalIdeal R).map φ=maximalIdeal S := hmax
  rw [hm]
  let : IsSimpleModule S (S ⧸ maximalIdeal S) := isSimpleModule_iff_quot_maximal.mpr
    ⟨maximalIdeal S,inferInstance,⟨LinearEquiv.refl S _⟩⟩
  rw [Module.length_eq_one (R:=S) (M:=S ⧸ maximalIdeal S),mul_one]

variable [IsNoetherianRing R] [IsNoetherianRing S]
lemma dimension_eq_of_map_maximalIdeal
    (hmax : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S) : dimension S=dimension R := by
  unfold dimension
  rw [ringKrullDim_eq_of_map_maximalIdeal hmax]

lemma duttaSequence_baseChange (p : ℕ) [Fact p.Prime] [CharP R p] [CharP S p]
    (hmax : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    duttaSequence S p (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex
      (.up ℤ)).obj F) n=duttaSequence R p F n := by
  unfold duttaSequence shortEuler
  rw [dimension_eq_of_map_maximalIdeal hmax]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have he := (homologyMapIso (frobeniusBaseChangeIso p (algebraMap R S) F n) (-(i:ℤ))).toLinearEquiv.length_eq
  rw [← he,flat_homology_length hmax]

lemma shortComplex_baseChange
    (hmax : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F) :
    IsShortComplex S (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex
      (.up ℤ)).obj F) := by
  let G := (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.up ℤ)).obj F)
  have hG := finiteHomology_extendScalars (algebraMap R S)
    (dimension_eq_of_map_maximalIdeal hmax)
    (by rw [hmax]; exact Ideal.IsPrime.radical inferInstance) F hF.finiteHomology
  refine ⟨hG.term_free,hG.term_finite,hG.bounded,hG.homology_finite_length,?_⟩
  intro hz
  have : Subsingleton (G.homology 0) := ModuleCat.isZero_iff_subsingleton.mp hz
  have he : Module.length R (F.homology 0)=0 :=
    (flat_homology_length hmax F 0).symm.trans (Module.length_eq_zero (R:=S) (M:=G.homology 0))
  exact hF.homology_zero_nonzero
    (ModuleCat.isZero_iff_subsingleton.mpr (Module.length_eq_zero_iff.mp he))

end Lech

end

end OAI
