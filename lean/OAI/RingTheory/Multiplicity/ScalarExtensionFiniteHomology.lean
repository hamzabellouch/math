import Mathlib
import OAI.RingTheory.Multiplicity.RobertsSeparable

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
  [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]

lemma finiteHomology_extendScalars (φ : R →+* S)
    (hd : dimension S = dimension R)
    (hφ : ((IsLocalRing.maximalIdeal R).map φ).radical = IsLocalRing.maximalIdeal S)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    IsFiniteHomologyComplex S (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj F) := by
  let G := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj F
  refine ⟨fun i => ?_,fun i => ?_,fun i hi => ?_,fun i => ?_⟩
  · have := hF.term_free i
    exact free_extendScalars φ (F.X i)
  · have := hF.term_finite i
    exact finite_extendScalars φ (F.X i)
  · exact (ModuleCat.extendScalars φ).map_isZero (hF.bounded i (by simpa only [hd] using hi))
  · have := hF.term_finite i
    have : Module.Finite S (G.X i) := finite_extendScalars φ (F.X i)
    have := finite_cochain_homology G i
    apply finiteLength_of_maximal_le_radical_annihilator
    rw [← hφ]
    apply le_trans (Ideal.radical_mono (J := (Module.annihilator S (G.homology i)).radical) ?_)
      (by rw [Ideal.radical_idem])
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    obtain ⟨a,ha⟩ := shortComplex_nullScalar_radical F hF hx
    change φ x ∈ (Module.annihilator S (G.homology i)).radical
    refine ⟨a,?_⟩
    have hh := Koszul.scalar_annihilates_homology G (φ (x^a))
      (extendScalars_nullhomotopy φ F (x^a) ha.some) i
    simpa only [map_pow] using hh
end Lech

end

end OAI
