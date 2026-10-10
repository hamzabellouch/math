import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootCech

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
variable (D : Diagram R ι)

lemma complex_zero (hD : IsZero (D.obj ∅)) : IsZero ((complex D).X 0) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun f g => funext fun s => ?_⟩
  have hs : s.val = ∅ := Finset.card_eq_zero.mp s.property
  have hz : IsZero (D.obj s.val) := hs ▸ hD
  exact (ModuleCat.subsingleton_of_isZero hz).elim (f s) (g s)

def positiveSuccScIso (q : ℕ) :
    (positiveComplex D).sc' q (q+1) (q+1+1) ≅
      (complex D).sc' (q+1) (q+1+1) (q+1+1+1) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor',Iso.refl_hom,
          positiveComplex_d,complex_d]
        exact (Category.id_comp (ModuleCat.ofHom (d D (q+1)))).trans (Category.comp_id _).symm)
    (by simp only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor',Iso.refl_hom,
          positiveComplex_d,complex_d]
        exact (Category.id_comp (ModuleCat.ofHom (d D (q+1+1)))).trans (Category.comp_id _).symm)

def positiveZeroScMap :
    (positiveComplex D).sc' 0 0 1 ⟶ (complex D).sc' 0 1 2 where
  τ₁ := 0
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by
    simp only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor']
    exact zero_comp.trans (((positiveComplex D).shape 0 0 (by decide)).symm.trans
      (Category.comp_id _).symm)
  comm₂₃ := by
    simp only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor',
      positiveComplex_d,complex_d]
    exact (Category.id_comp (ModuleCat.ofHom (d D 1))).trans (Category.comp_id _).symm

 

def positiveHomologyIso (hD : IsZero (D.obj ∅)) (q : ℕ) :
    (positiveComplex D).homology q ≅ (complex D).homology (q+1) := by
  cases q with
  | zero =>
      haveI : Epi (positiveZeroScMap D).τ₁ := (complex_zero D hD).epi _
      haveI : IsIso (positiveZeroScMap D).τ₂ := inferInstanceAs (IsIso (𝟙 _))
      haveI : Mono (positiveZeroScMap D).τ₃ := inferInstanceAs (Mono (𝟙 _))
      exact (positiveComplex D).homologyIsoSc' 0 0 1 (by simp) (by simp) ≪≫
        asIso (ShortComplex.homologyMap (positiveZeroScMap D)) ≪≫
          ((complex D).homologyIsoSc' 0 1 2 (by simp) (by simp)).symm
  | succ q =>
      exact (positiveComplex D).homologyIsoSc' q (q+1) (q+1+1) (by simp) (by simp) ≪≫
        ShortComplex.homologyMapIso (positiveSuccScIso D q) ≪≫
          ((complex D).homologyIsoSc' (q+1) (q+1+1) (q+1+1+1) (by simp) (by simp)).symm

end Lech.FiniteModuleCech

end

end OAI
