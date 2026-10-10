import Mathlib
import OAI.RingTheory.Multiplicity.MinimalComplexReduction
import OAI.RingTheory.Multiplicity.ScalarExtensionHomotopy

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
theorem exists_minimal_complex (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsFiniteHomologyComplex R F) :
    ∃ G : CochainComplex (ModuleCat.{u} R) ℤ,
      IsFiniteHomologyComplex R G ∧ IsMinimalComplex G ∧ Nonempty (HomotopyEquiv F G) := by
  classical
  have H (b : ℕ) : ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ), complexRankSum F = b →
      IsFiniteHomologyComplex R F →
      ∃ G : CochainComplex (ModuleCat.{u} R) ℤ,
        IsFiniteHomologyComplex R G ∧ IsMinimalComplex G ∧ Nonempty (HomotopyEquiv F G) := by
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro F hb hF
      by_cases hm : IsMinimalComplex F
      · exact ⟨F,hF,hm,⟨HomotopyEquiv.refl F⟩⟩
      obtain ⟨G,hG,⟨e⟩,hsize⟩ := nonminimal_complex_reduction F hF hm
      obtain ⟨K,hK,hmK,⟨e'⟩⟩ := ih (complexRankSum G) (hb ▸ hsize) G rfl hG
      exact ⟨K,hK,hmK,⟨e.trans e'⟩⟩
  exact H _ F rfl hF

theorem IsShortComplex.exists_minimal {F : CochainComplex (ModuleCat.{u} R) ℤ}
    (hF : IsShortComplex R F) :
    ∃ G : CochainComplex (ModuleCat.{u} R) ℤ,
      IsShortComplex R G ∧ IsMinimalComplex G ∧ Nonempty (HomotopyEquiv F G) := by
  obtain ⟨G,hG,hm,⟨e⟩⟩ := exists_minimal_complex F hF.finiteHomology
  refine ⟨G,⟨hG.term_free,hG.term_finite,hG.bounded,hG.homology_finite_length,?_⟩,hm,⟨e⟩⟩
  intro hz
  exact hF.homology_zero_nonzero (hz.of_iso (e.toHomologyIso 0))

omit [IsLocalRing R] [IsNoetherianRing R]
lemma shortEuler_eq_of_homotopyEquiv {F G : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : HomotopyEquiv F G) : shortEuler R F = shortEuler R G := by
  unfold shortEuler
  apply Finset.sum_congr rfl
  intro j _
  rw [(e.toHomologyIso (-(j:ℤ))).toLinearEquiv.length_eq]

lemma duttaSequence_eq_of_homotopyEquiv (p : ℕ) [Fact p.Prime] [CharP R p]
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (e : HomotopyEquiv F G) :
    duttaSequence R p F = duttaSequence R p G := by
  funext n
  unfold duttaSequence frobeniusComplex
  rw [shortEuler_eq_of_homotopyEquiv
    ((ModuleCat.extendScalars (iterateFrobenius R p n)).mapHomotopyEquiv e)]

lemma duttaMultiplicity_eq_of_homotopyEquiv (p : ℕ) [Fact p.Prime] [CharP R p]
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (e : HomotopyEquiv F G) :
    duttaMultiplicity R p F = duttaMultiplicity R p G := by
  unfold duttaMultiplicity
  rw [duttaSequence_eq_of_homotopyEquiv p e]
end Lech

end

end OAI
