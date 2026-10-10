import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Identity
import OAI.Topology.ArtinGroups.Complexes.MinimalEmbedding
import OAI.Topology.ArtinGroups.Quivers.LengthCases
import OAI.Topology.ArtinGroups.Complexes.NegativeAmplitudeCoreIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma reducedNegativeAmplitudeTwist_level (E : BasedComplex Q (K := K) I) (α : V)
    (k : NegativeAmplitudeCoreIndex Q E α) :
    ∃ i : I,
      ((reducedNegativeAmplitudeTwist Q E α).placement k).level = (E.placement i).level ∨
      (((reducedNegativeAmplitudeTwist Q E α).placement k).level = (E.placement i).level - 1 ∧
        ((reducedNegativeAmplitudeTwist Q E α).placement k).color = α) := by
  rw [reducedNegativeAmplitudeTwist_placement]
  rcases k with u | i
  · refine ⟨u.val.1, ?_⟩
    have h := Path.length_cases u.val.2.val
    have hn := u.property
    dsimp only [GeneratorPlacement.level]
    rcases h with h | h | h
    · exact Or.inr ⟨by omega, rfl⟩
    · exact Or.inl (by omega)
    · exact (hn h).elim
  · exact ⟨i.val, Or.inl rfl⟩

theorem negativeTwist_interval (E : BasedComplex Q (K := K) I) (α : V) (a b : ℤ)
    (hE : ∀ i, a ≤ (E.placement i).level ∧ (E.placement i).level ≤ b) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q (E.negativeTwist Q α) F.complex) ∧
      ∀ j, a - 1 ≤ (F.complex.placement j).level ∧ (F.complex.placement j).level ≤ b := by
  let B := FiniteModel.ofComplex Q (reducedNegativeAmplitudeTwist Q E α)
  obtain ⟨F, hF, ⟨e⟩, f, hf⟩ := B.exists_minimal_embedding Q
  refine ⟨F, hF, ⟨(negativeAmplitudeTwistReduction Q E α).trans Q e⟩, ?_⟩
  intro j
  rw [hf j]
  obtain ⟨i, hi⟩ := reducedNegativeAmplitudeTwist_level Q E α (f j)
  have hb := hE i
  change a - 1 ≤ ((reducedNegativeAmplitudeTwist Q E α).placement (f j)).level ∧
    ((reducedNegativeAmplitudeTwist Q E α).placement (f j)).level ≤ b
  rcases hi with hi | ⟨hi, _⟩ <;> omega

theorem negativeTwist_pure (E : BasedComplex Q (K := K) I) (α : V) (d : ℤ)
    (hE : ∀ i, (E.placement i).level = d) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q (E.negativeTwist Q α) F.complex) ∧
      ∀ j, (F.complex.placement j).level = d ∨
        ((F.complex.placement j).level = d - 1 ∧ (F.complex.placement j).color = α) := by
  let B := FiniteModel.ofComplex Q (reducedNegativeAmplitudeTwist Q E α)
  obtain ⟨F, hF, ⟨e⟩, f, hf⟩ := B.exists_minimal_embedding Q
  refine ⟨F, hF, ⟨(negativeAmplitudeTwistReduction Q E α).trans Q e⟩, ?_⟩
  intro j
  rw [hf j]
  obtain ⟨i, hi⟩ := reducedNegativeAmplitudeTwist_level Q E α (f j)
  change ((reducedNegativeAmplitudeTwist Q E α).placement (f j)).level = d ∨
    (((reducedNegativeAmplitudeTwist Q E α).placement (f j)).level = d - 1 ∧
      ((reducedNegativeAmplitudeTwist Q E α).placement (f j)).color = α)
  simpa only [hE i] using hi

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
