import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Identity
import OAI.Topology.ArtinGroups.Complexes.MinimalEmbedding
import OAI.Topology.ArtinGroups.Complexes.ActedIndex
import OAI.Topology.ArtinGroups.Quivers.LengthCases

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma reducedAmplitudeTwist_level (E : BasedComplex Q (K := K) I) (α : V)
    (k : AmplitudeCoreIndex Q E α) :
    ∃ i : I,
      ((reducedAmplitudeTwist Q E α).placement k).level = (E.placement i).level ∨
      (((reducedAmplitudeTwist Q E α).placement k).level = (E.placement i).level + 1 ∧
        ((reducedAmplitudeTwist Q E α).placement k).color = α) := by
  rw [reducedAmplitudeTwist_placement]
  rcases k with u | i
  · refine ⟨u.val.1, ?_⟩
    have h := Path.length_cases u.val.2.val
    have hn := u.property
    dsimp only [GeneratorPlacement.level]
    rcases h with h | h | h
    · exact (hn h).elim
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, rfl⟩
  · exact ⟨i.val, Or.inl rfl⟩

theorem positiveTwist_interval (E : BasedComplex Q (K := K) I) (α : V) (a b : ℤ)
    (hE : ∀ i, a ≤ (E.placement i).level ∧ (E.placement i).level ≤ b) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q (E.positiveTwist Q α) F.complex) ∧
      ∀ j, a ≤ (F.complex.placement j).level ∧ (F.complex.placement j).level ≤ b + 1 := by
  let B := FiniteModel.ofComplex Q (reducedAmplitudeTwist Q E α)
  obtain ⟨F, hF, ⟨e⟩, f, hf⟩ := B.exists_minimal_embedding Q
  refine ⟨F, hF, ⟨(amplitudeTwistReduction Q E α).trans Q e⟩, ?_⟩
  intro j
  rw [hf j]
  obtain ⟨i, hi⟩ := reducedAmplitudeTwist_level Q E α (f j)
  have hb := hE i
  change a ≤ ((reducedAmplitudeTwist Q E α).placement (f j)).level ∧
    ((reducedAmplitudeTwist Q E α).placement (f j)).level ≤ b + 1
  rcases hi with hi | ⟨hi, _⟩ <;> omega

theorem positiveTwist_pure (E : BasedComplex Q (K := K) I) (α : V) (d : ℤ)
    (hE : ∀ i, (E.placement i).level = d) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q (E.positiveTwist Q α) F.complex) ∧
      ∀ j, (F.complex.placement j).level = d ∨
        ((F.complex.placement j).level = d + 1 ∧ (F.complex.placement j).color = α) := by
  let B := FiniteModel.ofComplex Q (reducedAmplitudeTwist Q E α)
  obtain ⟨F, hF, ⟨e⟩, f, hf⟩ := B.exists_minimal_embedding Q
  refine ⟨F, hF, ⟨(amplitudeTwistReduction Q E α).trans Q e⟩, ?_⟩
  intro j
  rw [hf j]
  obtain ⟨i, hi⟩ := reducedAmplitudeTwist_level Q E α (f j)
  change ((reducedAmplitudeTwist Q E α).placement (f j)).level = d ∨
    (((reducedAmplitudeTwist Q E α).placement (f j)).level = d + 1 ∧
      ((reducedAmplitudeTwist Q E α).placement (f j)).color = α)
  simpa only [hE i] using hi

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
