import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Identity

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel

universe u

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

theorem exists_minimal_embedding (E : FiniteModel.{u} Q (K := K)) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q E.complex F.complex) ∧
        ∃ e : F.Index ↪ E.Index, ∀ i, F.complex.placement i = E.complex.placement (e i) := by
  have h : ∀ n (B : FiniteModel.{u} Q (K := K)), Fintype.card B.Index = n →
      ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
        Nonempty (HomotopyEquivalence Q B.complex F.complex) ∧
          ∃ e : F.Index ↪ B.Index,
            ∀ i, F.complex.placement i = B.complex.placement (e i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B hn
      by_cases hm : B.complex.IsMinimal Q
      · exact ⟨B, hm, ⟨HomotopyEquivalence.refl Q B.complex⟩,
          Function.Embedding.refl _, fun _ => rfl⟩
      · obtain ⟨p⟩ := scalarPivot_of_not_minimal Q B.complex hm
        let C := ofComplex Q (p.reduced Q)
        have hc : Fintype.card C.Index < n := by
          dsimp only [C, ofComplex]
          rw [← hn]
          exact p.retained_card_lt Q
        obtain ⟨F, hF, ⟨e⟩, j, hj⟩ := ih (Fintype.card C.Index) hc C rfl
        exact ⟨F, hF, ⟨(p.reductionEquivalence Q).trans Q e⟩,
          j.trans ⟨Subtype.val, Subtype.val_injective⟩, hj⟩
  exact h (Fintype.card E.Index) E rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel

end OAI
