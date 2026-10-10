import Mathlib
import OAI.RingTheory.Kurosh.WordGrowth

namespace OAI

/-! Finite families of independent bounded-length words. -/

namespace KuroshConstruction

section IndependentWords

variable (I : Type*) [Finite I]

abbrev BoundedWord (n : ℕ) := {w : List I // w.length ≤ n}

noncomputable instance (n : ℕ) : Fintype (BoundedWord I n) :=
  (List.finite_length_le I n).fintype

variable {I} {K A : Type*} [Field K] [Ring A] [Algebra K A]
  [Nontrivial A] [Module.Finite K A]

theorem exists_independent_bounded_words (X : I → A)
    (hgen : Algebra.adjoin K (Set.range X) = ⊤) (n : ℕ)
    (hdim : n+1 ≤ Module.finrank K A) :
    ∃ w : Fin (n+1) → BoundedWord I n,
      LinearIndependent K (fun j => wordValue A I X (w j).val) := by
  classical
  let v : BoundedWord I n → A := fun w => wordValue A I X w.val
  have hr : Set.range v = wordValue A I X '' {w : List I | w.length ≤ n} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩; exact ⟨w.val, w.property, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K v
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : n+1 ≤ Fintype.card κ := by
    rw [← finrank_span_eq_card hli, hsp, hr]
    exact wordSpan_finrank_lower X hgen n hdim
  let b : Fin (n+1) → κ := fun j => (Fintype.equivFin κ).symm (Fin.castLE hcard j)
  refine ⟨a ∘ b, ?_⟩
  exact hli.comp b ((Fintype.equivFin κ).symm.injective.comp (Fin.castLE_injective hcard))

end IndependentWords

end KuroshConstruction

end OAI
