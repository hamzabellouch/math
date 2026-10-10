import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.OutputBands
import OAI.RepresentationTheory.UniversalSquare.Capacity.RefinedExhaustion

namespace OAI

/-! Numeric Bands. -/

section

noncomputable section
namespace Saxl.Balance

def BandsValid (es : List (ℕ × ℕ)) : Prop :=
  (∀ e ∈ es, e.1 ≤ e.2) ∧ ∀ e ∈ es, ∀ f ∈ es,
    (e.1 = f.1 → e.2 = f.2) ∧ (e.1 < f.1 → e.2 < f.1)

instance (es : List (ℕ × ℕ)) : Decidable (BandsValid es) := by
  unfold BandsValid
  infer_instance

def bandStarts (es : List (ℕ × ℕ)) : Finset ℕ := (es.map Prod.fst).toFinset

def bandUpper (es : List (ℕ × ℕ)) (k : ℕ) : ℕ :=
  es.toFinset.sup (fun e => if e.1 = k then e.2 else 0)

lemma bandUpper_eq {es : List (ℕ × ℕ)} (h : BandsValid es) {e : ℕ × ℕ}
    (he : e ∈ es) : bandUpper es e.1 = e.2 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro f hf
    by_cases hf' : f.1 = e.1
    · simp only [ite_eq_left hf']
      exact ((h.2 f (List.mem_toFinset.mp hf) e he).1 hf').le
    · simp only [ite_eq_right hf']; exact Nat.zero_le _
  · have hh := Finset.le_sup (f := fun f : ℕ × ℕ => if f.1 = e.1 then f.2 else 0)
      (List.mem_toFinset.mpr he)
    simpa only [bandUpper, ite_true] using hh

lemma mem_bandStarts {es : List (ℕ × ℕ)} {k : ℕ} :
    k ∈ bandStarts es ↔ ∃ e ∈ es, e.1 = k := by simp [bandStarts]

def numericBands (es : List (ℕ × ℕ)) (h : BandsValid es) : OutputBands where
  starts := bandStarts es
  upper := bandUpper es
  nonempty := by
    intro k hk
    obtain ⟨e,he,rfl⟩ := mem_bandStarts.mp hk
    rw [bandUpper_eq h he]
    exact h.1 e he
  separated := by
    intro k hk l hl hkl
    obtain ⟨e,he,rfl⟩ := mem_bandStarts.mp hk
    obtain ⟨f,hf,rfl⟩ := mem_bandStarts.mp hl
    rw [bandUpper_eq h he]
    exact (h.2 e he f hf).2 hkl

lemma numericBands_iff {es : List (ℕ × ℕ)} (h : BandsValid es) {e : ℕ × ℕ}
    (he : e ∈ es) {d : ℕ} (z : Fin (d*d)) :
    ((numericBands es h).alphabet d z ∧ (numericBands es h).letterLabel d z = e.1) ↔
      output z ∈ Set.Icc e.1 e.2 := by
  rw [(numericBands es h).letter_iff (mem_bandStarts.mpr ⟨e,he,rfl⟩)]
  rw [show (numericBands es h).upper e.1 = e.2 from bandUpper_eq h he]

end Saxl.Balance
end
end

end OAI
