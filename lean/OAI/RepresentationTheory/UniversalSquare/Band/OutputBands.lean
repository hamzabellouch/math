import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalancePacking

namespace OAI

/-! Output Bands. -/

section

noncomputable section
namespace Saxl.Balance

structure OutputBands where
  starts : Finset ℕ
  upper : ℕ → ℕ
  nonempty : ∀ k ∈ starts, k ≤ upper k
  separated : ∀ k ∈ starts, ∀ l ∈ starts, k < l → upper k < l

def OutputBands.Allows (B : OutputBands) (x : ℕ) : Prop :=
  ∃ k ∈ B.starts, k ≤ x ∧ x ≤ B.upper k

def OutputBands.label (B : OutputBands) (x : ℕ) : ℕ := by
  classical
  exact if h : B.Allows x then Classical.choose h else 0

lemma OutputBands.label_spec (B : OutputBands) {x : ℕ} (h : B.Allows x) :
    B.label x ∈ B.starts ∧ B.label x ≤ x ∧ x ≤ B.upper (B.label x) := by
  rw [OutputBands.label,dite_eq_left h]
  exact Classical.choose_spec h

lemma OutputBands.unique (B : OutputBands) {x k l : ℕ}
    (hk : k ∈ B.starts) (hl : l ∈ B.starts)
    (hkx : k ≤ x) (hxk : x ≤ B.upper k) (hlx : l ≤ x) (hxl : x ≤ B.upper l) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · have := B.separated k hk l hl h
    omega
  · exact h
  · have := B.separated l hl k hk h
    omega

lemma OutputBands.label_iff (B : OutputBands) {k x : ℕ} (hk : k ∈ B.starts) :
    (B.Allows x ∧ B.label x = k) ↔ x ∈ Set.Icc k (B.upper k) := by
  constructor
  · rintro ⟨hx,hk'⟩
    have h := B.label_spec hx
    rw [hk'] at h
    exact h.2
  · rintro ⟨hkx,hxk⟩
    have hx : B.Allows x := ⟨k,hk,hkx,hxk⟩
    have h := B.label_spec hx
    exact ⟨hx,B.unique h.1 hk h.2.1 h.2.2 hkx hxk⟩

lemma OutputBands.ordered (B : OutputBands) {x y : ℕ}
    (hx : B.Allows x) (hy : B.Allows y) (hxy : B.label x < B.label y) : x < y := by
  have hx' := B.label_spec hx
  have hy' := B.label_spec hy
  exact lt_of_le_of_lt hx'.2.2 ((B.separated _ hx'.1 _ hy'.1 hxy).trans_le hy'.2.1)

def OutputBands.alphabet (B : OutputBands) (d : ℕ) : Fin (d*d) → Prop :=
  fun a => B.Allows (output a)

def OutputBands.letterLabel (B : OutputBands) (d : ℕ) : Fin (d*d) → ℕ :=
  fun a => B.label (output a)

lemma OutputBands.letter_iff (B : OutputBands) {d k : ℕ} (hk : k ∈ B.starts)
    (a : Fin (d*d)) :
    (B.alphabet d a ∧ B.letterLabel d a = k) ↔ output a ∈ Set.Icc k (B.upper k) :=
  B.label_iff hk

lemma OutputBands.letter_ordered (B : OutputBands) (d : ℕ) :
    ∀ x y, B.alphabet d x → B.alphabet d y →
      B.letterLabel d x < B.letterLabel d y → output x < output y := by
  intro x y hx hy h
  exact B.ordered hx hy h

end Saxl.Balance
end
end

end OAI
