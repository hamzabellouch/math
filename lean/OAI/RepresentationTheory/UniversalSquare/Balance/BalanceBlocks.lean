import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPackingPieri
import OAI.RepresentationTheory.UniversalSquare.Balance.EmptyPacking

namespace OAI

/-! Balance Blocks. -/

section

noncomputable section
namespace Saxl.Balance

def bigColumns (q δ : ℕ) : List ℕ := [q+1+δ,q] ++ List.replicate (1+δ) 1

def bigParts (q δ : ℕ) : List ℕ := balancedParts (2*q+1+3*δ) 4 ++ oneIf 1 (1-δ)

def bigUpper (q δ : ℕ) : ℕ := if δ = 0 then q+1 else 2*q+3

theorem WordPacking.bigBlock {q δ d : ℕ} (hq : 3 ≤ q) (hδ : δ ≤ 1)
    (hd : q+1+δ ≤ d) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ z, (A z ∧ label z = q) ↔ output z ∈ Set.Icc q (bigUpper q δ))
    (he1 : ∀ z, (A z ∧ label z = 1) ↔ output z = 1) :
    Nonempty (WordPacking (bigColumns q δ) (bigParts q δ) d A label {q,1}) := by
  rcases (by omega : δ = 0 ∨ δ = 1) with rfl | rfl
  · obtain ⟨P⟩ := WordPacking.neighbor (by omega : 0 < q) (by omega)
      (balancedParts_sum (2*q+1) 4 (by decide)) (by simp) q A label he
    obtain ⟨Q⟩ := WordPacking.repeated (m := 1) (k := 1) (by decide) (by decide)
      (by omega) 1 A label he1
    have hh : Disjoint ({q}:Finset ℕ) {1} := by simp; omega
    simpa [bigColumns,bigParts,oneIf] using Nonempty.intro (P.join Q hh)
  · have heq : 2*q+1+3*1 = 2*q+4 := by omega
    have heq' : q+1+1 = q+2 := by omega
    obtain ⟨P⟩ := WordPacking.twoPaths hq (by omega)
      (balancedParts_sum (2*q+4) 4 (by decide)) (by simp) q 1 (by omega) A label he he1
    simpa [bigColumns,bigParts,heq,heq',oneIf]
      using Nonempty.intro P

def shortColumns (m τ : ℕ) : List ℕ := List.replicate m 2 ++ oneIf 3 τ

def shortParts (m τ : ℕ) : List ℕ := if τ = 0 then [2*m] else balancedParts (2*m+3) 2

def shortMarks (τ : ℕ) : Finset ℕ := if τ = 0 then {2} else {2,3}

theorem WordPacking.shortBlock {m τ d : ℕ} (hm : 1 ≤ m) (hτm : τ ≠ 0 → 2 ≤ m) (hd : 3 ≤ d)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he2 : ∀ z, (A z ∧ label z = 2) ↔ output z = 2)
    (he3 : τ ≠ 0 → ∀ z, (A z ∧ label z = 3) ↔ output z = 3) :
    Nonempty (WordPacking (shortColumns m τ) (shortParts m τ) d A label (shortMarks τ)) := by
  by_cases hτ : τ = 0
  · obtain ⟨P⟩ := WordPacking.repeated (m := m) (k := 2) (by omega) (by decide)
      (by omega) 2 A label he2
    simpa only [shortColumns,shortParts,shortMarks,oneIf,ite_eq_left hτ,List.append_nil,
      Nat.mul_comm m 2] using Nonempty.intro P
  · have hm2 := hτm hτ
    obtain ⟨P⟩ := WordPacking.twosOdd (m := m) (x := 3) (by omega) (by decide)
      (by omega) (by omega) hd (balancedParts_sum (2*m+3) 2 (by decide)) (by simp)
      2 3 (by decide) A label he2 (he3 hτ)
    simpa only [shortColumns,shortParts,shortMarks,oneIf,ite_eq_right hτ] using Nonempty.intro P

lemma bigParts_length {q δ : ℕ} (hδ : δ ≤ 1) : (bigParts q δ).length = 5-δ := by
  simp only [bigParts,List.length_append,balancedParts_length,oneIf]
  split_ifs <;> simp_all <;> omega

lemma shortParts_length {m τ : ℕ} (hτ : τ ≤ 1) : (shortParts m τ).length = 1+τ := by
  simp only [shortParts]
  split_ifs <;> simp_all
  omega

lemma oneIf_length {x ε : ℕ} (hε : ε ≤ 1) : (oneIf x ε).length = ε := by
  unfold oneIf
  split_ifs <;> simp_all
  omega

lemma mem_shortMarks {τ k : ℕ} (hk : k ∈ shortMarks τ) : k = 2 ∨ (τ ≠ 0 ∧ k = 3) := by
  unfold shortMarks at hk
  split_ifs at hk with hτ
  · simp only [Finset.mem_singleton] at hk
    exact Or.inl hk
  · simpa only [Finset.mem_insert,Finset.mem_singleton,hτ,true_and] using
      (show k = 2 ∨ (τ ≠ 0 ∧ k = 3) from
        (by rcases Finset.mem_insert.mp hk with h | h
            · exact Or.inl h
            · exact Or.inr ⟨hτ, Finset.mem_singleton.mp h⟩))

lemma mem_markIf {x ε k : ℕ} (hk : k ∈ markIf x ε) : ε ≠ 0 ∧ k = x := by
  unfold markIf at hk
  split_ifs at hk with hε
  · simp at hk
  · exact ⟨hε,Finset.mem_singleton.mp hk⟩

end Saxl.Balance
end
end

end OAI
