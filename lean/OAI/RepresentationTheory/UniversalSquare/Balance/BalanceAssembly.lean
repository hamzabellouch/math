import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.RunBands
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceBlocks

namespace OAI

/-! Balance Assembly. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

def balanceColumns (M b δ τ ε m : ℕ) : List ℕ :=
  ((bigColumns (M-1+b) δ ++ shortColumns (b+1) τ) ++
    pairColumns (3+τ+ε) m) ++ oneIf (3+τ) ε

def balanceParts (M b δ τ ε m : ℕ) : List ℕ :=
  ((bigParts (M-1+b) δ ++ shortParts (b+1) τ) ++
    pairParts (3+τ+ε) m) ++ oneIf (3+τ) ε

theorem balancePacking {M b δ τ ε m : ℕ}
    (hM : 4 ≤ M) (hδ : δ ≤ 1) (hτ : τ ≤ 1) (hε : ε ≤ 1)
    (heq : M = 4+τ+ε+2*m) (hshort : τ ≠ 0 → 1 ≤ b) :
    ∃ (A : Fin ((M+b+δ)*(M+b+δ)) → Prop)
      (label : Fin ((M+b+δ)*(M+b+δ)) → ℕ) (marks : Finset ℕ),
      (∀ x y, A x → A y → label x < label y → output x < output y) ∧
      Nonempty (WordPacking (balanceColumns M b δ τ ε m)
        (balanceParts M b δ τ ε m) (M+b+δ) A label marks) := by
  let a := 3+τ+ε
  let q := M-1+b
  let lo := 3+τ
  let d := M+b+δ
  have hg : a+2*m ≤ q := by dsimp [a,q]; omega
  have hU : q ≤ bigUpper q δ := by unfold bigUpper; split_ifs <;> omega
  let B := runBands a m q (bigUpper q δ) hg hU
  let A := B.alphabet d
  let label := B.letterLabel d
  have he1 : ∀ z, (A z ∧ label z = 1) ↔ output z = 1 :=
    fun z => runBands_low_iff hg hU (by dsimp [a]; omega) z
  obtain ⟨P⟩ := WordPacking.bigBlock (by dsimp [q]; omega : 3 ≤ q) hδ
    (by dsimp [q,d]; omega) A label (fun z => runBands_top_iff hg hU z) he1
  have he2 : ∀ z, (A z ∧ label z = 2) ↔ output z = 2 :=
    fun z => runBands_low_iff hg hU (by dsimp [a]; omega) z
  obtain ⟨Q⟩ := WordPacking.shortBlock (by omega : 1 ≤ b+1)
    (by intro h; have := hshort h; omega) (by dsimp [d]; omega)
    A label he2 (by
      intro ht z
      exact runBands_low_iff hg hU (by dsimp [a]; omega) z)
  obtain ⟨R⟩ := WordPacking.pairRunAny (by dsimp [a]; omega : 2 ≤ a)
    (by dsimp [a,d]; omega) A label
    (fun k hk z => runBands_pair_iff hg hU hk z)
  obtain ⟨S⟩ := WordPacking.optional (by dsimp [lo]; omega : 0 < lo)
    (by dsimp [lo,d]; omega) A label (ε := ε) (by
      intro h z
      exact runBands_low_iff hg hU (by dsimp [lo,a]; omega) z)
  have hpq : Disjoint ({q,1}:Finset ℕ) (shortMarks τ) := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    have hl := mem_shortMarks hl
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    dsimp [q] at hk
    omega
  have hpqr : Disjoint (({q,1}:Finset ℕ) ∪ shortMarks τ) (pairMarks a m) := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    have hh := pairMarks_bound hl
    rcases Finset.mem_union.mp hk with hk | hk
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      dsimp [a,q] at hh hk
      omega
    · have hk := mem_shortMarks hk
      dsimp [a] at hh
      omega
  have hd : Disjoint ((({q,1}:Finset ℕ) ∪ shortMarks τ) ∪ pairMarks a m)
      (markIf lo ε) := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    have hl := mem_markIf hl
    rcases Finset.mem_union.mp hk with hk | hk
    · rcases Finset.mem_union.mp hk with hk | hk
      · simp only [Finset.mem_insert,Finset.mem_singleton] at hk
        dsimp [q,lo] at hk hl
        omega
      · have hk := mem_shortMarks hk
        dsimp [lo] at hl
        omega
    · have hh := pairMarks_bound hk
      dsimp [a,lo] at hh hl
      omega
  exact ⟨A,label,_,B.letter_ordered _,⟨((P.join Q hpq).join R hpqr).join S hd⟩⟩

lemma balanceParts_length {M b δ τ ε m : ℕ}
    (hδ : δ ≤ 1) (hτ : τ ≤ 1) (hε : ε ≤ 1) (heq : M = 4+τ+ε+2*m) :
    2*M-5 ≤ (balanceParts M b δ τ ε m).length := by
  rw [balanceParts,List.length_append,List.length_append,List.length_append,
    bigParts_length hδ,shortParts_length hτ,pairParts_length,oneIf_length hε]
  omega

lemma oneIf_mem {x ε p : ℕ} (hp : p ∈ oneIf x ε) : p = x := by
  unfold oneIf at hp
  split_ifs at hp
  · simp at hp
  · exact List.mem_singleton.mp hp

lemma balanceParts_positive {M b δ τ ε m : ℕ} (hM : 4 ≤ M) :
    ∀ p ∈ balanceParts M b δ τ ε m, 0 < p := by
  intro p hp
  simp only [balanceParts,List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact balancedParts_pos (by decide) (by omega) p hp
    · have := oneIf_mem hp; omega
  · unfold shortParts at hp
    split_ifs at hp
    · have := List.mem_singleton.mp hp; omega
    · exact balancedParts_pos (by decide) (by omega) p hp
  · exact pairParts_positive (by omega) p hp
  · have := oneIf_mem hp; omega

lemma balanceParts_bound {M b δ τ ε m p : ℕ}
    (hM : 4 ≤ M) (hb : b ≤ M-2) (hδ : δ ≤ 1) (hτ : τ ≤ 1) (hε : ε ≤ 1)
    (heq : M = 4+τ+ε+2*m) (hsmall : τ = 0 → 2*(b+1) ≤ M)
    (hp : p ∈ balanceParts M b δ τ ε m) : p ≤ M+1 := by
  simp only [balanceParts,List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · rcases List.mem_append.mp hp with hp | hp
    · have hh := (balancedParts_part hp).2
      omega
    · have := oneIf_mem hp; omega
  · unfold shortParts at hp
    split_ifs at hp with ht
    · have := List.mem_singleton.mp hp
      have := hsmall ht
      omega
    · have hh := (balancedParts_part hp).2
      omega
  · have := pairParts_bound (by omega : 2 ≤ 3+τ+ε) hp
    omega
  · have := oneIf_mem hp; omega

end Saxl.Balance
end
end

end OAI
