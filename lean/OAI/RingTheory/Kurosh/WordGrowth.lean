import Mathlib

namespace OAI

/-! Growth and stabilization of spans of bounded-length words. -/

namespace KuroshConstruction

section WordGrowth

variable (K A I : Type*) [Field K] [Ring A] [Algebra K A]

noncomputable def wordValue (X : I → A) (w : List I) : A := (w.map X).prod

noncomputable def wordSpan (X : I → A) (n : ℕ) : Submodule K A :=
  Submodule.span K (wordValue A I X '' {w : List I | w.length ≤ n})

variable {K A I}

lemma word_mem_wordSpan (X : I → A) {n : ℕ} {w : List I} (hw : w.length ≤ n) :
    wordValue A I X w ∈ wordSpan K A I X n :=
  Submodule.subset_span ⟨w, hw, rfl⟩

lemma one_mem_wordSpan (X : I → A) (n : ℕ) : 1 ∈ wordSpan K A I X n := by
  simpa [wordValue] using word_mem_wordSpan (K := K) X (w := []) (n := n) (by simp)

lemma wordSpan_mono (X : I → A) {m n : ℕ} (hmn : m ≤ n) :
    wordSpan K A I X m ≤ wordSpan K A I X n := by
  apply Submodule.span_mono
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, hw.trans hmn, rfl⟩

lemma generator_mul_wordSpan (X : I → A) (n : ℕ) (c : I) (z : A)
    (hz : z ∈ wordSpan K A I X n) : X c * z ∈ wordSpan K A I X (n+1) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, hw, rfl⟩ := hz
    simpa [wordValue] using word_mem_wordSpan (K := K) X (w := c :: w)
      (n := n+1) (by simpa using Nat.succ_le_succ hw)
  | zero => simp
  | add z t _ _ hz ht => simpa [mul_add] using (wordSpan K A I X (n+1)).add_mem hz ht
  | smul r z _ hz => simpa [mul_smul_comm] using (wordSpan K A I X (n+1)).smul_mem r hz

lemma wordSpan_stabilizes (X : I → A)
    (hgen : Algebra.adjoin K (Set.range X) = ⊤) (n : ℕ)
    (he : wordSpan K A I X n = wordSpan K A I X (n+1)) :
    wordSpan K A I X n = ⊤ := by
  apply top_unique
  have hle : (Algebra.adjoin K (Set.range X)).toSubmodule ≤ wordSpan K A I X n := by
    rw [Algebra.adjoin_eq_span]
    apply Submodule.span_le.mpr
    intro z hz
    induction hz using Submonoid.closure_induction_left with
    | one => exact one_mem_wordSpan X n
    | mul_left z hz t _ ht =>
      obtain ⟨c, rfl⟩ := hz
      rw [he]
      exact generator_mul_wordSpan X n c t ht
  simpa [hgen] using hle

lemma wordSpan_finrank_lower [Nontrivial A] [Module.Finite K A]
    (X : I → A) (hgen : Algebra.adjoin K (Set.range X) = ⊤) (n : ℕ)
    (hdim : n+1 ≤ Module.finrank K A) :
    n+1 ≤ Module.finrank K (wordSpan K A I X n) := by
  induction n with
  | zero =>
    have hh : Submodule.span K ({1} : Set A) ≤ wordSpan K A I X 0 :=
      Submodule.span_le.mpr (by simpa using one_mem_wordSpan (K := K) X 0)
    simpa [finrank_span_singleton one_ne_zero] using Submodule.finrank_mono hh
  | succ n ih =>
    by_cases he : wordSpan K A I X n = wordSpan K A I X (n+1)
    · have ht := wordSpan_stabilizes X hgen n he
      rw [← he, ht]
      simpa using hdim
    · have hl := Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne (wordSpan_mono (K := K) X (Nat.le_succ n)) he)
      have hi := ih (by omega)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt hi hl)

end WordGrowth

end KuroshConstruction

end OAI
