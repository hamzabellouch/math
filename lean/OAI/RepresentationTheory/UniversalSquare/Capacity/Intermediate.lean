import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.BandCriterion

namespace OAI

/-! Intermediate. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

def testWidth (M f : ℕ) : ℕ := min 8 ((2*M-8-f)/f)

lemma testWidth_valid {M f : ℕ} (hM : 9 ≤ M) (hf : 1 ≤ f) (hf' : f ≤ 4) :
    testWidth M f ≤ 8 ∧ f * testWidth M f + 7 + f ≤ 2*M-1 := by
  refine ⟨min_le_left _ _, ?_⟩
  have h := Nat.mul_le_mul_left f (min_le_right 8 ((2*M-8-f)/f))
  have h' := Nat.div_mul_le_self (2*M-8-f) f
  unfold testWidth
  nlinarith [Nat.sub_add_cancel (show f ≤ 2*M-8 by omega),
    Nat.sub_add_cancel (show 8 ≤ 2*M by omega),
    Nat.sub_add_cancel (show 1 ≤ 2*M by omega)]

def prefixBounds (M r d e : ℕ) : List (ℕ × ℕ) :=
  (if 1 < d then [(d-1,2*M-2)] else []) ++
    ((List.range 4).filterMap fun k =>
      let f := k+1
      let q := testWidth M f
      if e ≤ f ∧ 0 < q then some (q,2*r-2+q*(f+1)) else none)

lemma prefixBounds_sound (μ : YoungDiagram) {M r d e : ℕ}
    (hM : 9 ≤ M) (hr : 0 < r)
    (hd : 1 < d → colPrefix μ (d-1) < 2*M-1)
    (he : 2*M-1 ≤ rowPrefix μ e) (hfail : ¬BandTest M r μ) :
    ∀ p ∈ prefixBounds M r d e, 0 < p.1 ∧ colPrefix μ p.1 ≤ p.2 := by
  intro p hp
  simp only [prefixBounds, List.mem_append] at hp
  rcases hp with hp | hp
  · split_ifs at hp with hd'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst p
      exact ⟨by omega, by have := hd hd'; dsimp; omega⟩
    · simp at hp
  · obtain ⟨k,hk,hkp⟩ := List.mem_filterMap.mp hp
    simp only [List.mem_range] at hk
    split_ifs at hkp with hke
    · have hp' := Option.some.inj hkp
      subst p
      have hw := testWidth_valid hM (by omega : 1 ≤ k+1) (by omega : k+1 ≤ 4)
      have hc : bandCapacity μ (k+1) (testWidth M (k+1)) < r := by
        by_contra hh
        apply hfail
        exact ⟨k+1, by omega, by omega, testWidth M (k+1), hw.1,
          he.trans (rowPrefix_mono μ hke.1), hw.2, by omega⟩
      have hb := prefix_le_capacity μ (k+1) (testWidth M (k+1))
      exact ⟨hke.2, by dsimp; omega⟩

def exceptionalPair (M r : ℕ) : Prop :=
  (M = 10 ∧ 8 ≤ r ∧ r ≤ 17) ∨ (M = 12 ∧ 14 ≤ r ∧ r ≤ 20) ∨
    (M = 14 ∧ 22 ≤ r ∧ r ≤ 23)

instance (M r : ℕ) : Decidable (exceptionalPair M r) := inferInstanceAs
  (Decidable ((M = 10 ∧ 8 ≤ r ∧ r ≤ 17) ∨ (M = 12 ∧ 14 ≤ r ∧ r ≤ 20) ∨
    (M = 14 ∧ 22 ≤ r ∧ r ≤ 23)))

def admissibleR (M r : ℕ) : Prop := 0 < r ∧
  (if M % 2 = 1 then 2*r ≤ M-1 else 2*r ≤ 3*M+4) ∧ ¬exceptionalPair M r

instance (M r : ℕ) : Decidable (admissibleR M r) := inferInstanceAs
  (Decidable (0 < r ∧ (if M % 2 = 1 then 2*r ≤ M-1 else 2*r ≤ 3*M+4) ∧
    ¬exceptionalPair M r))

def intermediateCheck (M r d e : ℕ) : Prop :=
  ∃ p ∈ prefixBounds M r d e, ∃ q ∈ prefixBounds M r e d,
    max (p.2+q.2-1) (p.2*q.2/(p.1*q.1)) < M*(M+1)/2+2*r

instance (M r d e : ℕ) : Decidable (intermediateCheck M r d e) :=
  inferInstanceAs (Decidable (∃ p ∈ prefixBounds M r d e,
    ∃ q ∈ prefixBounds M r e d,
    max (p.2+q.2-1) (p.2*q.2/(p.1*q.1)) < M*(M+1)/2+2*r))

lemma intermediate9 : ∀ r ∈ List.range 34, admissibleR 9 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 9 r (d+1) (e+1) := by decide

lemma intermediate10 : ∀ r ∈ List.range 34, admissibleR 10 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 10 r (d+1) (e+1) := by decide

lemma intermediate11 : ∀ r ∈ List.range 34, admissibleR 11 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 11 r (d+1) (e+1) := by decide

lemma intermediate12 : ∀ r ∈ List.range 34, admissibleR 12 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 12 r (d+1) (e+1) := by decide

lemma intermediate13 : ∀ r ∈ List.range 34, admissibleR 13 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 13 r (d+1) (e+1) := by decide

lemma intermediate14 : ∀ r ∈ List.range 34, admissibleR 14 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 14 r (d+1) (e+1) := by decide

lemma intermediate15 : ∀ r ∈ List.range 34, admissibleR 15 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 15 r (d+1) (e+1) := by decide

lemma intermediate16 : ∀ r ∈ List.range 34, admissibleR 16 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 16 r (d+1) (e+1) := by decide

lemma intermediate17 : ∀ r ∈ List.range 34, admissibleR 17 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 17 r (d+1) (e+1) := by decide

lemma intermediate18 : ∀ r ∈ List.range 34, admissibleR 18 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 18 r (d+1) (e+1) := by decide

lemma intermediate19 : ∀ r ∈ List.range 34, admissibleR 19 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 19 r (d+1) (e+1) := by decide

lemma intermediate20 : ∀ r ∈ List.range 34, admissibleR 20 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 20 r (d+1) (e+1) := by decide

lemma intermediate21 : ∀ r ∈ List.range 34, admissibleR 21 r →
    ∀ d ∈ List.range 4, ∀ e ∈ List.range 4, intermediateCheck 21 r (d+1) (e+1) := by decide

lemma capacity_intermediate_numeric {M r d e : ℕ}
    (hM : 9 ≤ M) (hM' : M ≤ 21) (hr : admissibleR M r)
    (hd : 1 ≤ d) (hd' : d ≤ 4) (he : 1 ≤ e) (he' : e ≤ 4) :
    intermediateCheck M r d e := by
  have hr' : r ∈ List.range 34 := by
    have hb := hr.2.1
    split_ifs at hb <;> simp only [List.mem_range] <;> omega
  have hdd : d-1 ∈ List.range 4 := by simp only [List.mem_range]; omega
  have hee : e-1 ∈ List.range 4 := by simp only [List.mem_range]; omega
  have hde : d = (d-1)+1 := by omega
  have hee' : e = (e-1)+1 := by omega
  rw [hde, hee']
  interval_cases M
  · exact intermediate9 r hr' hr _ hdd _ hee
  · exact intermediate10 r hr' hr _ hdd _ hee
  · exact intermediate11 r hr' hr _ hdd _ hee
  · exact intermediate12 r hr' hr _ hdd _ hee
  · exact intermediate13 r hr' hr _ hdd _ hee
  · exact intermediate14 r hr' hr _ hdd _ hee
  · exact intermediate15 r hr' hr _ hdd _ hee
  · exact intermediate16 r hr' hr _ hdd _ hee
  · exact intermediate17 r hr' hr _ hdd _ hee
  · exact intermediate18 r hr' hr _ hdd _ hee
  · exact intermediate19 r hr' hr _ hdd _ hee
  · exact intermediate20 r hr' hr _ hdd _ hee
  · exact intermediate21 r hr' hr _ hdd _ hee

lemma first_prefix_height (μ : YoungDiagram) {K : ℕ} (hK : 0 < K)
    (h : K ≤ rowPrefix μ 4) :
    ∃ d, 1 ≤ d ∧ d ≤ 4 ∧ K ≤ rowPrefix μ d ∧
      (1 < d → rowPrefix μ (d-1) < K) := by
  let h' : ∃ d, K ≤ rowPrefix μ d := ⟨4,h⟩
  refine ⟨Nat.find h', ?_, Nat.find_min' h' h, Nat.find_spec h', ?_⟩
  · have hx := Nat.find_spec h'
    by_contra hh
    have hd : Nat.find h' = 0 := by omega
    change K ≤ rowPrefix μ (Nat.find h') at hx
    rw [hd] at hx
    simp only [rowPrefix, Finset.range_zero, Finset.sum_empty] at hx
    omega
  · intro hd
    exact Nat.lt_of_not_ge (Nat.find_min h' (by omega))

theorem capacity_intermediate (μ : YoungDiagram) {M r : ℕ}
    (hM : 9 ≤ M) (hM' : M ≤ 21) (hr : admissibleR M r)
    (hn : μ.card = (staircase M).card + 2*r)
    (hH : 2*M-1 ≤ colPrefix μ 4) (hW : 2*M-1 ≤ rowPrefix μ 4) :
    BandTest M r μ ∨ BandTest M r μ.transpose := by
  classical
  by_contra hh
  push Not at hh
  obtain ⟨d,hd,hd',hHd,hHd'⟩ := first_prefix_height μ.transpose (by omega) hH
  obtain ⟨e,he,he',hWe,hWe'⟩ := first_prefix_height μ (by omega) hW
  obtain ⟨p,hp,q,hq,hpq⟩ := capacity_intermediate_numeric hM hM' hr hd hd' he he'
  have hp' := prefixBounds_sound μ hM hr.1 hHd' hWe hh.1 p hp
  have hq' := prefixBounds_sound μ.transpose hM hr.1
    (by simpa only [colPrefix, YoungDiagram.transpose_transpose] using hWe')
    hHd hh.2 q hq
  have hb := capacity_rectangle μ hp'.1 hq'.1 hp'.2
    (by simpa only [colPrefix, YoungDiagram.transpose_transpose] using hq'.2)
  have hn' : μ.card = M*(M+1)/2+2*r := by rw [hn, staircase_card]
  omega

end UniversalTensorSquare
end
end

end OAI
