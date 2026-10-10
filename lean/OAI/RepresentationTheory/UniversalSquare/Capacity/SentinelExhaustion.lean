import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.CandidateColumns
import OAI.RepresentationTheory.UniversalSquare.Support.ConstrainedDiagrams
import OAI.RepresentationTheory.UniversalSquare.Balance.PackingPlans

namespace OAI

/-! Sentinel Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma testWidth_valid_pos {M f : ℕ} (hf : 1 ≤ f) (hw : 0 < testWidth M f) :
    testWidth M f ≤ 8 ∧ f * testWidth M f + 7 + f ≤ 2*M-1 := by
  refine ⟨min_le_left _ _, ?_⟩
  have hh := Nat.mul_le_mul_left f (min_le_right 8 ((2*M-8-f)/f))
  have hh' := Nat.div_mul_le_self (2*M-8-f) f
  have hq : 0 < (2*M-8-f)/f := lt_of_lt_of_le hw (min_le_right _ _)
  have hn : f ≤ 2*M-8-f := by simpa using (Nat.le_div_iff_mul_le (by omega)).mp hq
  unfold testWidth
  nlinarith [Nat.sub_add_cancel (show f ≤ 2*M-8 by omega),
    Nat.sub_add_cancel (show 8 ≤ 2*M by omega),
    Nat.sub_add_cancel (show 1 ≤ 2*M by omega)]

lemma sentinel_height (μ : YoungDiagram) {K : ℕ} (hK : 0 < K) :
    ∃ d, 1 ≤ d ∧ d ≤ 5 ∧ (d ≤ 4 → K ≤ rowPrefix μ d) ∧
      (1 < d → rowPrefix μ (d-1) < K) := by
  by_cases hh : K ≤ rowPrefix μ 4
  · obtain ⟨d,hd,h4,hp,hl⟩ := first_prefix_height μ hK hh
    exact ⟨d,hd,by omega,fun _ => hp,hl⟩
  · exact ⟨5,by decide,le_rfl,by omega,by simpa using Nat.lt_of_not_ge hh⟩

lemma prefixBounds_sound_sentinel (μ : YoungDiagram) {M r d e : ℕ}
    (hM : 1 ≤ M) (hr : 0 < r)
    (hd : 1 < d → colPrefix μ (d-1) < 2*M-1)
    (he : e ≤ 4 → 2*M-1 ≤ rowPrefix μ e) (hfail : ¬BandTest M r μ) :
    ∀ p ∈ prefixBounds M r d e, 0 < p.1 ∧ colPrefix μ p.1 ≤ p.2 := by
  intro p hp
  simp only [prefixBounds,List.mem_append] at hp
  rcases hp with hp | hp
  · split_ifs at hp with hd'
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      subst p
      exact ⟨by omega,by have := hd hd'; dsimp; omega⟩
    · simp at hp
  · obtain ⟨k,hk,hkp⟩ := List.mem_filterMap.mp hp
    simp only [List.mem_range] at hk
    split_ifs at hkp with hke
    · have hp' := Option.some.inj hkp
      subst p
      have hw := testWidth_valid_pos (by omega : 1 ≤ k+1) hke.2
      have hc : bandCapacity μ (k+1) (testWidth M (k+1)) < r := by
        by_contra hh
        apply hfail
        exact ⟨k+1,by omega,by omega,testWidth M (k+1),hw.1,
          (he (by omega)).trans (rowPrefix_mono μ hke.1),hw.2,by omega⟩
      have hb := prefix_le_capacity μ (k+1) (testWidth M (k+1))
      exact ⟨hke.2,by dsimp; omega⟩

def residualCheck (n M r d e a b : ℕ) (q : List ℕ) (P : List ℕ → Prop) : Prop :=
  let A := prefixBounds M r d e ++ [(a,(q.take a).sum-1)]
  let B := prefixBounds M r e d ++ [(b,(q.take b).sum-1)]
  (d ≤ 4 ∧ coreImpossible (2*M-1) d A) ∨
    (e ≤ 4 ∧ coreImpossible (2*M-1) e B) ∨ impossibleBounds n A B ∨
    ∀ rs ∈ rowsWithin n A B, P rs

instance (n M r d e a b : ℕ) (q : List ℕ) (P : List ℕ → Prop) [DecidablePred P] :
    Decidable (residualCheck n M r d e a b q P) := by
  unfold residualCheck; infer_instance

theorem sentinel_capacity_dichotomy (μ θ : YoungDiagram) {n M r : ℕ}
    (hn : 0 < n) (hM : 1 ≤ M) (hr : 0 < r) (hc : μ.card = n) (ht : θ.card = n)
    (P : List ℕ → Prop)
    (check : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
      ∀ a ∈ List.range θ.rowLens.length, ∀ b ∈ List.range θ.rowLens.length,
        residualCheck n M r (d+1) (e+1) (a+1) (b+1) θ.rowLens P) :
    BandTest M r μ ∨ BandTest M r μ.transpose ∨ Dominates μ θ ∨
      Dominates μ.transpose θ ∨ P μ.rowLens := by
  classical
  by_contra hh
  push Not at hh
  rcases hh with ⟨hband,hband',hdom,hdom',hP⟩
  obtain ⟨d,hd,hd',hHd,hHd'⟩ := sentinel_height μ.transpose (show 0 < 2*M-1 by omega)
  obtain ⟨e,he,he',hWe,hWe'⟩ := sentinel_height μ (show 0 < 2*M-1 by omega)
  obtain ⟨a,ha,ha',hA⟩ := not_dominates_witness ((transpose_card _).trans hc |>.trans ht.symm) hdom'
  obtain ⟨b,hb,hb',hB⟩ := not_dominates_witness (hc.trans ht.symm) hdom
  have hAf := prefixBounds_sound_sentinel μ hM hr hHd' hWe hband
  have hBf := prefixBounds_sound_sentinel μ.transpose hM hr
    (by simpa only [colPrefix,YoungDiagram.transpose_transpose] using hWe') hHd hband'
  let A := prefixBounds M r d e ++ [(a,(θ.rowLens.take a).sum-1)]
  let B := prefixBounds M r e d ++ [(b,(θ.rowLens.take b).sum-1)]
  have hAbb : RowBounds μ.transpose A := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hAf p hp
    · have heq : p = (a,(θ.rowLens.take a).sum-1) := by simpa using hp
      subst p
      rw [rowPrefix_eq_take θ] at hA
      exact ⟨ha,by dsimp; omega⟩
  have hBbb : RowBounds μ B := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · simpa only [colPrefix,YoungDiagram.transpose_transpose] using hBf p hp
    · have heq : p = (b,(θ.rowLens.take b).sum-1) := by simpa using hp
      subst p
      rw [rowPrefix_eq_take θ] at hB
      exact ⟨hb,by dsimp; omega⟩
  have h := check (d-1) (by simp; omega) (e-1) (by simp; omega)
    (a-1) (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
    (b-1) (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
  have hde : d-1+1 = d := by omega
  have hee : e-1+1 = e := by omega
  have hae : a-1+1 = a := by omega
  have hbe : b-1+1 = b := by omega
  rw [hde,hee,hae,hbe] at h
  rcases h with ⟨h4,h⟩ | ⟨h4,h⟩ | h | h
  · exact coreImpossible_false μ.transpose (hHd h4) hAbb h
  · exact coreImpossible_false μ (hWe h4) hBbb h
  · exact impossibleBounds_false hn μ hc hAbb hBbb h
  · exact hP (rowsWithin_sound hn μ hc hAbb hBbb h)

theorem candidate_residual_pos {n M b δ r : ℕ} (hM : 4 ≤ M)
    (hδ : δ ≤ 1) (hr : r = 2*b+δ) (hrpos : 0 < r)
    (hn : (candidate M b δ).card = n)
    (q : List ℕ) (hq : GoodRows q) (hqn : q.sum = n)
    (p : PackingPlan) (hv : p.Valid (M+b+δ)) (hbands : BandsValid p.bands)
    (hcols : p.columns.Perm ([M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1))
    (hparts : p.parts.Perm q) (P : List ℕ → Prop)
    (hP : ∀ rs, GoodRows rs → rs.sum = n → P rs → SquareOccurs (candidate M b δ) (rowDiagram rs))
    (check : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
      ∀ a ∈ List.range q.length, ∀ c ∈ List.range q.length,
        residualCheck n M r (d+1) (e+1) (a+1) (c+1) q P)
    (μ : YoungDiagram) (hμ : μ.card = n) :
    0 < kronecker (canonicalTableau (candidate M b δ) hn)
      (canonicalTableau (candidate M b δ) hn) (canonicalTableau μ hμ) := by
  have hposn : 0 < n := by rw [← hn,candidate_card _ _ _ (by omega)]; omega
  have hp : ∀ a ∈ p.parts, 0 < a := fun a ha => hq.2 a (hparts.mem_iff.mp ha)
  have hshape : (columnShape p.parts).transpose = rowDiagram q := by
    rw [columnShape_perm hparts]; rfl
  have hh : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ hM]; simp [candidateLengths]
  have hc : p.columns.Perm (candidate M b δ).transpose.rowLens := by
    rw [candidate_transpose,candidate_rowLens hM]; exact hcols
  have cone (ν : YoungDiagram) (hν : ν.card = n) (hd : Dominates ν (rowDiagram q)) :
      0 < kronecker (canonicalTableau (candidate M b δ) hn)
        (canonicalTableau (candidate M b δ) hn) (canonicalTableau ν hν) := by
    apply packingPlan_pos p hv hbands hh hc hp
    simpa only [hshape] using hd
  have htcheck : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
      ∀ a ∈ List.range (rowDiagram q).rowLens.length, ∀ c ∈ List.range (rowDiagram q).rowLens.length,
        residualCheck n M r (d+1) (e+1) (a+1) (c+1) (rowDiagram q).rowLens P := by
    simpa only [rowDiagram_rows hq] using check
  rcases sentinel_capacity_dichotomy μ (rowDiagram q) hposn (by omega) hrpos hμ
    ((rowDiagram_card q).trans hqn) P htcheck with h | h | h | h | h
  · exact band_kronecker_pos hM hδ hr _ μ _ h
  · apply (kronecker_pos_transpose_iff _ hn (candidate_transpose M b δ) μ hμ).mpr
    exact band_kronecker_pos hM hδ hr _ μ.transpose _ h
  · exact cone μ hμ h
  · apply (kronecker_pos_transpose_iff _ hn (candidate_transpose M b δ) μ hμ).mpr
    exact cone μ.transpose ((transpose_card μ).trans hμ) h
  · have ht := hP μ.rowLens ⟨μ.rowLens_sorted,μ.pos_of_mem_rowLens⟩
      ((card_eq_sum_rowLens μ).symm.trans hμ) h
    rw [rowDiagram_rowLens] at ht
    exact ht.pos _ _

end UniversalTensorSquare
end
end

end OAI
