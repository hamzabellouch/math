import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.FastRowCheck

namespace OAI

/-! Union Row Checker. -/

section

namespace UniversalTensorSquare

def liveRegions (fuel n upper : ℕ) (regions : List PrefixRegion) : List PrefixRegion :=
  regions.filter fun R => !quickRejected fuel n upper R.1 R.2

def nextRegions (a : ℕ) (regions : List PrefixRegion) : List PrefixRegion :=
  regions.filterMap fun R => if quickAllowed a R.1 R.2 then
    some (clipBudget R.1 a,rowBudget R.2 a) else none

def checkRegionPrefixes (P : List ℕ → Bool) : ℕ → ℕ → ℕ →
    List PrefixRegion → List ℕ → Bool
  | fuel,n,upper,regions,pref =>
    let alive := liveRegions fuel n upper regions
    if alive.isEmpty then true else
      match fuel with
      | 0 => if n = 0 then P pref.reverse else true
      | k+1 =>
          let lo := max 1 (n/(k+1))
          (List.range' lo (min n upper+1-lo)).all fun a =>
            if n ≤ (k+1)*a then
              checkRegionPrefixes P k (n-a) a (nextRegions a alive) (a::pref)
            else true

lemma checkRegionPrefixes_sound (P : List ℕ → Bool) (fuel n upper : ℕ)
    (regions : List PrefixRegion) (pref : List ℕ)
    (hc : checkRegionPrefixes P fuel n upper regions pref = true) :
    ∀ A B, (A,B) ∈ regions → ∀ rs ∈ constrainedRows fuel n upper A B,
      P (pref.reverse ++ rs) = true := by
  induction fuel generalizing n upper regions pref with
  | zero =>
    intro A B hR rs hrs
    rw [constrainedRows] at hrs
    split_ifs at hrs with hrej hn
    · simp at hrs
    · simp only [List.mem_singleton] at hrs
      subst rs
      have hmem : (A,B) ∈ liveRegions 0 n upper regions := by
        apply List.mem_filter.mpr
        exact ⟨hR,by simpa only [Bool.not_eq_true',quickRejected_iff,
          Bool.eq_false_iff,ne_eq] using hrej⟩
      have hne : ¬(liveRegions 0 n upper regions).isEmpty := by
        simp only [List.isEmpty_iff]
        intro he
        simp only [he,List.not_mem_nil] at hmem
      simpa only [checkRegionPrefixes,ite_eq_right hne,ite_eq_left hn,List.append_nil] using hc
    · simp at hrs
  | succ k ih =>
    intro A B hR rs hrs
    rw [constrainedRows] at hrs
    split_ifs at hrs with hrej
    · simp at hrs
    · have hmem : (A,B) ∈ liveRegions (k+1) n upper regions := by
        apply List.mem_filter.mpr
        exact ⟨hR,by simpa only [Bool.not_eq_true',quickRejected_iff,
          Bool.eq_false_iff,ne_eq] using hrej⟩
      have hne : ¬(liveRegions (k+1) n upper regions).isEmpty := by
        simp only [List.isEmpty_iff]
        intro he
        simp only [he,List.not_mem_nil] at hmem
      obtain ⟨a,ha,hr⟩ := List.mem_flatMap.mp hrs
      split_ifs at hr with hallowed
      · obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hr
        have hlo : max 1 (n/(k+1)) ≤ a := by
          have hh := Nat.div_le_of_le_mul hallowed.2
          have ha' := (List.mem_range'_1.mp ha).1
          exact max_le ha' hh
        have hai : a ∈ List.range' (max 1 (n/(k+1)))
            (min n upper+1-max 1 (n/(k+1))) := by
          have ha' := List.mem_range'_1.mp ha
          apply List.mem_range'_1.mpr
          refine ⟨hlo, ?_⟩
          have he : max 1 (n/(k+1)) + (min n upper+1-max 1 (n/(k+1))) = min n upper+1 := by
            apply Nat.add_sub_of_le
            omega
          rw [he]
          omega
        rw [checkRegionPrefixes] at hc
        simp only [ite_eq_right hne] at hc
        have hh := List.all_eq_true.mp hc a hai
        rw [ite_eq_left hallowed.2] at hh
        have hnext : (clipBudget A a,rowBudget B a) ∈
            nextRegions a (liveRegions (k+1) n upper regions) := by
          apply List.mem_filterMap.mpr
          refine ⟨(A,B),hmem,?_⟩
          simp only [quickAllowed_iff,ite_eq_left hallowed.1]
        have hi := ih (n-a) a (nextRegions a (liveRegions (k+1) n upper regions))
          (a::pref) hh _ _ hnext ys hy
        simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hi
      · simp at hr

lemma checkedRegion_diagram {n M r H W : ℕ} {qs : List (List ℕ)} {t : RowTree}
    {regions : List PrefixRegion}
    (check : ∀ h ≤ H, checkRegionPrefixes (quickResidual M r qs t) h n W regions [] = true)
    (μ : YoungDiagram) (hn : μ.card = n) {A B : List (ℕ × ℕ)}
    (hR : (A,B) ∈ regions) (hA : RowBounds μ.transpose A) (hB : RowBounds μ B)
    (hH : firstBound n A ≤ H) (hW : firstBound n B ≤ W) :
    TreeResidual M r qs t μ.rowLens := by
  have hu : ∀ a ∈ μ.rowLens, a ≤ W := by
    intro a ha
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem ha
    rw [← he, YoungDiagram.get_rowLens]
    exact (μ.rowLen_anti _ _ (Nat.zero_le _)).trans ((firstBound_sound μ hn hB).trans hW)
  have hl : μ.rowLens.length ≤ H := by
    rw [YoungDiagram.length_rowLens]
    have hh := (firstBound_sound μ.transpose ((Saxl.transpose_card μ).trans hn) hA).trans hH
    simpa only [YoungDiagram.rowLen_transpose] using hh
  have hmem : μ.rowLens ∈ constrainedRows μ.rowLens.length n W A B := by
    apply mem_constrainedRows _ _ _ _ _ _ rfl
    · exact (Saxl.card_eq_sum_rowLens μ).symm.trans hn
    · exact μ.pos_of_mem_rowLens
    · exact hu
    · exact μ.rowLens_sorted
    · intro p hp
      rw [clippedSum_rowLens]
      exact (hA p hp).2
    · intro p hp
      rw [← rowPrefix_eq_take]
      exact (hB p hp).2
  apply quickResidual_sound
  have hh := checkRegionPrefixes_sound (quickResidual M r qs t) μ.rowLens.length n W
    regions [] (check _ hl) A B hR μ.rowLens hmem
  simpa only [List.reverse_nil,List.nil_append] using hh

end UniversalTensorSquare
end

end OAI
