import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPackingGeometry
import OAI.RepresentationTheory.UniversalSquare.Band.OutputBands

namespace OAI

/-! Pair Run. -/

section

noncomputable section
namespace Saxl.Balance

def pairColumns (a m : ℕ) : List ℕ :=
  (List.range m).flatMap (fun j => [a+2*j+1,a+2*j])

def pairParts (a m : ℕ) : List ℕ :=
  (List.range m).flatMap (fun j => balancedParts (2*(a+2*j)+1) 4)

def pairMarks (a m : ℕ) : Finset ℕ :=
  (Finset.range m).image (fun j => a+2*j)

lemma pairColumns_succ (a m : ℕ) :
    pairColumns a (m+1) = pairColumns a m ++ [a+2*m+1,a+2*m] := by
  simp [pairColumns,List.range_succ]

lemma pairParts_succ (a m : ℕ) :
    pairParts a (m+1) = pairParts a m ++ balancedParts (2*(a+2*m)+1) 4 := by
  simp [pairParts,List.range_succ]

lemma pairMarks_succ (a m : ℕ) :
    pairMarks a (m+1) = pairMarks a m ∪ {a+2*m} := by
  simp only [pairMarks,Finset.range_add_one,Finset.image_insert,Finset.union_singleton]

lemma mem_pairMarks {a m k : ℕ} :
    k ∈ pairMarks a m ↔ ∃ j < m, k = a+2*j := by
  simp only [pairMarks,Finset.mem_image,Finset.mem_range]
  constructor <;> rintro ⟨j,hj,he⟩ <;> exact ⟨j,hj,he.symm⟩

lemma pairMarks_bound {a m k : ℕ} (hk : k ∈ pairMarks a m) :
    a ≤ k ∧ k+1 < a+2*m := by
  obtain ⟨j,hj,rfl⟩ := mem_pairMarks.mp hk
  omega

lemma pairMarks_separated {a m k l : ℕ} (hk : k ∈ pairMarks a m)
    (hl : l ∈ pairMarks a m) (h : k < l) : k+1 < l := by
  obtain ⟨i,hi,rfl⟩ := mem_pairMarks.mp hk
  obtain ⟨j,hj,rfl⟩ := mem_pairMarks.mp hl
  omega

lemma pairColumns_perm (a m : ℕ) : (pairColumns a m).Perm (List.range' a (2*m)) := by
  induction m with
  | zero => simp [pairColumns]
  | succ m ih =>
    rw [pairColumns_succ]
    have hpair : [a+2*m+1,a+2*m].Perm (List.range' (a+2*m) 2) := by
      simpa [List.range'] using List.Perm.swap (a+2*m) (a+2*m+1) []
    have h := ih.append hpair
    rw [List.range'_append_1] at h
    simpa only [Nat.mul_add,Nat.mul_one] using h

lemma pairParts_length (a m : ℕ) : (pairParts a m).length = 4*m := by
  induction m with
  | zero => simp [pairParts]
  | succ m ih => rw [pairParts_succ,List.length_append,ih,balancedParts_length]; omega

lemma pairParts_positive {a m : ℕ} (ha : 2 ≤ a) : ∀ p ∈ pairParts a m, 0 < p := by
  intro p hp
  obtain ⟨j,hj,hp⟩ := List.mem_flatMap.mp hp
  exact balancedParts_pos (by decide) (by omega) p hp

lemma pairParts_bound {a m p : ℕ} (_ha : 2 ≤ a) (hp : p ∈ pairParts a m) :
    p < a+2*m := by
  obtain ⟨j,hj,hp⟩ := List.mem_flatMap.mp hp
  have hj := List.mem_range.mp hj
  have hb := (balancedParts_part hp).2
  omega

theorem WordPacking.pairRun {a m d : ℕ} (ha : 2 ≤ a) (hm : 0 < m)
    (hd : a+2*m-1 ≤ d)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ k ∈ pairMarks a m, ∀ z,
      (A z ∧ label z = k) ↔ output z ∈ Set.Icc k (k+1)) :
    Nonempty (WordPacking (pairColumns a m) (pairParts a m) d A label (pairMarks a m)) := by
  induction m with
  | zero => omega
  | succ m ih =>
    let r := a+2*m
    have hr : 0 < r := by dsimp [r]; omega
    have hdr : r+1 ≤ d := by dsimp [r]; omega
    have hlast : r ∈ pairMarks a (m+1) := by
      apply mem_pairMarks.mpr
      exact ⟨m,by omega,rfl⟩
    obtain ⟨Q⟩ := WordPacking.neighbor hr hdr
      (balancedParts_sum (2*r+1) 4 (by decide)) (by simp) r A label (he r hlast)
    by_cases hm0 : m = 0
    · subst m
      simpa [pairColumns,pairParts,pairMarks,r,List.range_succ] using Nonempty.intro Q
    · obtain ⟨P⟩ := ih (by omega) (by omega) (by
        intro k hk z
        exact he k (by rw [pairMarks_succ]; exact Finset.mem_union_left _ hk) z)
      have hdis : Disjoint (pairMarks a m) {r} := by
        apply Finset.disjoint_left.mpr
        intro k hk hkr
        have hh := pairMarks_bound hk
        have hkr := Finset.mem_singleton.mp hkr
        dsimp [r] at hkr
        omega
      rw [pairColumns_succ,pairParts_succ,pairMarks_succ]
      exact ⟨P.join Q hdis⟩

end Saxl.Balance
end
end

end OAI
