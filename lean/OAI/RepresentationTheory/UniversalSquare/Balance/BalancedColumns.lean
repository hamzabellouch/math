import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.ZeroColumns
import OAI.RepresentationTheory.UniversalSquare.Balance.BalancePacking

namespace OAI

/-! Balanced Columns. -/

section

noncomputable section
namespace Saxl.Columns

def doubled {α : Type*} (xs : List α) : List α := xs.flatMap (fun x => [x,x])

@[simp] lemma doubled_nil {α : Type*} : doubled ([] : List α) = [] := rfl
@[simp] lemma doubled_cons {α : Type*} (x : α) (xs : List α) :
    doubled (x::xs) = x::x::doubled xs := rfl

lemma doubled_map {α β : Type*} (f : α → β) (xs : List α) :
    (doubled xs).map f = doubled (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [doubled_cons, List.map_cons, ih]

lemma doubled_sum (xs : List ℕ) : (doubled xs).sum = 2*xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [doubled_cons, List.sum_cons, ih]; omega

lemma doubled_countP {α : Type*} (p : α → Bool) (xs : List α) :
    (doubled xs).countP p = 2*xs.countP p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [doubled_cons, List.countP_cons, ih]; split <;> omega

lemma doubled_mem {α : Type*} (x : α) (xs : List α) : x ∈ doubled xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [doubled_cons, List.mem_cons, ih, or_self_left]

lemma doubled_perm {α : Type*} {xs ys : List α} (h : xs.Perm ys) :
    (doubled xs).Perm (doubled ys) :=
  h.flatMap (fun _ _ => List.Perm.refl _)

theorem balanced_heights (xs : List ℕ) (D : ℕ) (hD : ∀ h ∈ xs, h ≤ 2*D) :
    ∃ ps : List (ℕ × ℕ),
      ps.map (fun p => p.1+p.2) = xs ∧
      (∀ p ∈ ps, p.1 ≤ D ∧ p.2 ≤ D) ∧
      (ps.map Prod.fst).sum = xs.sum/2 ∧
      (ps.map Prod.snd).sum = (xs.sum+1)/2 := by
  induction xs with
  | nil => exact ⟨[],rfl,by simp,by simp,by simp⟩
  | cons j xs ih =>
    obtain ⟨ps,ht,hp,ha,hb⟩ := ih (fun h hh => hD h (by simp [hh]))
    let a := if xs.sum % 2 = 0 then j/2 else (j+1)/2
    let b := j-a
    have hj := hD j (by simp)
    have hab : a + b = j := by unfold b a; split_ifs <;> omega
    have haD : a ≤ D := by unfold a; split_ifs <;> omega
    have hbD : b ≤ D := by unfold b a; split_ifs <;> omega
    refine ⟨(a,b)::ps,?_,?_,?_,?_⟩
    · simp only [List.map_cons, hab, ht]
    · intro p hp'
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact ⟨haD,hbD⟩
      · exact hp p hp'
    · simp only [List.map_cons, List.sum_cons, ha]
      unfold a; split_ifs <;> omega
    · simp only [List.map_cons, List.sum_cons, hb]
      unfold b a; split_ifs <;> omega

lemma odd_sum_has_odd (xs : List ℕ) (h : xs.sum % 2 = 1) :
    ∃ j ∈ xs, j % 2 = 1 := by
  induction xs with
  | nil => simp at h
  | cons j xs ih =>
    by_cases hj : j % 2 = 1
    · exact ⟨j,by simp,hj⟩
    · have ht : xs.sum % 2 = 1 := by simp only [List.sum_cons] at h; omega
      obtain ⟨k,hk,hko⟩ := ih ht
      exact ⟨k,List.mem_cons_of_mem _ hk,hko⟩

theorem balanced_even_splits (xs : List ℕ) (D : ℕ)
    (hD : ∀ h ∈ xs, h ≤ 2*D) (he : xs.sum % 2 = 0) :
    ∃ ps : List (ℕ × ℕ),
      ps.map (fun p => p.1+p.2) = doubled xs ∧
      (∀ p ∈ ps, p.1 ≤ D ∧ p.2 ≤ D) ∧
      (ps.map Prod.fst).sum = xs.sum ∧
      (ps.map Prod.snd).sum = xs.sum ∧
      (∀ i, Even ((ps.map Prod.fst).countP (fun h => decide (i<h)))) ∧
      (∀ i, Even ((ps.map Prod.snd).countP (fun h => decide (i<h)))) := by
  obtain ⟨ps,ht,hp,ha,hb⟩ := balanced_heights xs D hD
  refine ⟨doubled ps,?_,?_,?_,?_,?_,?_⟩
  · rw [doubled_map,ht]
  · intro p hh; exact hp p ((doubled_mem p ps).mp hh)
  · rw [doubled_map,doubled_sum,ha]; omega
  · rw [doubled_map,doubled_sum,hb]; omega
  · intro i; rw [doubled_map,doubled_countP]; exact even_two_mul _
  · intro i; rw [doubled_map,doubled_countP]; exact even_two_mul _

theorem balanced_double_splits (xs : List ℕ) (D : ℕ)
    (hD : ∀ h ∈ xs, h ≤ 2*D) :
    ∃ ps : List (ℕ × ℕ),
      (ps.map (fun p => p.1+p.2)).Perm (doubled xs) ∧
      (∀ p ∈ ps, p.1 ≤ D ∧ p.2 ≤ D) ∧
      (ps.map Prod.fst).sum = xs.sum ∧
      (ps.map Prod.snd).sum = xs.sum ∧
      ShortColumns.RowParity (xs.sum%2) (columnShape (ps.map Prod.fst)) ∧
      ShortColumns.RowParity (xs.sum%2) (columnShape (ps.map Prod.snd)) := by
  by_cases he : xs.sum % 2 = 0
  · obtain ⟨ps,ht,hp,ha,hb,hra,hrb⟩ := balanced_even_splits xs D hD he
    refine ⟨ps,ht ▸ List.Perm.refl _,hp,ha,hb,?_,?_⟩
    · simpa only [he, ShortColumns.RowParity, ↓reduceIte, columnShape_rowLen] using hra
    · simpa only [he, ShortColumns.RowParity, ↓reduceIte, columnShape_rowLen] using hrb
  · have ho : xs.sum % 2 = 1 := by omega
    obtain ⟨j,hj,hjo⟩ := odd_sum_has_odd xs ho
    let ys := xs.erase j
    have hperm : xs.Perm (j::ys) := List.perm_cons_erase hj
    have hsum : xs.sum = j + ys.sum := by simpa only [List.sum_cons] using hperm.sum_eq
    have hys : ys.sum % 2 = 0 := by omega
    have hDy : ∀ h ∈ ys, h ≤ 2*D := by
      intro h hh; exact hD h ((hperm.mem_iff).mpr (List.mem_cons_of_mem _ hh))
    obtain ⟨ps,ht,hp,ha,hb,hra,hrb⟩ := balanced_even_splits ys D hDy hys
    let k := j/2
    have hjk : j = 2*k+1 := by dsimp [k]; omega
    have hkD : k+1 ≤ D := by have := hD j hj; omega
    let qs := (k+1,k)::(k,k+1)::ps
    have hta : (qs.map Prod.fst) = (k+1)::k::(ps.map Prod.fst) := rfl
    have htb : (qs.map Prod.snd) = k::(k+1)::(ps.map Prod.snd) := rfl
    have rowVals (zs : List ℕ) (i : ℕ) :
        ((k+1)::k::zs).countP (fun h => decide (i<h)) =
          zs.countP (fun h => decide (i<h)) +
            (if i<k then 2 else if i=k then 1 else 0) := by
      simp only [List.countP_cons, decide_eq_true_eq]
      split_ifs <;> omega
    have hpA : ShortColumns.RowParity 1 (columnShape (qs.map Prod.fst)) := by
      simp only [ShortColumns.RowParity, Nat.one_ne_zero, ite_false]
      refine ⟨k,?_,?_⟩
      · rw [columnShape_rowLen,hta,rowVals]
        simp only [lt_self_iff_false, ite_false]
        exact (hra k).add_odd odd_one
      · intro i hi
        rw [columnShape_rowLen,hta,rowVals]
        simp only [hi, ite_false]
        split_ifs
        · exact (hra i).add (by decide : Even 2)
        · simpa using hra i
    have countSwap (i : ℕ) :
        (qs.map Prod.snd).countP (fun h => decide (i<h)) =
          ((k+1)::k::(ps.map Prod.snd)).countP (fun h => decide (i<h)) := by
      rw [htb]
      exact List.Perm.countP_eq _ (List.Perm.swap _ _ _)
    have hpB : ShortColumns.RowParity 1 (columnShape (qs.map Prod.snd)) := by
      simp only [ShortColumns.RowParity, Nat.one_ne_zero, ite_false]
      refine ⟨k,?_,?_⟩
      · rw [columnShape_rowLen,countSwap,rowVals]
        simp only [lt_self_iff_false, ite_false]
        exact (hrb k).add_odd odd_one
      · intro i hi
        rw [columnShape_rowLen,countSwap,rowVals]
        simp only [hi, ite_false]
        split_ifs
        · exact (hrb i).add (by decide : Even 2)
        · simpa using hrb i
    refine ⟨qs,?_,?_,?_,?_,by rwa [ho],by rwa [ho]⟩
    · have ht' : qs.map (fun p => p.1+p.2) = doubled (j::ys) := by
        simp only [qs,List.map_cons,ht,doubled_cons]
        rw [show k+1+k = j by omega, show k+(k+1) = j by omega]
      exact ht' ▸ (doubled_perm hperm).symm
    · intro p hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact ⟨hkD,by omega⟩
      · rcases List.mem_cons.mp hh with rfl | hh
        · exact ⟨by omega,hkD⟩
        · exact hp p hh
    · rw [hta,List.sum_cons,List.sum_cons,ha]; omega
    · rw [htb,List.sum_cons,List.sum_cons,hb]; omega

lemma columnShape_perm {xs ys : List ℕ} (hp : xs.Perm ys) :
    columnShape xs = columnShape ys := by
  apply YoungDiagram.ext
  apply Finset.ext
  rintro ⟨i,j⟩
  change (i,j) ∈ columnShape xs ↔ (i,j) ∈ columnShape ys
  rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen,
    columnShape_rowLen, columnShape_rowLen, hp.countP_eq]

lemma count_columns (μ : YoungDiagram) (i : ℕ) :
    μ.transpose.rowLens.countP (fun h => decide (i<h)) = μ.rowLen i :=
  (placed_rowLen (toYoung μ) (fun _ => rfl) i).symm

lemma columnShape_doubled_halfRows (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i)) :
    columnShape (doubled (halfRows μ).transpose.rowLens) = μ := by
  apply YoungDiagram.ext
  apply Finset.ext
  rintro ⟨i,j⟩
  change (i,j) ∈ columnShape _ ↔ (i,j) ∈ μ
  rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen,
    columnShape_rowLen,doubled_countP,count_columns,halfRows_rowLen]
  have hh := (Nat.even_iff.mp (he i))
  omega

lemma columns_bounded (μ : YoungDiagram) (D : ℕ) (hD : μ.colLen 0 ≤ D) :
    ∀ h ∈ μ.transpose.rowLens, h ≤ D := by
  intro h hh
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hh
  exact le_trans (by simpa only [YoungDiagram.rowLen_transpose] using μ.colLen_anti 0 i (Nat.zero_le _)) hD

theorem even_rows_allocation (r D : ℕ) (μ : YoungDiagram) (hm : μ.card = 2*r)
    (he : ∀ i, Even (μ.rowLen i)) (hD : μ.colLen 0 ≤ 2*D) :
    ∃ ps : List (ℕ × ℕ),
      columnShape (ps.map (fun p => p.1+p.2)) = μ ∧
      (∀ p ∈ ps, p.1 ≤ D ∧ p.2 ≤ D) ∧
      (ps.map Prod.fst).sum = r ∧ (ps.map Prod.snd).sum = r ∧
      ShortColumns.RowParity (r%2) (columnShape (ps.map Prod.fst)) ∧
      ShortColumns.RowParity (r%2) (columnShape (ps.map Prod.snd)) := by
  let xs := (halfRows μ).transpose.rowLens
  have hx : xs.sum = r := by
    have hc := placed_card (toYoung (halfRows μ))
    have hc' := halfRows_card μ he
    change (halfRows μ).card = xs.sum at hc
    omega
  obtain ⟨ps,ht,hp,ha,hb,hpa,hpb⟩ := balanced_double_splits xs D
    (columns_bounded (halfRows μ) (2*D) (by rwa [halfRows_height μ he]))
  refine ⟨ps,?_,hp,ha.trans hx,hb.trans hx,?_,?_⟩
  · exact (columnShape_perm ht).trans (columnShape_doubled_halfRows μ he)
  · rwa [hx] at hpa
  · rwa [hx] at hpb

end Saxl.Columns
end
end

end OAI
