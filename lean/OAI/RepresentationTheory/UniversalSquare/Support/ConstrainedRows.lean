import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Capacity.NumericBands

namespace OAI

/-! Constrained Rows. -/

section

namespace UniversalTensorSquare

def clippedSum (rs : List ℕ) (k : ℕ) : ℕ := (rs.map (min k)).sum

def ListRowBounds (rs : List ℕ) (B : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ B, (rs.take p.1).sum ≤ p.2

def ListColBounds (rs : List ℕ) (A : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ A, clippedSum rs p.1 ≤ p.2

def clipBudget (A : List (ℕ × ℕ)) (a : ℕ) : List (ℕ × ℕ) :=
  A.map fun p => (p.1, p.2-min p.1 a)

def rowBudget (B : List (ℕ × ℕ)) (a : ℕ) : List (ℕ × ℕ) :=
  B.filterMap fun p => if 1 < p.1 then some (p.1-1,p.2-a) else none

def rejectedRows (fuel n upper : ℕ) (A B : List (ℕ × ℕ)) : Prop :=
  n < fuel ∨ fuel*upper < n ∨
  (∃ p ∈ A, 0 < p.1 ∧ p.2 < fuel) ∨ (∃ p ∈ B, fuel ≤ p.1 ∧ p.2 < n) ∨
  (∃ p ∈ A, p.2*upper < n*min p.1 upper) ∨
  (∃ p ∈ B, p.2*fuel < n*min p.1 fuel)

instance (fuel n upper : ℕ) (A B : List (ℕ × ℕ)) : Decidable (rejectedRows fuel n upper A B) := by
  unfold rejectedRows; infer_instance

def allowedRow (a : ℕ) (A B : List (ℕ × ℕ)) : Prop :=
  (∀ p ∈ A, min p.1 a ≤ p.2) ∧ (∀ p ∈ B, 0 < p.1 → a ≤ p.2)

instance (a : ℕ) (A B : List (ℕ × ℕ)) : Decidable (allowedRow a A B) := by
  unfold allowedRow; infer_instance

def constrainedRows : ℕ → ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → List (List ℕ)
  | fuel,n,upper,A,B =>
    if rejectedRows fuel n upper A B then [] else
      match fuel with
      | 0 => if n = 0 then [[]] else []
      | k+1 => (List.range' 1 (min n upper)).flatMap fun a =>
          if allowedRow a A B ∧ n ≤ (k+1)*a then
            (constrainedRows k (n-a) a (clipBudget A a) (rowBudget B a)).map (List.cons a)
          else []

lemma list_sum_le_mul_length {rs : List ℕ} {b : ℕ} (h : ∀ a ∈ rs, a ≤ b) :
    rs.sum ≤ rs.length*b := by
  induction rs with
  | nil => simp
  | cons a rs ih =>
    have ha := h a (by simp)
    have hr := ih (fun x hx => h x (by simp [hx]))
    simp only [List.sum_cons,List.length_cons]
    nlinarith

lemma clippedSum_length_le {rs : List ℕ} (hp : ∀ a ∈ rs, 0 < a) {k : ℕ} (hk : 0 < k) :
    rs.length ≤ clippedSum rs k := by
  induction rs with
  | nil => simp [clippedSum]
  | cons a rs ih =>
    have ha := hp a (by simp)
    have ht := ih (fun x hx => hp x (by simp [hx]))
    simp only [clippedSum,List.map_cons,List.sum_cons,List.length_cons] at *
    have : 1 ≤ min k a := le_min hk ha
    omega

lemma clippedSum_proportion {rs : List ℕ} {upper k : ℕ}
    (hu : ∀ a ∈ rs, a ≤ upper) : rs.sum * min k upper ≤ clippedSum rs k * upper := by
  induction rs with
  | nil => simp [clippedSum]
  | cons a rs ih =>
    have ha := hu a (by simp)
    have ht := ih (fun x hx => hu x (by simp [hx]))
    have hm : a * min k upper ≤ min k a * upper := by
      by_cases hk : k ≤ a
      · rw [min_eq_left hk, min_eq_left (hk.trans ha)]
        exact Nat.mul_le_mul_right k ha |>.trans_eq (Nat.mul_comm upper k)
      · rw [min_eq_right (by omega : a ≤ k)]
        exact Nat.mul_le_mul_left a (min_le_right _ _)
    simp only [clippedSum,List.map_cons,List.sum_cons] at *
    nlinarith

lemma cross_product_bound (xs ys : List ℕ)
    (h : ∀ a ∈ xs, ∀ b ∈ ys, b ≤ a) : ys.sum*xs.length ≤ xs.sum*ys.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := list_sum_le_mul_length (fun b hb => h a (by simp) b hb)
    have ht := ih (fun c hc b hb => h c (by simp [hc]) b hb)
    simp only [List.sum_cons,List.length_cons]
    nlinarith

lemma rowSum_proportion {rs : List ℕ} (hs : rs.SortedGE) (k : ℕ) :
    rs.sum * min k rs.length ≤ (rs.take k).sum * rs.length := by
  have he : (rs.take k ++ rs.drop k).Pairwise (· ≥ ·) := by
    simpa only [List.take_append_drop] using hs.pairwise
  have hh := cross_product_bound (rs.take k) (rs.drop k) (List.pairwise_append.mp he).2.2
  have hl : (rs.take k).length + (rs.drop k).length = rs.length := by
    rw [← List.length_append,List.take_append_drop]
  have ht : (rs.take k).sum + (rs.drop k).sum = rs.sum := by
    rw [← List.sum_append,List.take_append_drop]
  rw [List.length_take] at hh hl
  calc
    rs.sum * min k rs.length = ((rs.take k).sum + (rs.drop k).sum)*min k rs.length := by rw [ht]
    _ = (rs.take k).sum*min k rs.length + (rs.drop k).sum*min k rs.length := by ring
    _ ≤ (rs.take k).sum*min k rs.length + (rs.take k).sum*(rs.drop k).length := Nat.add_le_add_left hh _
    _ = (rs.take k).sum*(min k rs.length+(rs.drop k).length) := by ring
    _ = _ := by rw [hl]

lemma rejectedRows_false {rs : List ℕ} {fuel n upper : ℕ} {A B : List (ℕ × ℕ)}
    (hlen : rs.length = fuel) (hsum : rs.sum = n) (hp : ∀ a ∈ rs, 0 < a)
    (hu : ∀ a ∈ rs, a ≤ upper) (hs : rs.SortedGE)
    (ha : ListColBounds rs A) (hb : ListRowBounds rs B) :
    ¬rejectedRows fuel n upper A B := by
  intro hh
  have hlo : fuel ≤ n := by
    rw [← hlen,← hsum]
    exact List.length_le_sum_of_one_le _ hp
  have hhi : n ≤ fuel*upper := by rw [← hsum,← hlen]; exact list_sum_le_mul_length hu
  rcases hh with h | h | ⟨p,hp',hpk,hpU⟩ | ⟨p,hp',hpk,hpU⟩ | ⟨p,hp',hpU⟩ | ⟨p,hp',hpU⟩
  · omega
  · omega
  · have hw := (clippedSum_length_le hp hpk).trans (ha p hp')
    omega
  · have hw := hb p hp'
    rw [List.take_of_length_le (hlen ▸ hpk),hsum] at hw
    omega
  · have hh := (clippedSum_proportion (k := p.1) hu).trans
      (Nat.mul_le_mul_right upper (ha p hp'))
    rw [hsum] at hh
    omega
  · have hh := (rowSum_proportion hs p.1).trans (Nat.mul_le_mul_right rs.length (hb p hp'))
    rw [hsum,hlen] at hh
    omega

lemma allowedRow_cons {a : ℕ} {rs : List ℕ} {A B : List (ℕ × ℕ)}
    (ha : ListColBounds (a::rs) A) (hb : ListRowBounds (a::rs) B) :
    allowedRow a A B := by
  constructor
  · intro p hp
    have hh := ha p hp
    simp only [clippedSum,List.map_cons,List.sum_cons] at hh
    omega
  · intro p hp hk
    have hh := hb p hp
    obtain ⟨k,hk'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p.1 ≠ 0)
    simp only [hk',List.take_succ_cons,List.sum_cons] at hh
    omega

lemma clipBudget_cons {a : ℕ} {rs : List ℕ} {A : List (ℕ × ℕ)}
    (ha : ListColBounds (a::rs) A) : ListColBounds rs (clipBudget A a) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have hh := ha q hq
  simp only [clippedSum,List.map_cons,List.sum_cons] at hh ⊢
  omega

lemma rowBudget_cons {a : ℕ} {rs : List ℕ} {B : List (ℕ × ℕ)}
    (hb : ListRowBounds (a::rs) B) : ListRowBounds rs (rowBudget B a) := by
  intro p hp
  obtain ⟨q,hq,he⟩ := List.mem_filterMap.mp hp
  split_ifs at he with hk
  · have hh := hb q hq
    have heq := Option.some.inj he
    subst p
    have ht : q.1 = (q.1-1)+1 := by omega
    rw [ht,List.take_succ_cons,List.sum_cons] at hh
    dsimp only
    omega

lemma mem_constrainedRows (fuel : ℕ) (rs : List ℕ) (n upper : ℕ) (A B : List (ℕ × ℕ))
    (hlen : rs.length = fuel) (hsum : rs.sum = n) (hp : ∀ a ∈ rs, 0 < a)
    (hu : ∀ a ∈ rs, a ≤ upper) (hs : rs.SortedGE)
    (ha : ListColBounds rs A) (hb : ListRowBounds rs B) :
    rs ∈ constrainedRows fuel n upper A B := by
  have hr := rejectedRows_false hlen hsum hp hu hs ha hb
  induction fuel generalizing rs n upper A B with
  | zero =>
    have he : rs = [] := List.length_eq_zero_iff.mp hlen
    subst rs
    simp only [List.sum_nil] at hsum
    subst n
    simp [constrainedRows,hr]
  | succ fuel ih =>
    cases rs with
    | nil => simp at hlen
    | cons a rs =>
      rw [constrainedRows,ite_eq_right hr]
      apply List.mem_flatMap.mpr
      have hap := hp a (by simp)
      have hau := hu a (by simp)
      have han : a ≤ n := by simp only [List.sum_cons] at hsum; omega
      refine ⟨a,?_,?_⟩
      · simp only [List.mem_range'_1]
        omega
      · have haall : ∀ x ∈ a::rs, x ≤ a := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact le_rfl
          · exact (List.pairwise_cons.mp hs.pairwise).1 x hx
        have hlim : n ≤ (fuel+1)*a := by
          have hh := list_sum_le_mul_length haall
          rw [hsum,hlen] at hh
          exact hh
        rw [ite_eq_left ⟨allowedRow_cons ha hb,hlim⟩]
        apply List.mem_map.mpr
        refine ⟨rs,ih rs (n-a) a (clipBudget A a) (rowBudget B a) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,rfl⟩
        · simpa only [List.length_cons,Nat.succ.injEq] using hlen
        · simp only [List.sum_cons] at hsum; omega
        · exact fun x hx => hp x (by simp [hx])
        · exact fun x hx => (List.pairwise_cons.mp hs.pairwise).1 x hx
        · exact (List.pairwise_cons.mp hs.pairwise).2.sortedGE
        · exact clipBudget_cons ha
        · exact rowBudget_cons hb
        · apply rejectedRows_false
          · simpa only [List.length_cons,Nat.succ.injEq] using hlen
          · simp only [List.sum_cons] at hsum; omega
          · exact fun x hx => hp x (by simp [hx])
          · exact fun x hx => (List.pairwise_cons.mp hs.pairwise).1 x hx
          · exact (List.pairwise_cons.mp hs.pairwise).2.sortedGE
          · exact clipBudget_cons ha
          · exact rowBudget_cons hb

end UniversalTensorSquare
end

end OAI
