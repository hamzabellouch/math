import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.BandGluing

namespace OAI

/-! Column Clearance. -/

section

noncomputable section
namespace Saxl.FlagColumns

lemma columnsAway_append (K : ℕ) (xs ys : List (ℕ × ℕ)) (o : ℕ) :
    columnsAway K (xs++ys) o ↔
      columnsAway K xs o ∧ columnsAway K ys (o+(xs.map Prod.fst).sum) := by
  induction xs generalizing o with
  | nil => simp [columnsAway]
  | cons x xs ih =>
    obtain ⟨a,b⟩ := x
    simp only [List.cons_append, columnsAway, ih, List.map_cons, List.sum_cons]
    simp only [Nat.add_assoc, and_assoc]

lemma columnsAway_of_zero (K : ℕ) (ps : List (ℕ × ℕ))
    (h : ∀ p ∈ ps, p.2 = 0) (o : ℕ) : columnsAway K ps o := by
  induction ps generalizing o with
  | nil => trivial
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    exact ⟨fun hb => (hb (h (a,b) (by simp))).elim,
      ih (fun p hp => h p (by simp [hp])) _⟩

lemma columnsAway_of_bounds (K : ℕ) (ps : List (ℕ × ℕ)) (o : ℕ)
    (hl : 4 ≤ o) (hr : o+(ps.map Prod.fst).sum+4 ≤ K) : columnsAway K ps o := by
  induction ps generalizing o with
  | nil => trivial
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    simp only [List.map_cons, List.sum_cons] at hr
    exact ⟨fun _ => ⟨hl,by omega⟩, ih (o+a) (by omega) (by omega)⟩

lemma prefix_bounded_sum {α : Type*} (w : α → ℕ) (d : ℕ)
    (xs : List α) (hb : ∀ x ∈ xs, w x ≤ d) (k : ℕ)
    (hk : k ≤ (xs.map w).sum) :
    ∃ pre post, xs = pre++post ∧ k ≤ (pre.map w).sum ∧
      (pre.map w).sum ≤ k+(d-1) := by
  induction xs generalizing k with
  | nil =>
    exact ⟨[],[],rfl,hk,by simp⟩
  | cons x xs ih =>
    by_cases hk0 : k = 0
    · subst k
      exact ⟨[],x::xs,rfl,by simp,by simp⟩
    by_cases hx : k ≤ w x
    · refine ⟨[x],xs,rfl,by simpa using hx,?_⟩
      have hh := hb x (by simp)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
    · have hk' : k-w x ≤ (xs.map w).sum := by
        simp only [List.map_cons, List.sum_cons] at hk
        omega
      obtain ⟨pre,post,hpp,hl,hr⟩ := ih (fun x hx => hb x (by simp [hx])) (k-w x) hk'
      refine ⟨x::pre,post,by rw [hpp]; rfl,?_,?_⟩ <;>
        simp only [List.map_cons, List.sum_cons] <;> omega

theorem reorder_columns_away (ps : List (ℕ × ℕ)) (d K q : ℕ)
    (hK : (ps.map Prod.fst).sum = K)
    (ha : ∀ p ∈ ps, p.1 ≤ d) (hb : ∀ p ∈ ps, p.2 ≠ 0 → p.1 = d)
    (hc : (ps.filter (fun p => p.2 ≠ 0)).length ≤ q)
    (hclear : d*q+7+d ≤ K) :
    ∃ qs : List (ℕ × ℕ), qs.Perm ps ∧ columnsAway K qs 0 := by
  classical
  let chosen := ps.filter (fun p => p.2 ≠ 0)
  let free := ps.filter (fun p => p.2 = 0)
  have hperm : (chosen++free).Perm ps := by
    simpa only [chosen,free,decide_not, Bool.not_not] using
      List.filter_append_perm (fun p : ℕ × ℕ => decide (p.2 ≠ 0)) ps
  have hchosen : (chosen.map Prod.fst).sum = chosen.length*d := by
    have he : chosen.map Prod.fst = chosen.map (fun _ => d) := by
      apply List.map_congr_left
      intro p hp
      exact hb p (List.mem_filter.mp hp).1 (of_decide_eq_true (List.mem_filter.mp hp).2)
    rw [he, List.map_const', List.sum_replicate, smul_eq_mul]
  have hsum : (chosen.map Prod.fst).sum+(free.map Prod.fst).sum = K := by
    simpa only [List.map_append, List.sum_append] using (hperm.map Prod.fst).sum_eq.trans hK
  have hlen : chosen.length*d ≤ d*q := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left d hc
  have hd : 1 ≤ d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have hz : (ps.map Prod.fst).sum = 0 := List.sum_eq_zero_iff.mpr (by
      intro a ha'
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha'
      have H := ha p hp
      rw [hd0] at H
      exact Nat.le_zero.mp H)
    omega
  have hfree : 7+d ≤ (free.map Prod.fst).sum := by rw [hchosen] at hsum; omega
  obtain ⟨pre,post,hpp,hl,hr⟩ := prefix_bounded_sum Prod.fst d free
    (fun p hp => ha p (List.mem_filter.mp hp).1) 4 (by omega)
  have hz : ∀ p ∈ pre++post, p.2 = 0 := by
    rw [← hpp]
    intro p hp
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  have hs : (pre.map Prod.fst).sum+(chosen.map Prod.fst).sum+(post.map Prod.fst).sum = K := by
    rw [hpp,List.map_append,List.sum_append] at hsum
    omega
  have hpost : 4 ≤ (post.map Prod.fst).sum := by
    rw [hpp,List.map_append,List.sum_append] at hfree
    omega
  refine ⟨pre++chosen++post,?_,?_⟩
  · rw [List.append_assoc]
    apply List.Perm.trans _ hperm
    rw [hpp]
    simpa only [List.append_assoc] using (List.Perm.append_right post
      (List.perm_append_comm (l₁ := pre) (l₂ := chosen)))
  · rw [columnsAway_append, columnsAway_append]
    refine ⟨⟨columnsAway_of_zero K pre (fun p hp => hz p (List.mem_append_left _ hp)) 0,?_⟩,?_⟩
    · apply columnsAway_of_bounds <;> omega
    · exact columnsAway_of_zero K post (fun p hp => hz p (List.mem_append_right _ hp)) _

end Saxl.FlagColumns
end
end

end OAI
