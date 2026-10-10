import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Row Checker. -/

section

namespace UniversalTensorSquare

def quickRejected (fuel n upper : ℕ) (A B : List (ℕ × ℕ)) : Bool :=
  decide (n < fuel) || decide (fuel*upper < n) ||
    A.any (fun p => decide (0 < p.1) && decide (p.2 < fuel)) ||
    B.any (fun p => decide (fuel ≤ p.1) && decide (p.2 < n)) ||
    A.any (fun p => decide (p.2*upper < n*min p.1 upper)) ||
    B.any (fun p => decide (p.2*fuel < n*min p.1 fuel))

lemma quickRejected_iff (fuel n upper : ℕ) (A B : List (ℕ × ℕ)) :
    quickRejected fuel n upper A B = true ↔ rejectedRows fuel n upper A B := by
  simp only [quickRejected,rejectedRows,Bool.or_eq_true,Bool.and_eq_true,
    List.any_eq_true,decide_eq_true_eq]
  simp only [or_assoc]

def quickAllowed (a : ℕ) (A B : List (ℕ × ℕ)) : Bool :=
  A.all (fun p => decide (min p.1 a ≤ p.2)) &&
    B.all (fun p => decide (p.1 = 0) || decide (a ≤ p.2))

lemma quickAllowed_iff (a : ℕ) (A B : List (ℕ × ℕ)) :
    quickAllowed a A B = true ↔ allowedRow a A B := by
  simp only [quickAllowed,allowedRow,Bool.and_eq_true,List.all_eq_true,
    Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hA,hB⟩
    refine ⟨hA,fun p hp hk => ?_⟩
    obtain h | h := hB p hp
    · omega
    · exact h
  · rintro ⟨hA,hB⟩
    refine ⟨hA,fun p hp => ?_⟩
    by_cases hz : p.1 = 0
    · exact Or.inl hz
    · exact Or.inr (hB p hp (by omega))

def checkRowPrefixes (P : List ℕ → Bool) : ℕ → ℕ → ℕ →
    List (ℕ × ℕ) → List (ℕ × ℕ) → List ℕ → Bool
  | fuel,n,upper,A,B,pref =>
      if quickRejected fuel n upper A B then true else
      match fuel with
      | 0 => if n = 0 then P pref.reverse else true
      | k+1 =>
          let lo := max 1 (n/(k+1))
          (List.range' lo (min n upper+1-lo)).all fun a =>
            if quickAllowed a A B && decide (n ≤ (k+1)*a) then
              checkRowPrefixes P k (n-a) a (clipBudget A a) (rowBudget B a) (a::pref)
            else true

lemma checkRowPrefixes_sound (P : List ℕ → Bool) (fuel n upper : ℕ)
    (A B : List (ℕ × ℕ)) (pref : List ℕ)
    (hc : checkRowPrefixes P fuel n upper A B pref = true) :
    ∀ rs ∈ constrainedRows fuel n upper A B, P (pref.reverse ++ rs) = true := by
  induction fuel generalizing n upper A B pref with
  | zero =>
    intro rs hrs
    rw [constrainedRows] at hrs
    split_ifs at hrs with hrej hn
    · simp at hrs
    · simp only [List.mem_singleton] at hrs
      subst rs
      simpa only [checkRowPrefixes, quickRejected_iff, ite_eq_right hrej, ite_eq_left hn, List.append_nil] using hc
    · simp at hrs
  | succ k ih =>
    intro rs hrs
    rw [constrainedRows] at hrs
    split_ifs at hrs with hrej
    · simp at hrs
    · obtain ⟨a,ha,hr⟩ := List.mem_flatMap.mp hrs
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
        rw [checkRowPrefixes] at hc
        simp only [quickRejected_iff, ite_eq_right hrej] at hc
        have hh := List.all_eq_true.mp hc a hai
        simp only [Bool.and_eq_true,quickAllowed_iff,decide_eq_true_eq,ite_eq_left hallowed] at hh
        have hi := ih (n-a) a (clipBudget A a) (rowBudget B a) (a::pref) hh ys hy
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hi
      · simp at hr

lemma checked_constrainedRows (P : List ℕ → Prop) [DecidablePred P]
    (fuel n upper : ℕ) (A B : List (ℕ × ℕ))
    (h : checkRowPrefixes (fun rs => decide (P rs)) fuel n upper A B [] = true) :
    ∀ rs ∈ constrainedRows fuel n upper A B, P rs := by
  intro rs hrs
  have hh := checkRowPrefixes_sound (fun rs => decide (P rs)) fuel n upper A B [] h rs hrs
  simp only [List.reverse_nil,List.nil_append] at hh
  exact of_decide_eq_true hh

end UniversalTensorSquare
end

end OAI
