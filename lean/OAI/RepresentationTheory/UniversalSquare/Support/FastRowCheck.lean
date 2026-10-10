import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.RowChecker

namespace OAI

/-! Fast Row Check. -/

section

namespace UniversalTensorSquare

def quickBand (M r : ℕ) (rs : List ℕ) : Bool :=
  (List.range 4).any fun k =>
    let d := k+1
    let q := testWidth M d
    decide (d*q+7+d ≤ 2*M-1) && decide (2*M-1 ≤ (rs.take d).sum) &&
      decide (r ≤ ((List.range q).map fun j => (rs.countP (fun a => decide (j < a))-d)/2).sum)

lemma quickBand_sound {M r : ℕ} {rs : List ℕ} (h : quickBand M r rs = true) :
    RowsBand M r rs := by
  obtain ⟨k,hk,hh⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact ⟨k,hk,hh.1.1,hh.1.2,hh.2⟩

def quickResidual (M r : ℕ) (qs : List (List ℕ)) (t : RowTree) (rs : List ℕ) : Bool :=
  let ts := transposeRows rs
  t.find rs || t.find ts || quickBand M r rs || quickBand M r ts ||
    qs.any (fun q => decide (RowsDom rs q) || decide (RowsDom ts q))

lemma quickResidual_sound {M r : ℕ} {qs : List (List ℕ)} {t : RowTree} {rs : List ℕ}
    (h : quickResidual M r qs t rs = true) : TreeResidual M r qs t rs := by
  simp only [quickResidual,Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl (Or.inl (quickBand_sound h))
  · exact Or.inl (Or.inr (Or.inl (quickBand_sound h)))
  · obtain ⟨q,hq,h⟩ := List.any_eq_true.mp h
    simp only [Bool.or_eq_true,decide_eq_true_eq] at h
    exact Or.inl (Or.inr (Or.inr (Or.inl ⟨q,hq,h⟩)))

lemma quickCheckedRows (M r : ℕ) (qs : List (List ℕ)) (t : RowTree)
    (fuel n upper : ℕ) (A B : List (ℕ × ℕ))
    (h : checkRowPrefixes (quickResidual M r qs t) fuel n upper A B [] = true) :
    ∀ rs ∈ constrainedRows fuel n upper A B, TreeResidual M r qs t rs := by
  intro rs hrs
  apply quickResidual_sound
  simpa only [List.reverse_nil,List.nil_append] using
    checkRowPrefixes_sound (quickResidual M r qs t) fuel n upper A B [] h rs hrs

end UniversalTensorSquare
end

end OAI
