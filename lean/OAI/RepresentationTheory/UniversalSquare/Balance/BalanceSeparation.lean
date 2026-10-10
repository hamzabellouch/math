import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.SquareDetection

namespace OAI

/-! Balance Separation. -/

section

noncomputable section
namespace Saxl

lemma equal_sets_of_card_sum_gap {X : Type*} [DecidableEq X]
    (A B : Finset X) (z : X → ℤ) (hc : A.card = B.card)
    (hz : ∑ x ∈ A, z x = ∑ x ∈ B, z x)
    (hgap : ∀ x ∈ A \ B, ∀ y ∈ B \ A, z y < z x) : A = B := by
  classical
  have he := Finset.card_sdiff_comm hc
  let e : ↥(A \ B) ≃ ↥(B \ A) := Finset.equivOfCardEq he
  have hsum : ∑ x ∈ A \ B, z x = ∑ x ∈ B \ A, z x := by
    have h₁ := Finset.sum_sdiff_eq_sub (f := z) (Finset.inter_subset_left (s₁ := A) (s₂ := B))
    have h₂ := Finset.sum_sdiff_eq_sub (f := z) (Finset.inter_subset_right (s₁ := A) (s₂ := B))
    simp only [Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right] at h₁ h₂
    rw [h₁, h₂, hz]
  have hn : A \ B = ∅ := by
    by_contra hn
    have hs : (Finset.univ : Finset ↥(A \ B)).Nonempty := by
      obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hn
      exact ⟨⟨x,hx⟩,Finset.mem_univ _⟩
    have hh : (∑ x : ↥(A \ B), z (e x)) < ∑ x : ↥(A \ B), z x := by
      apply Finset.sum_lt_sum_of_nonempty hs
      intro x hx
      exact hgap x.val x.property (e x).val (e x).property
    rw [Equiv.sum_comp e (fun y : ↥(B \ A) => z y),
      Finset.sum_coe_sort, Finset.sum_coe_sort, hsum] at hh
    exact lt_irrefl _ hh
  exact Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp hn) hc.ge

theorem ordered_output_fibers_eq {X : Type*} [DecidableEq X]
    (s : Finset X) (a b : X → ℕ) (z : X → ℤ)
    (ho : ∀ x ∈ s, ∀ y ∈ s, b x < b y → z x < z y)
    (hc : ∀ k, (s.filter (fun x => a x = k)).card =
      (s.filter (fun x => b x = k)).card)
    (hz : ∀ k, ∑ x ∈ s.filter (fun x => a x = k), z x =
      ∑ x ∈ s.filter (fun x => b x = k), z x) :
    ∀ k, s.filter (fun x => a x = k) = s.filter (fun x => b x = k) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    apply equal_sets_of_card_sum_gap _ _ z (hc k) (hz k)
    intro x hx y hy
    obtain ⟨hxA,hxB⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hyB,hyA⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨hxs,hxa⟩ := Finset.mem_filter.mp hxA
    obtain ⟨hys,hyb⟩ := Finset.mem_filter.mp hyB
    have hxne : b x ≠ k := by
      intro hh
      exact hxB (Finset.mem_filter.mpr ⟨hxs,hh⟩)
    have hxge : k ≤ b x := by
      by_contra hh
      have hh' : b x < k := Nat.lt_of_not_ge hh
      have hi := ih (b x) hh'
      have hx' : x ∈ s.filter (fun w => a w = b x) := by
        rw [hi]
        exact Finset.mem_filter.mpr ⟨hxs,rfl⟩
      have ha := (Finset.mem_filter.mp hx').2
      omega
    exact ho y hys x hxs (by omega)

lemma ordered_output_labels_eq {X : Type*} [DecidableEq X]
    (s : Finset X) (a b : X → ℕ) (z : X → ℤ)
    (ho : ∀ x ∈ s, ∀ y ∈ s, b x < b y → z x < z y)
    (hc : ∀ k, (s.filter (fun x => a x = k)).card =
      (s.filter (fun x => b x = k)).card)
    (hz : ∀ k, ∑ x ∈ s.filter (fun x => a x = k), z x =
      ∑ x ∈ s.filter (fun x => b x = k), z x) :
    ∀ x ∈ s, a x = b x := by
  intro x hx
  have he := ordered_output_fibers_eq s a b z ho hc hz (b x)
  have hh : x ∈ s.filter (fun w => a w = b x) := by
    rw [he]
    exact Finset.mem_filter.mpr ⟨hx,rfl⟩
  exact (Finset.mem_filter.mp hh).2

end Saxl
end
end

end OAI
