import OAI.RingTheory.DirectFiniteness.CycleSplitting

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} [Fintype α]

def Ribbon.swapBlack (R : Ribbon α) (a b : α) : Ribbon α :=
  ⟨swap a b * R.black, R.white⟩

omit [Fintype α] in
lemma Ribbon.swapBlack_twice (R : Ribbon α) (a b : α) :
    (R.swapBlack a b).swapBlack a b = R := by
  cases R
  simp [Ribbon.swapBlack, ← mul_assoc]

omit [Fintype α] in
lemma Ribbon.swapBlack_face (R : Ribbon α) (a b : α) :
    (R.swapBlack a b).face = swap (R.white a) (R.white b) * R.face := by
  simp only [Ribbon.face, Ribbon.swapBlack, ← mul_assoc]
  rw [mul_swap_eq_swap_mul]

lemma Ribbon.swapBlack_components_merge (R : Ribbon α) (a b : α)
    (hab : ¬ R.black.SameCycle a b) :
    (R.swapBlack a b).components = joinPair R.components a b := by
  apply le_antisymm
  · apply (R.swapBlack a b).components_le_of_steps
    · intro x
      exact (joinPair R.components a b).iseqv.trans
        (le_joinPair _ _ _ (R.black_step x))
        (setoid_swap_related _ (joinPair_related _ _ _) _)
    · intro x
      exact le_joinPair _ _ _ (R.white_step x)
  · apply joinPair_le
    · apply sup_le
      · intro x y hxy
        exact (show SameCycle.setoid (R.swapBlack a b).black ≤
            (R.swapBlack a b).components from le_sup_left)
          (sameCycle_swap_mul R.black a b hab hxy)
      · exact le_sup_right
    · exact (show SameCycle.setoid (R.swapBlack a b).black ≤
          (R.swapBlack a b).components from le_sup_left)
        (swap_mul_sameCycle R.black a b hab)

omit [Fintype α] in
lemma Ribbon.not_blackCycle_of_not_component (R : Ribbon α) {a b : α}
    (h : ¬ R.components.r a b) : ¬ R.black.SameCycle a b :=
  fun hab => h ((show SameCycle.setoid R.black ≤ R.components from le_sup_left) hab)

lemma Ribbon.not_white_faceCycle_of_not_component (R : Ribbon α) {a b : α}
    (h : ¬ R.components.r a b) : ¬ R.face.SameCycle (R.white a) (R.white b) := by
  intro hab
  exact h (R.components.iseqv.trans (R.white_step a)
    (R.components.iseqv.trans (R.sameCycle_face_components hab)
      (R.components.iseqv.symm (R.white_step b))))

/-- Gluing black vertices from distinct connected components preserves genus zero. -/
lemma Ribbon.genusZero_swapBlack_merge (R : Ribbon α) (hR : R.GenusZero) (a b : α)
    (hab : ¬ R.components.r a b) : (R.swapBlack a b).GenusZero := by
  have hb := R.not_blackCycle_of_not_component hab
  have hbc := swap_mul_cycles_card R.black a b hb
  have hfc := swap_mul_cycles_card R.face (R.white a) (R.white b)
    (R.not_white_faceCycle_of_not_component hab)
  have hcc := joinPair_card R.components a b hab
  rw [← R.swapBlack_components_merge a b hb] at hcc
  rw [← R.swapBlack_face a b] at hfc
  change Nat.card (Cycles (R.swapBlack a b).black) + 1 = _ at hbc
  have hw : (R.swapBlack a b).white = R.white := rfl
  unfold Ribbon.GenusZero at hR ⊢
  rw [hw]
  omega

/-- Splitting one black vertex preserves genus zero, even when the split
separates its connected component into two. -/
lemma Ribbon.genusZero_swapBlack_split (R : Ribbon α) (hR : R.GenusZero) (a b : α)
    (hne : a ≠ b) (hab : R.black.SameCycle a b) : (R.swapBlack a b).GenusZero := by
  let S := R.swapBlack a b
  have hback : S.swapBlack a b = R := R.swapBlack_twice a b
  have hn : ¬ S.black.SameCycle a b := not_sameCycle_swap_of_sameCycle R.black a b hne hab
  have hbc := swap_mul_cycles_card_split R.black a b hne hab
  change Nat.card (Cycles S.black) = Nat.card (Cycles R.black) + 1 at hbc
  have hw : S.white = R.white := rfl
  have hcomp := S.swapBlack_components_merge a b hn
  rw [hback] at hcomp
  by_cases hc : S.components.r a b
  · rw [joinPair_eq_of_related S.components hc] at hcomp
    have hfc := swap_cycles_card_le S.face (S.white a) (S.white b)
    rw [← S.swapBlack_face a b, hback] at hfc
    have hbnd := S.euler_le
    unfold Ribbon.GenusZero at hR ⊢
    change Nat.card (Cycles S.black) + Nat.card (Cycles S.white) +
      Nat.card (Cycles S.face) = Fintype.card α + 2 * Nat.card (Quotient S.components)
    rw [hw] at hbnd ⊢
    rw [hcomp] at hR
    omega
  · have hcc := joinPair_card S.components a b hc
    rw [← hcomp] at hcc
    have hfc := swap_mul_cycles_card S.face (S.white a) (S.white b)
      (S.not_white_faceCycle_of_not_component hc)
    rw [← S.swapBlack_face a b, hback] at hfc
    unfold Ribbon.GenusZero at hR ⊢
    change Nat.card (Cycles S.black) + Nat.card (Cycles S.white) +
      Nat.card (Cycles S.face) = Fintype.card α + 2 * Nat.card (Quotient S.components)
    rw [hw]
    omega

end KaplanskyCounterexample.Planar

end

end OAI
