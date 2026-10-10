import OAI.RingTheory.DirectFiniteness.BalanceRestriction

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

/-- Add the weight at `a` to the parallel edge `b`, leaving a temporary zero. -/
def transferWeight (w : α → A) (a b x : α) : A :=
  w x + (if x = b then w a else 0) - (if x = a then w a else 0)

omit [Fintype α] in
lemma transferWeight_zero (w : α → A) (a b : α) (hab : a ≠ b) :
    transferWeight w a b a = 0 := by simp [transferWeight, hab]

omit [Fintype α] in
lemma sum_transferWeight (s : Finset α) (w : α → A) (a b : α)
    (hmem : a ∈ s ↔ b ∈ s) : ∑ x ∈ s, transferWeight w a b x = ∑ x ∈ s, w x := by
  classical
  simp only [transferWeight, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq']
  simp only [hmem, add_sub_cancel_right]

omit [Fintype α] in
lemma sum_transferWeight_map (s : Finset α) (w : α → A) (a b : α)
    (f : α → (A →+ B)) (hab : f a = f b)
    (hmem : a ∈ s ↔ b ∈ s) :
    ∑ x ∈ s, f x (transferWeight w a b x) = ∑ x ∈ s, f x (w x) := by
  classical
  have hf : ∀ x, f x (transferWeight w a b x) =
      f x (w x) + (if x = b then f b (w a) else 0) -
        (if x = a then f a (w a) else 0) := by
    intro x
    simp only [transferWeight, map_sub, map_add]
    congr 1
    · congr 1
      split_ifs with h
      · subst x; rfl
      · exact map_zero _
    · split_ifs with h
      · subst x; rfl
      · exact map_zero _
  simp only [hf, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [hmem, hab, add_sub_cancel_right]

lemma cycleSet_mem_iff_of_sameCycle (p : Perm α) {a b : α} (hab : p.SameCycle a b)
    (c : Cycles p) : a ∈ cycleSet p c ↔ b ∈ cycleSet p c := by
  rw [mem_cycleSet, mem_cycleSet, (cycleClass_eq p a b).mpr hab]

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def WeakBalanced.transfer (D : WeakBalanced R Inc ι) (a b : α)
    (hb : R.black.SameCycle a b) (hw : R.white.SameCycle a b) :
    WeakBalanced R Inc ι where
  blackLabel := D.blackLabel
  whiteLabel := D.whiteLabel
  blackLabel_rot := D.blackLabel_rot
  whiteLabel_rot := D.whiteLabel_rot
  incident := D.incident
  weight := transferWeight D.weight a b
  exception := D.exception
  black_sum c := by
    rw [sum_transferWeight_map]
    · exact D.black_sum c
    · rw [label_sameCycle R.black D.blackLabel D.blackLabel_rot hb,
        label_sameCycle R.white D.whiteLabel D.whiteLabel_rot hw]
    · exact cycleSet_mem_iff_of_sameCycle _ hb c
  white_sum c hc := by
    rw [sum_transferWeight _ _ _ _ (cycleSet_mem_iff_of_sameCycle _ hw c)]
    exact D.white_sum c hc
  exceptional_sum := by
    rw [sum_transferWeight _ _ _ _ (cycleSet_mem_iff_of_sameCycle _ hw D.exception)]
    exact D.exceptional_sum

end KaplanskyCounterexample.Planar
end

end OAI
