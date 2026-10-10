import OAI.RingTheory.DirectFiniteness.DiagramObstruction

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]
variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def WeakBalanced.split_none (D : WeakBalanced R (augInc Inc) (augMap ι))
    (a b : α) (ha : D.blackLabel a = none) (hb : D.blackLabel b = none)
    (hab : R.black.SameCycle a b) : WeakBalanced (R.swapBlack a b) (augInc Inc) (augMap ι) where
  blackLabel := D.blackLabel
  whiteLabel := D.whiteLabel
  blackLabel_rot x := by
    apply label_sameCycle R.black D.blackLabel D.blackLabel_rot
    exact sameCycle_after_swap hab (SameCycle.apply_left SameCycle.rfl)
  whiteLabel_rot := D.whiteLabel_rot
  incident := D.incident
  weight := D.weight
  exception := D.exception
  black_sum c := by
    induction c using Quotient.inductionOn with
    | h x =>
      by_cases hx : D.blackLabel x = none
      · apply Finset.sum_eq_zero
        intro y hy
        have hyx : R.black.SameCycle y x := sameCycle_after_swap hab
          ((cycleClass_eq _ _ _).mp ((mem_cycleSet _ _ _).mp hy))
        have hl := label_sameCycle R.black D.blackLabel D.blackLabel_rot hyx
        simp only [hl, hx, augMap, AddMonoidHom.zero_apply]
      · have heq (z : α) (hz : R.black.SameCycle x z) :
            (R.swapBlack a b).black z = R.black z := by
          change swap a b (R.black z) = R.black z
          apply swap_apply_of_ne_of_ne
          · intro hz'
            have hl := label_sameCycle R.black D.blackLabel D.blackLabel_rot
              hz.apply_right
            rw [hz', ha] at hl
            exact hx hl
          · intro hz'
            have hl := label_sameCycle R.black D.blackLabel D.blackLabel_rot
              hz.apply_right
            rw [hz', hb] at hl
            exact hx hl
        change (∑ y ∈ cycleSet (R.swapBlack a b).black
          (cycleClass _ x), augMap ι (D.blackLabel y) (D.whiteLabel y) (D.weight y)) = 0
        rw [cycleSet_eq_of_eqOn_cycle R.black (R.swapBlack a b).black x heq]
        exact D.black_sum _
  white_sum := D.white_sum
  exceptional_sum := D.exceptional_sum

def WeakBalanced.fill (D : WeakBalanced R (augInc Inc) (augMap ι))
    (l : List α) (hd : l.Nodup) (hrot : Follows R.black l) (v : V)
    (hinc : ∀ x ∈ l, Inc v (D.whiteLabel x))
    (hsum : (∑ x ∈ l.toFinset, ι v (D.whiteLabel x) (D.weight x)) = 0) :
    WeakBalanced R (augInc Inc) (augMap ι) where
  blackLabel x := if x ∈ l then some v else D.blackLabel x
  whiteLabel := D.whiteLabel
  blackLabel_rot x := by simp only [hrot.invariant, D.blackLabel_rot]
  whiteLabel_rot := D.whiteLabel_rot
  incident x := by
    by_cases hx : x ∈ l
    · simpa only [ite_eq_left hx, augInc] using hinc x hx
    · simpa only [ite_eq_right hx] using D.incident x
  weight := D.weight
  exception := D.exception
  black_sum c := by
    induction c using Quotient.inductionOn with
    | h x =>
      by_cases hx : x ∈ l
      · change (∑ y ∈ cycleSet R.black (cycleClass R.black x), _) = 0
        rw [hrot.cycleSet hd hx]
        calc
          _ = ∑ y ∈ l.toFinset, ι v (D.whiteLabel y) (D.weight y) := by
            apply Finset.sum_congr rfl
            intro y hy
            simp only [List.mem_toFinset.mp hy, ↓reduceIte, augMap]
          _ = 0 := hsum
      · calc
          _ = ∑ y ∈ cycleSet R.black ⟦x⟧,
              augMap ι (D.blackLabel y) (D.whiteLabel y) (D.weight y) := by
            apply Finset.sum_congr rfl
            intro y hy
            have hxy : R.black.SameCycle y x :=
              (cycleClass_eq _ _ _).mp ((mem_cycleSet _ _ _).mp hy)
            have hy' : y ∉ l := fun hy' => hx
              ((perm_invariant_cycle R.black (fun z => z ∈ l) hrot.invariant hxy).mp hy')
            rw [ite_eq_right hy']
          _ = 0 := D.black_sum _
  white_sum := D.white_sum
  exceptional_sum := D.exceptional_sum

end KaplanskyCounterexample.Planar

end

end OAI
