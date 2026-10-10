import OAI.RingTheory.DirectFiniteness.WordWheels

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {β : Type u_2}

lemma Follows.map_sum_right {p : Perm α} {q : Perm β} {l : List β}
    (h : Follows q l) : Follows (Equiv.sumCongr p q) (l.map Sum.inr) := by
  classical
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simpa only [Equiv.sumCongr_apply, Sum.map_inr,
    formPerm_map_apply Sum.inr Sum.inr_injective] using congrArg Sum.inr (h x hx)

lemma Follows.merge {p : Perm α} {a b : α} {l m : List α}
    (hl : Follows p (a :: l)) (hm : Follows p (b :: m))
    (hdis : List.Disjoint (a :: l) (b :: m)) :
    Follows (swap a b * p) ((a :: l) ++ (b :: m)) := by
  classical
  have hb : b ∉ a :: l := fun hb => hdis hb (by simp)
  intro x hx
  rw [formPerm_append_nonempty a b l m hb]
  simp only [Perm.mul_apply]
  apply congrArg (swap a b)
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.formPerm_apply_of_notMem (fun h => hdis hx h)]
    exact hl x hx
  · rw [List.formPerm_apply_of_notMem (fun h => hdis h ((b :: m).formPerm_apply_mem_of_mem hx))]
    exact hm x hx

variable [Fintype α]
variable {V : Type u_3} {F : Type u_4} {A : Type u_5} {B : Type u_6} [AddCommGroup A] [AddCommGroup B]
variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def WeakBalanced.joinBlack (D : WeakBalanced R Inc ι) (a b : α)
    (hcycle : ¬ R.black.SameCycle a b) (hlabel : D.blackLabel a = D.blackLabel b) :
    WeakBalanced (R.swapBlack a b) Inc ι :=
  D.coarsen (R.swapBlack a b) (sameCycle_swap_mul R.black a b hcycle) (fun h => h)
    (fun x => by
      change D.blackLabel (swap a b (R.black x)) = D.blackLabel x
      rw [label_swap D.blackLabel a b hlabel, D.blackLabel_rot]) D.whiteLabel_rot

end KaplanskyCounterexample.Planar

end

end OAI
