import OAI.RingTheory.DirectFiniteness.BoundaryFilling

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1}

lemma Follows.append_rotate {p : Perm α} {l m : List α} (h : Follows p (l ++ m))
    (hd : (l ++ m).Nodup) : Follows p (m ++ l) := by
  intro x hx
  have hx' : x ∈ l ++ m := by simpa only [List.mem_append, or_comm] using hx
  rw [h x hx', List.formPerm_eq_of_isRotated hd List.isRotated_append]

lemma Follows.split {p : Perm α} {a b : α} {l m : List α}
    (h : Follows p ((a :: l) ++ (b :: m))) (hd : ((a :: l) ++ (b :: m)).Nodup) :
    Follows (swap a b * p) (a :: l) ∧ Follows (swap a b * p) (b :: m) := by
  classical
  have hdis : List.Disjoint (a :: l) (b :: m) := by
    intro x hx hy
    exact (List.nodup_append.mp hd).2.2 x hx x hy rfl
  have hb : b ∉ a :: l := fun hb => hdis hb (by simp)
  have heq (x : α) (hx : x ∈ (a :: l) ++ (b :: m)) :
      (swap a b * p) x = (a :: l).formPerm ((b :: m).formPerm x) := by
    rw [Perm.mul_apply, h x hx, formPerm_append_nonempty a b l m hb]
    simp only [Perm.mul_apply, swap_apply_self]
  constructor
  · intro x hx
    have hx' : x ∉ b :: m := fun hx' => hdis hx hx'
    rw [heq x (List.mem_append_left _ hx), List.formPerm_apply_of_notMem hx']
  · intro x hx
    rw [heq x (List.mem_append_right _ hx)]
    apply List.formPerm_apply_of_notMem
    exact fun hx' => hdis hx' ((b :: m).formPerm_apply_mem_of_mem hx)

end KaplanskyCounterexample.Planar

end

end OAI
