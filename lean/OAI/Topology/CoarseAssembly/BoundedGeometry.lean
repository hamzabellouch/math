import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Uniformly bounded degree gives uniformly finite graph balls

The elementary bounded-geometry argument used in §3 of the coarse Novikov
manuscript. Finite neighbor lists are supplied for an arbitrary graph; no
finiteness assumption is made about the whole vertex set. The bound
`(degreeBound + 1)^radius` is sufficient for the application.
-/

namespace CoarseAssembly

variable {V : Type*} [DecidableEq V]

/-- A finite over-approximation of vertices reached in at most `r` edges. -/
def walkBall (neighbors : V → Finset V) (x : V) : ℕ → Finset V
  | 0 => {x}
  | r + 1 => walkBall neighbors x r ∪ (walkBall neighbors x r).biUnion neighbors

@[simp] theorem mem_walkBall_zero (neighbors : V → Finset V) (x y : V) :
    y ∈ walkBall neighbors x 0 ↔ y = x := by simp [walkBall]

theorem walkBall_mono_step (neighbors : V → Finset V) (x : V) (r : ℕ) :
    walkBall neighbors x r ⊆ walkBall neighbors x (r + 1) :=
  Finset.subset_union_left

theorem walkBall_mono (neighbors : V → Finset V) (x : V) {r s : ℕ} (h : r ≤ s) :
    walkBall neighbors x r ⊆ walkBall neighbors x s := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @step s h ih => exact ih.trans (walkBall_mono_step neighbors x s)

/-- A uniform degree bound bounds every finite combinatorial ball. -/
theorem card_walkBall_le (neighbors : V → Finset V) (d : ℕ)
    (hd : ∀ v, (neighbors v).card ≤ d) (x : V) (r : ℕ) :
    (walkBall neighbors x r).card ≤ (d + 1) ^ r := by
  induction r with
  | zero => simp [walkBall]
  | succ r ih =>
    calc
      (walkBall neighbors x (r + 1)).card ≤
          (walkBall neighbors x r).card + ((walkBall neighbors x r).biUnion neighbors).card :=
        Finset.card_union_le _ _
      _ ≤ (walkBall neighbors x r).card + (walkBall neighbors x r).card * d := by
        exact Nat.add_le_add_left
          (Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => hd v)) _
      _ = (d + 1) * (walkBall neighbors x r).card := by ring
      _ ≤ (d + 1) * (d + 1) ^ r := Nat.mul_le_mul_left _ ih
      _ = (d + 1) ^ (r + 1) := by rw [pow_succ, Nat.mul_comm]

variable {G : SimpleGraph V}

/-- Each walk endpoint belongs to the finite ball of its length. -/
theorem endpoint_mem_walkBall (neighbors : V → Finset V)
    (hN : ∀ u v, G.Adj u v → v ∈ neighbors u) {x y : V} (p : G.Walk x y) :
    y ∈ walkBall neighbors x p.length := by
  induction p using SimpleGraph.Walk.concatRec with
  | Hnil => simp [walkBall]
  | @Hconcat x y z p h ih =>
    rw [SimpleGraph.Walk.length_concat]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, ih, hN y z h⟩)

/-- Closed graph balls are finite, uniformly in the center. -/
theorem finite_edist_ball (neighbors : V → Finset V)
    (hN : ∀ u v, G.Adj u v → v ∈ neighbors u) (x : V) (r : ℕ) :
    {y | G.edist x y ≤ (r : ℕ∞)}.Finite := by
  apply (walkBall neighbors x r).finite_toSet.subset
  intro y hy
  obtain ⟨p, hp⟩ := G.exists_walk_of_edist_ne_top (ne_of_lt (lt_of_le_of_lt hy (by simp)))
  have hlen : p.length ≤ r := by exact_mod_cast hp.trans_le hy
  exact walkBall_mono neighbors x hlen (endpoint_mem_walkBall neighbors hN p)

/-- An explicit cardinal bound independent of the center. -/
theorem ncard_edist_ball_le (neighbors : V → Finset V) (d : ℕ)
    (hN : ∀ u v, G.Adj u v → v ∈ neighbors u)
    (hd : ∀ v, (neighbors v).card ≤ d) (x : V) (r : ℕ) :
    Set.ncard {y | G.edist x y ≤ (r : ℕ∞)} ≤ (d + 1) ^ r := by
  apply le_trans (Set.ncard_le_ncard ?_ (walkBall neighbors x r).finite_toSet)
    (by simpa using card_walkBall_le neighbors d hd x r)
  intro y hy
  obtain ⟨p, hp⟩ := G.exists_walk_of_edist_ne_top (ne_of_lt (lt_of_le_of_lt hy (by simp)))
  have hlen : p.length ≤ r := by exact_mod_cast hp.trans_le hy
  exact walkBall_mono neighbors x hlen (endpoint_mem_walkBall neighbors hN p)

end CoarseAssembly

end OAI
