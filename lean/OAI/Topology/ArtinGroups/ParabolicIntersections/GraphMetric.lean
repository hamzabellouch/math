import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.GroupTheory.GroupAction.Basic

namespace OAI

/-! The real-valued graph metric and the induced isometric action. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {V : Type} (H : SimpleGraph V)

@[instance_reducible]
noncomputable def graphMetric (hH : H.Connected) : MetricSpace V where
  dist x y := H.dist x y
  dist_self x := by simp
  dist_comm x y := by rw [H.dist_comm]
  dist_triangle x y z := by exact_mod_cast hH.dist_triangle (u := x) (v := y) (w := z)
  eq_of_dist_eq_zero h := hH.dist_eq_zero_iff.mp (Nat.cast_eq_zero.mp h)

variable {G : Type} [Group G] [MulAction G V]

lemma graph_action_dist (hH : H.Connected)
    (hA : ∀ g : G,∀ ⦃x y : V⦄,H.Adj x y → H.Adj (g • x) (g • y))
    (g : G) (x y : V) : H.dist (g • x) (g • y)=H.dist x y := by
  have hle (a : G) (u v : V) : H.dist (a • u) (a • v)≤H.dist u v := by
    obtain ⟨p,hp⟩ := hH.exists_walk_length_eq_dist u v
    let f : H →g H := ⟨(a • ·),fun h => hA a h⟩
    have h := H.dist_le (p.map f)
    change H.dist (a • u) (a • v)≤(p.map f).length at h
    simpa only [SimpleGraph.Walk.length_map,hp] using h
  apply le_antisymm (hle g x y)
  simpa only [inv_smul_smul] using hle g⁻¹ (g • x) (g • y)

lemma graph_action_isometric (hH : H.Connected)
    (hA : ∀ g : G,∀ ⦃x y : V⦄,H.Adj x y → H.Adj (g • x) (g • y)) (g : G) :
    let _ := graphMetric H hH
    Isometry (fun x : V => g • x) := by
  let _ := graphMetric H hH
  apply isometry_iff_dist_eq.mpr
  intro x y
  change (H.dist (g • x) (g • y) : ℝ)=(H.dist x y : ℝ)
  exact_mod_cast graph_action_dist H hH hA g x y

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
