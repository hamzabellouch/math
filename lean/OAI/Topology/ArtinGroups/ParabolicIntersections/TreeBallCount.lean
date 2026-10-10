import OAI.Topology.ArtinGroups.ParabolicIntersections.TreePathMetric
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat

namespace OAI

/-! Uniformly bounded intersections of a tree path with a metric ball. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (T : SimpleGraph V)

lemma path_prefix_dist (hT : T.IsAcyclic) {x y : V}
    (p : T.Walk x y) (hp : p.IsPath) (i : ℕ) (hi : i≤p.length) :
    T.dist x (p.getVert i)=i := by
  have he := path_length_eq_dist T hT (p.take i) (hp.take i)
  rw [SimpleGraph.Walk.take_length,Nat.min_eq_left hi] at he
  exact he.symm

lemma path_index_dist (hT : T.IsAcyclic) {x y w : V}
    (p : T.Walk x y) (hp : p.IsPath) (hw : w∈p.support) :
    T.dist x w=p.support.idxOf w := by
  have hi : p.support.idxOf w≤p.length := by
    have h := List.idxOf_lt_length_of_mem hw
    rw [SimpleGraph.Walk.length_support] at h
    omega
  have he := path_prefix_dist T hT p hp _ hi
  rwa [SimpleGraph.Walk.getVert_support_idxOf p hw] at he

/-- Even in a tree of infinite valence, a radius-`L` ball meets a simple
path in at most `2L+1` vertices. -/
theorem path_ball_ncard (hT : T.IsTree) {x y b : V}
    (p : T.Walk x y) (hp : p.IsPath) (hb : b∈p.support) (L : ℕ) :
    {w | w∈p.support ∧ T.dist b w≤L}.ncard≤2*L+1 := by
  let i := p.support.idxOf b
  let C := Finset.Icc (i-L) (i+L)
  have hsubset : {w | w∈p.support ∧ T.dist b w≤L} ⊆
      (↑(C.image p.getVert) : Set V) := by
    intro w hw
    let j := p.support.idxOf w
    have hdw : T.dist x w=j := path_index_dist T hT.isAcyclic p hp hw.1
    have hdb : T.dist x b=i := path_index_dist T hT.isAcyclic p hp hb
    have hbw : T.dist b w≤L := hw.2
    have hj : j ≤ i+L := by
      have h := hT.connected.dist_triangle (u := x) (v := b) (w := w)
      rw [hdw,hdb] at h
      omega
    have hi : i ≤ j+L := by
      have h := hT.connected.dist_triangle (u := x) (v := w) (w := b)
      rw [hdw,hdb,T.dist_comm (u := w) (v := b)] at h
      omega
    apply Finset.mem_image.mpr
    refine ⟨j,?_,SimpleGraph.Walk.getVert_support_idxOf p hw.1⟩
    exact Finset.mem_Icc.mpr ⟨by omega,hj⟩
  calc
    {w | w∈p.support ∧ T.dist b w≤L}.ncard ≤ (C.image p.getVert).card := by
      exact_mod_cast Set.ncard_le_ncard hsubset (Finset.finite_toSet _)
    _ ≤ C.card := Finset.card_image_le
    _ ≤ 2*L+1 := by
      dsimp only [C]
      rw [Nat.card_Icc]
      omega

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
