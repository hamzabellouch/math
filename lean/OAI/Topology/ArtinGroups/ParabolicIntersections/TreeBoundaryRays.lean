import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeTranslationSegment
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeShortcutMetric
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeShortcutHyperbolic

namespace OAI

/-! Distinct directions of tree rays determine distinct shortcut-boundary points. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T H : SimpleGraph V)

lemma separated_graphProduct (hT : T.IsTree) (hH : H.Connected) (hS : PathSaturated T H)
    {x a b : V} (p : T.Walk x a) (q : T.Walk x b) (hp : p.IsPath) (hq : q.IsPath)
    (hsep : p.Nil ∨ q.Nil ∨ p.snd≠q.snd) : graphProduct H x a b ≤ 1/2 := by
  rcases hsep with hn|hn|hne
  · cases hn
    unfold graphProduct
    rw [SimpleGraph.dist_self]
    simp
  · cases hn
    unfold graphProduct
    rw [SimpleGraph.dist_self,H.dist_comm (u := a) (v := x)]
    simp
  · have hpq := reverse_append_isPath T hT.isAcyclic p q hp hq hne
    have hx : x∈(p.reverse.append q).support :=
      SimpleGraph.Walk.support_subset_support_append_right _ _ q.start_mem_support
    have h := shortcut_dist_split T H hT hH hS (p.reverse.append q) hpq hx
    rw [H.dist_comm (u := a) (v := x)] at h
    have h' : (H.dist x a : ℝ)+H.dist x b ≤ H.dist a b+1 := by exact_mod_cast h
    unfold graphProduct
    linarith

variable (hA : PreservesAdj (G := G) T)

def inverseSegment (g : G) {x : V} (p : T.Walk x (g • x)) : T.Walk x (g⁻¹ • x) :=
  (actPath T hA g⁻¹ p.reverse).copy (by simp) rfl

lemma inverseSegment_isPath (g : G) {x : V} (p : T.Walk x (g • x)) (hp : p.IsPath) :
    (inverseSegment T hA g p).IsPath :=
  (SimpleGraph.Walk.isPath_copy _ _ _).mpr (hp.reverse.map (MulAction.toPerm g⁻¹).injective)

lemma inverseSegment_snd (g : G) {x : V} (p : T.Walk x (g • x)) :
    (inverseSegment T hA g p).snd=g⁻¹ • p.reverse.snd :=
  actPath_copy_snd T hA g⁻¹ p.reverse _ rfl

lemma inverseSegment_reverse_snd (g : G) {x : V} (p : T.Walk x (g • x)) :
    (inverseSegment T hA g p).reverse.snd=g⁻¹ • p.snd := by
  simpa only [inverseSegment,SimpleGraph.Walk.reverse_reverse] using
    actPath_copy_reverse_snd T hA g⁻¹ p.reverse (by simp) rfl

lemma inverseSegment_nonempty (g : G) {x : V} (p : T.Walk x (g • x)) (hpn : ¬p.Nil) :
    ¬(inverseSegment T hA g p).Nil := by
  intro hn
  have hl := hn.length_eq_zero
  simp only [inverseSegment,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map,
    SimpleGraph.Walk.length_reverse] at hl
  exact hpn (SimpleGraph.Walk.length_eq_zero_iff.mp hl)

lemma inverseSegment_turn (g : G) {x : V} (p : T.Walk x (g • x))
    (hturn : p.reverse.snd≠g • p.snd) :
    (inverseSegment T hA g p).reverse.snd≠g⁻¹ • (inverseSegment T hA g p).snd := by
  rw [inverseSegment_reverse_snd,inverseSegment_snd]
  intro he
  have h₁ := congrArg (fun w : V => g • w) he
  simp only [smul_inv_smul] at h₁
  have h₂ := congrArg (fun w : V => g • w) h₁
  simp only [smul_inv_smul] at h₂
  exact hturn h₂.symm

lemma inverseSegment_mem (g a : G) {x w : V} (p : T.Walk x (g • x))
    (hw : a • w∈p.support) : (g⁻¹*a) • w∈(inverseSegment T hA g p).support := by
  simp only [inverseSegment,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map]
  apply List.mem_map.mpr
  refine ⟨a • w,?_,?_⟩
  · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hw
  · exact (mul_smul g⁻¹ a w).symm

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
