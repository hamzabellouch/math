import OAI.Topology.ArtinGroups.ParabolicIntersections.AvoidingBoundaryRays

namespace OAI

/-! A periodic free segment and a third direction give a non-elementary action. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
open GraphRealization
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

lemma graphProduct_smul (H : SimpleGraph V) (hH : H.Connected)
    (hB : PreservesAdj (G := G) H) (g : G) (x y z : V) :
    graphProduct H (g • x) (g • y) (g • z)=graphProduct H x y z := by
  simp only [graphProduct,graph_action_dist H hH hB]

theorem periodic_three_limit_points (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v) (hnadj : ¬T.Adj u v)
    (g : G) {x : V} (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) (a : G)
    (hau : a • u∈p.support) (hav : a • v∈p.support)
    (c : G) (hc : c • x=x) (hc₁ : c • p.snd≠p.snd)
    (hc₂ : c • p.snd≠g⁻¹ • p.reverse.snd) :
    let H := avoidingGraph (G := G) T u v
    let hH := avoidingGraph_connected T u v hT hA hne hnadj
    let hB := avoidingGraph_preservesAdj T u v hA
    let _ := action H hB hH
    HasThreeOrbitLimitPoints G (Space H hH) := by
  let q := inverseSegment T hA g p
  have hq : q.IsPath := inverseSegment_isPath T hA g p hp
  have hqn : ¬q.Nil := inverseSegment_nonempty T hA g p hpn
  have hqt : q.reverse.snd≠g⁻¹ • q.snd := inverseSegment_turn T hA g p hturn
  have hqu : (g⁻¹*a) • u∈q.support := inverseSegment_mem T hA g a p hau
  have hqv : (g⁻¹*a) • v∈q.support := inverseSegment_mem T hA g a p hav
  have hback : q.snd≠p.snd := by
    rw [inverseSegment_snd]
    intro he
    have hh := congrArg (fun w : V => g • w) he
    rw [smul_inv_smul] at hh
    exact hturn hh
  let seq : Fin 3 → ℕ → G := ![fun n => g^n,fun n => (g⁻¹)^n,fun n => c*g^n]
  let P : ∀ i n,T.Walk x (seq i n • x) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro n
      exact periodicPath T hA g p n
    · intro j
      refine Fin.cases ?_ ?_ j
      · intro n
        exact periodicPath T hA g⁻¹ q n
      · intro k
        refine Fin.cases ?_ (fun z => Fin.elim0 z) k
        intro n
        exact (actPath T hA c (periodicPath T hA g p n)).copy hc (mul_smul c (g^n) x).symm
  let d : Fin 3 → V := ![p.snd,q.snd,c • p.snd]
  refine realization_three_rays T u v hT hA hne hnadj x seq P ?_ ?_ d ?_ ?_ ?_
  · intro i n
    fin_cases i
    · exact periodicPath_isPath T hA hT.isAcyclic g p hp hpn hturn n
    · exact periodicPath_isPath T hA hT.isAcyclic g⁻¹ q hq hqn hqt n
    · apply (SimpleGraph.Walk.isPath_copy _ _ _).mpr
      exact (periodicPath_isPath T hA hT.isAcyclic g p hp hpn hturn n).map
        (MulAction.toPerm c).injective
  · intro i
    fin_cases i
    · change (periodicPath T hA g p 0).Nil
      simp [periodicPath]
    · change (periodicPath T hA g⁻¹ q 0).Nil
      simp [periodicPath]
    · change ((actPath T hA c (periodicPath T hA g p 0)).copy hc _).Nil
      apply SimpleGraph.Walk.length_eq_zero_iff.mp
      exact (actPath_copy_length T hA c (periodicPath T hA g p 0) hc _).trans
        ((periodicPath_length T hA g p 0).trans (zero_mul _))
  · intro i j he
    have hc₂' : c • p.snd≠q.snd := by simpa only [q,inverseSegment_snd] using hc₂
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hback (show p.snd=q.snd from he).symm)
    · exact False.elim (hc₁ (show p.snd=c • p.snd from he).symm)
    · exact False.elim (hback (show q.snd=p.snd from he))
    · rfl
    · exact False.elim (hc₂' (show q.snd=c • p.snd from he).symm)
    · exact False.elim (hc₁ (show c • p.snd=p.snd from he))
    · exact False.elim (hc₂' (show c • p.snd=q.snd from he))
    · rfl
  · intro i n hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    fin_cases i
    · exact periodicPath_snd T hA g p hpn k
    · exact periodicPath_snd T hA g⁻¹ q hqn k
    · change ((actPath T hA c (periodicPath T hA g p (k+1))).copy hc _).snd=c • p.snd
      exact (actPath_copy_snd T hA c (periodicPath T hA g p (k+1)) hc _).trans
        (congrArg (fun w : V => c • w) (periodicPath_snd T hA g p hpn k))
  · intro i R
    fin_cases i
    · exact periodic_shortcut_gromov T hA hT u v hfree hne hnadj g p hp hpn hturn a hau hav R
    · exact periodic_shortcut_gromov T hA hT u v hfree hne hnadj g⁻¹ q hq hqn hqt (g⁻¹*a) hqu hqv R
    · obtain ⟨N,hN⟩ := periodic_shortcut_gromov T hA hT u v hfree hne hnadj g p hp hpn hturn a hau hav R
      refine ⟨N,?_⟩
      intro m hm n hn
      change R ≤ graphProduct (avoidingGraph (G := G) T u v) x ((c*g^m) • x) ((c*g^n) • x)
      rw [mul_smul,mul_smul]
      have he := graphProduct_smul _ (avoidingGraph_connected T u v hT hA hne hnadj)
        (avoidingGraph_preservesAdj T u v hA) c x (g^m • x) (g^n • x)
      rw [hc] at he
      rw [he]
      exact hN m hm n hn

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
