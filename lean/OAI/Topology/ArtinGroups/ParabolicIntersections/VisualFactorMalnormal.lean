import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualEdgeMalnormal

namespace OAI

/-! Weak malnormality for the vertex factors, and hence their parabolics. -/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

omit [LinearOrder S] in
private lemma trivial_pair_endpoint_type (u v : VisualVertex M Y Z) (hne : u≠v)
    (he : pairStabilizer (G := Artin M) u v=⊥) (b : Bool) :
    ∃ w : VisualVertex M Y Z, u≠w ∧ w.1=b ∧ pairStabilizer (G := Artin M) u w=⊥ := by
  by_cases hv : v.1=b
  · exact ⟨v,hne,hv,he⟩
  obtain ⟨p,hp⟩ := (visualGraph_isTree M Y Z).connected.exists_isPath v u
  have hpnot : ¬p.Nil := fun h => hne (hp.nil_iff_eq.mp h).symm
  obtain ⟨a,ha,haw⟩ := visual_branching M Y Z v p.snd (p.adj_snd hpnot)
  have hadj : (visualGraph M Y Z).Adj v (a • p.snd) := by
    have h := visual_preservesAdj M Y Z a (p.adj_snd hpnot)
    rwa [ha] at h
  have hn : u≠a • p.snd := by
    intro hu
    have hmem : a • p.snd∈p.support := hu ▸ p.end_mem_support
    exact haw ((visualGraph_isTree M Y Z).isAcyclic.eq_snd_of_adj_start hp hadj hmem)
  refine ⟨a • p.snd,hn,?_,?_⟩
  · have hne' := hadj.1
    cases hb : b <;> cases hv' : v.1 <;> cases hw : (a • p.snd).1 <;>
      simp_all only [Bool.false_eq_true,Bool.true_eq_false,not_false_eq_true,not_true_eq_false]
  · rw [extended_pair (visualGraph M Y Z) (visualGraph_isTree M Y Z).isAcyclic
      (visual_preservesAdj M Y Z) u v (a • p.snd) p hp hadj haw]
    · exact he
    · rw [he]
      exact bot_le

/-- A nondegenerate segment with trivial stabilizer in either vertex orbit. -/
lemma visual_trivial_pair_distinct_type (hIrred : IsIrreducible M) (b : Bool) :
    ∃ u v : VisualVertex M Y Z, u≠v ∧ u.1=b ∧ v.1=b ∧
      pairStabilizer (G := Artin M) u v=⊥ := by
  obtain ⟨u,v,hne,he⟩ := visual_exists_trivial_pair M Y Z hIrred
  obtain ⟨w,hnw,hw,hew⟩ := trivial_pair_endpoint_type M Y Z u v hne he b
  have he' : pairStabilizer (G := Artin M) w u=⊥ := by
    simpa only [pairStabilizer,inf_comm] using hew
  obtain ⟨x,hnx,hx,hex⟩ := trivial_pair_endpoint_type M Y Z w u hnw.symm he' b
  exact ⟨w,x,hnx,hw,hx,hex⟩

/-- Both endpoints may be taken in either vertex orbit. -/
lemma visual_trivial_pair_type (hIrred : IsIrreducible M) (b : Bool) :
    ∃ u v : VisualVertex M Y Z, u.1=b ∧ v.1=b ∧
      pairStabilizer (G := Artin M) u v=⊥ := by
  obtain ⟨u,v,hne,he⟩ := visual_exists_trivial_pair M Y Z hIrred
  obtain ⟨w,hnw,hw,hew⟩ := trivial_pair_endpoint_type M Y Z u v hne he b
  have he' : pairStabilizer (G := Artin M) w u=⊥ := by
    simpa only [pairStabilizer,inf_comm] using hew
  obtain ⟨x,_,hx,hex⟩ := trivial_pair_endpoint_type M Y Z w u hnw.symm he' b
  exact ⟨w,x,hw,hx,hex⟩

/-- Each vertex factor of a visual splitting is weakly malnormal. -/
theorem visual_factor_weaklyMalnormal (hIrred : IsIrreducible M) (b : Bool) :
    WeaklyMalnormal (artinParabolic M (visualSide Y Z b)) := by
  obtain ⟨u,v,hu,hv,he⟩ := visual_trivial_pair_type M Y Z hIrred b
  obtain ⟨i,g,hg⟩ := visual_vertex_exists M Y Z u
  obtain ⟨j,h,hh⟩ := visual_vertex_exists M Y Z v
  have hi : i=b := by simpa only [hg,visualVertex,AmalgamTree.vertex] using hu
  have hj : j=b := by simpa only [hh,visualVertex,AmalgamTree.vertex] using hv
  change MulAction.stabilizer (Artin M) u ⊓ MulAction.stabilizer (Artin M) v=⊥ at he
  rw [hg,hh,visual_vertex_stabilizer,visual_vertex_stabilizer,hi,hj] at he
  exact weaklyMalnormal_of_conjugates_inf_bot _ g h he

/-- Any parabolic lying in a vertex factor inherits its weak malnormality. -/
theorem visual_subgroup_weaklyMalnormal (hIrred : IsIrreducible M)
    (b : Bool) (P : Subgroup (Artin M)) (hP : P≤artinParabolic M (visualSide Y Z b)) :
    WeaklyMalnormal P :=
  (visual_factor_weaklyMalnormal M Y Z hIrred b).mono hP

end HarmonicArtin.ParabolicIntersections

end OAI
