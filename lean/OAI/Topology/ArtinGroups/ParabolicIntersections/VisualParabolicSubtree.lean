import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeConvex
import OAI.Topology.ArtinGroups.ParabolicIntersections.ParabolicProductProper
import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualTreeProperties

namespace OAI

/-! Every proper standard parabolic preserves a proper convex subtree. -/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance visualParabolicSubtreeAction : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

noncomputable def parabolicSubtree (X : Set S) : Set (VisualVertex M Y Z) :=
  orbitVertices (artinParabolic M X) (visualVertex M Y Z hSplit.out false 1)
    (visualVertex M Y Z hSplit.out true 1)

omit [Fintype S] in
lemma parabolicSubtree_generators (X : Set S) :
    ∀ a∈generator M '' X,
      a • visualVertex M Y Z hSplit.out false 1=visualVertex M Y Z hSplit.out false 1 ∨
      a • visualVertex M Y Z hSplit.out true 1=visualVertex M Y Z hSplit.out true 1 := by
  rintro a ⟨s,_,rfl⟩
  have hs : s∈Y ∪ Z := hSplit.out.1.symm ▸ Set.mem_univ s
  rcases hs with hs|hs
  · left
    apply (MulAction.mem_stabilizer_iff).mp
    rw [visual_vertex_stabilizer,conjugate_one]
    exact Subgroup.subset_closure ⟨s,hs,rfl⟩
  · right
    apply (MulAction.mem_stabilizer_iff).mp
    rw [visual_vertex_stabilizer,conjugate_one]
    exact Subgroup.subset_closure ⟨s,hs,rfl⟩

omit [Fintype S] in
lemma parabolicSubtree_pathClosed (X : Set S) :
    PathClosed (visualGraph M Y Z) (parabolicSubtree M Y Z X) :=
  orbit_pathClosed (visualGraph M Y Z) (visualGraph_isTree M Y Z).isAcyclic
    (visual_preservesAdj M Y Z) _ _ _ (visual_vertex_adj M Y Z 1) rfl
    (parabolicSubtree_generators M Y Z X)

omit [Fintype S] in
lemma parabolicSubtree_invariant (X : Set S) {p : Artin M} (hp : p∈artinParabolic M X)
    {w : VisualVertex M Y Z} (hw : w∈parabolicSubtree M Y Z X) :
    p • w∈parabolicSubtree M Y Z X := orbit_smul_mem hp hw

lemma parabolicSubtree_proper (hIrred : IsIrreducible M) (X : Set S)
    (hX : X≠Set.univ) : ∃ w : VisualVertex M Y Z,w∉parabolicSubtree M Y Z X := by
  obtain ⟨g,hg⟩ := artin_parabolic_product_proper M hIrred X Y hX
    (Set.ssubset_iff_subset_ne.mp hSplit.out.2.1).2
  refine ⟨visualVertex M Y Z hSplit.out false g,?_⟩
  rintro ⟨p,hp,he|he⟩
  · have heq : g • visualVertex M Y Z hSplit.out false 1=
        p • visualVertex M Y Z hSplit.out false 1 := by
      simpa only [visual_smul_vertex,mul_one] using he
    have ha : p⁻¹*g∈MulAction.stabilizer (Artin M) (visualVertex M Y Z hSplit.out false 1) := by
      change (p⁻¹*g) • visualVertex M Y Z hSplit.out false 1=_
      rw [mul_smul,heq,inv_smul_smul]
    rw [visual_vertex_stabilizer,conjugate_one] at ha
    exact hg p hp (p⁻¹*g) ha (by group)
  · have h := congrArg (fun w : VisualVertex M Y Z => w.1) he
    exact Bool.false_ne_true h

lemma parabolicSubtree_boundary (hIrred : IsIrreducible M) (X : Set S)
    (hX : X≠Set.univ) : ∃ u v : VisualVertex M Y Z,
    (visualGraph M Y Z).Adj u v ∧ u∈parabolicSubtree M Y Z X ∧
      v∉parabolicSubtree M Y Z X := by
  obtain ⟨w,hw⟩ := parabolicSubtree_proper M Y Z hIrred X hX
  let u := visualVertex M Y Z hSplit.out false 1
  have hu : u∈parabolicSubtree M Y Z X :=
    ⟨1,Subgroup.one_mem _,Or.inl (one_smul _ _).symm⟩
  obtain ⟨p,_⟩ := (visualGraph_isTree M Y Z).connected.exists_isPath u w
  exact exists_boundary_edge (visualGraph M Y Z) hu hw p

end HarmonicArtin.ParabolicIntersections

end OAI
