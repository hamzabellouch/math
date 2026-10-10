import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualAmalgam
import OAI.Topology.ArtinGroups.ParabolicIntersections.AmalgamAcyclic

namespace OAI

/-! The Bass--Serre tree and stabilizers of an actual visual Artin splitting. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S) (Y Z : Set S)
local notation "φ" => visualEdgeInclusion M Y Z

abbrev VisualVertex := AmalgamTree.Vertex φ
noncomputable abbrev visualGraph := AmalgamTree.graph φ

noncomputable abbrev visualAction (hsplit : IsVisualSplit M Y Z) :
    MulAction (Artin M) (VisualVertex M Y Z) :=
  MulAction.compHom _ (visualFromArtin M Y Z hsplit)

noncomputable def visualVertex (hsplit : IsVisualSplit M Y Z) (b : Bool) (g : Artin M) : VisualVertex M Y Z :=
  AmalgamTree.vertex φ b (visualFromArtin M Y Z hsplit g)

variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

@[simp] lemma visual_smul_vertex (g h : Artin M) (b : Bool) :
    g • visualVertex M Y Z hSplit.out b h=visualVertex M Y Z hSplit.out b (g*h) := by
  change AmalgamTree.vertex φ b (visualFromArtin M Y Z hSplit.out g*visualFromArtin M Y Z hSplit.out h)=_
  rw [←map_mul]
  rfl

lemma visual_factor_comap (b : Bool) :
    (AmalgamTree.Factor φ b).comap (visualFromArtin M Y Z hSplit.out)=
      artinParabolic M (visualSide Y Z b) := by
  ext a
  constructor
  · rintro ⟨x,hx⟩
    have h := congrArg (visualToArtin M Y Z) hx
    rw [visualToArtin_from] at h
    have hx' : visualToArtin M Y Z (Monoid.PushoutI.of b x)=x.val :=
      Monoid.PushoutI.lift_of _ _ _ _
    rw [hx'] at h
    exact h ▸ x.property
  · intro ha
    exact ⟨⟨a,ha⟩,(visualFromArtin_factor M Y Z hSplit.out b ⟨a,ha⟩).symm⟩

lemma conjugate_comap_hom {A B : Type*} [Group A] [Group B]
    (f : A →* B) (g : A) (P : Subgroup B) :
    (conjugate (f g) P).comap f=conjugate g (P.comap f) := by
  ext a
  simp only [Subgroup.mem_comap,mem_conjugate,map_mul,map_inv]

lemma visual_vertex_stabilizer (b : Bool) (g : Artin M) :
    MulAction.stabilizer (Artin M) (visualVertex M Y Z hSplit.out b g)=
      conjugate g (artinParabolic M (visualSide Y Z b)) := by
  change (MulAction.stabilizer (VisualAmalgam M Y Z)
    (AmalgamTree.vertex φ b (visualFromArtin M Y Z hSplit.out g))).comap
      (visualFromArtin M Y Z hSplit.out)=_
  rw [AmalgamTree.vertex_stabilizer,conjugate_comap_hom,visual_factor_comap]

omit hSplit in
lemma visualGraph_isTree : (visualGraph M Y Z).IsTree := by
  apply AmalgamTree.isTree
  intro b
  exact Subgroup.inclusion_injective _

lemma visual_vertex_exists (v : VisualVertex M Y Z) :
    ∃ b g, v=visualVertex M Y Z hSplit.out b g := by
  obtain ⟨b,v⟩ := v
  obtain ⟨g,rfl⟩ := Quotient.exists_rep v
  refine ⟨b,visualToArtin M Y Z g,?_⟩
  unfold visualVertex
  rw [visualFromArtin_to]
  rfl

lemma visual_vertex_isParabolic (v : VisualVertex M Y Z) :
    IsParabolic M (MulAction.stabilizer (Artin M) v) := by
  obtain ⟨b,g,rfl⟩ := visual_vertex_exists M Y Z v
  rw [visual_vertex_stabilizer]
  exact ⟨_,g,rfl⟩

lemma visual_vertex_adj (g : Artin M) :
    (visualGraph M Y Z).Adj (visualVertex M Y Z hSplit.out false g)
      (visualVertex M Y Z hSplit.out true g) := AmalgamTree.vertex_adj φ _

lemma visual_adj_representatives {u v : VisualVertex M Y Z}
    (h : (visualGraph M Y Z).Adj u v) :
    ∃ g : Artin M, u=visualVertex M Y Z hSplit.out u.1 g ∧
      v=visualVertex M Y Z hSplit.out v.1 g := by
  obtain ⟨g,hu,hv⟩ := AmalgamTree.adj_representatives φ h
  refine ⟨visualToArtin M Y Z g,?_,?_⟩ <;>
    unfold visualVertex <;> rw [visualFromArtin_to] <;> assumption

/-- The stabilizers of the endpoints of every edge generate the whole group. -/
lemma visual_adj_stabilizers_generate {u v : VisualVertex M Y Z}
    (h : (visualGraph M Y Z).Adj u v) :
    MulAction.stabilizer (Artin M) u ⊔ MulAction.stabilizer (Artin M) v=⊤ := by
  obtain ⟨g,hu,hv⟩ := visual_adj_representatives M Y Z h
  rw [hu,hv,visual_vertex_stabilizer,visual_vertex_stabilizer,←conjugate_sup]
  have hne : u.1≠v.1 := h.1
  have hsides : visualSide Y Z u.1 ∪ visualSide Y Z v.1=Set.univ := by
    by_cases hu' : u.1=false
    · have hv' : v.1=true := Bool.eq_true_of_not_eq_false (fun hf => hne (hu'.trans hf.symm))
      rw [hu',hv']
      exact hSplit.out.1
    · have hu'' : u.1=true := Bool.eq_true_of_not_eq_false hu'
      have hv' : v.1=false := Bool.eq_false_of_not_eq_true (fun hf => hne (hu''.trans hf.symm))
      rw [hu'',hv',Set.union_comm]
      exact hSplit.out.1
  have he : artinParabolic M (visualSide Y Z u.1) ⊔
      artinParabolic M (visualSide Y Z v.1)=⊤ := by
    rw [←standard_union,hsides,standard_univ]
  rw [he,conjugate_top]

end HarmonicArtin.ParabolicIntersections

end OAI
