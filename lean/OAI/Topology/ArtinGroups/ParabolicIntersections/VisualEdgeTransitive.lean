import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualTree

namespace OAI

/-! Transitivity on oriented edges of the visual Bass--Serre tree. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance visualEdgeTransitiveAction : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

lemma visual_oriented_edge_transitive {x y u v : VisualVertex M Y Z}
    (hxy : (visualGraph M Y Z).Adj x y) (huv : (visualGraph M Y Z).Adj u v)
    (hx : x.1=u.1) : ∃ a : Artin M,a • x=u ∧ a • y=v := by
  obtain ⟨k,hxk,hyk⟩ := visual_adj_representatives M Y Z hxy
  obtain ⟨g,hug,hvg⟩ := visual_adj_representatives M Y Z huv
  have hy : y.1=v.1 := by
    have h : ∀ a b c d : Bool,a≠b → c≠d → a=c → b=d := by decide
    exact h _ _ _ _ hxy.1 huv.1 hx
  refine ⟨g*k⁻¹,?_,?_⟩
  · rw [hxk,visual_smul_vertex,mul_assoc,inv_mul_cancel,mul_one,hx]
    exact hug.symm
  · rw [hyk,visual_smul_vertex,mul_assoc,inv_mul_cancel,mul_one,hy]
    exact hvg.symm

end HarmonicArtin.ParabolicIntersections

end OAI
