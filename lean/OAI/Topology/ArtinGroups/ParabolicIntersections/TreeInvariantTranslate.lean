import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeConvex

namespace OAI

/-! Equivariance of invariant vertex sets under subgroup conjugation. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]

lemma conjugate_preserves_image (P : Subgroup G) (U : Set V)
    (hU : ∀ p∈P,∀ x∈U,p • x∈U) (a : G)
    {g : G} (hg : g∈conjugate a P) {y : V} (hy : y∈(a • ·) '' U) :
    g • y∈(a • ·) '' U := by
  obtain ⟨x,hx,rfl⟩ := hy
  refine ⟨(a⁻¹*g*a) • x,hU _ ((mem_conjugate a P g).mp hg) _ hx,?_⟩
  simp only [smul_smul,mul_assoc,mul_inv_cancel_left]

lemma not_mem_image_of_smul_eq {U : Set V} {a : G} {x y : V}
    (hx : x∉U) (he : a • x=y) : y∉(a • ·) '' U := by
  rintro ⟨z,hz,h⟩
  have heq : z=x := (MulAction.toPerm a).injective (h.trans he.symm)
  exact hx (heq ▸ hz)

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
