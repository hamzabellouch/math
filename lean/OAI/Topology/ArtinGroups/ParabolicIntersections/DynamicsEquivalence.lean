import OAI.Topology.ArtinGroups.ParabolicIntersections.DynamicsDefinitions

namespace OAI

/-! Transport of the metric definition of acylindrical hyperbolicity. -/
namespace HarmonicArtin.ParabolicIntersections
variable {G H : Type} [Group G] [Group H]

/-- A group isomorphism transports the action, its uniform acylindricity
bounds, and all three distinct orbit limit points. -/
theorem AcylindricallyHyperbolic.of_equiv (e : G ≃* H) (h : AcylindricallyHyperbolic H) :
    AcylindricallyHyperbolic G := by
  obtain ⟨X,d,a,hgeo,hhyp,hiso,hacyl,hlim⟩ := h
  let : MetricSpace X := d
  let : MulAction H X := a
  let : MulAction G X := MulAction.compHom X e.toMonoidHom
  refine ⟨X,d,inferInstance,hgeo,hhyp,fun g => hiso (e g),?_,?_⟩
  · intro ε hε
    obtain ⟨R,N,hRN⟩ := hacyl ε hε
    refine ⟨R,N,?_⟩
    intro x y hxy
    obtain ⟨hfin,hcard⟩ := hRN x y hxy
    let Q : Set H := {h | dist x (h • x)≤ε ∧ dist y (h • y)≤ε}
    change (e ⁻¹' Q).Finite ∧ (e ⁻¹' Q).ncard≤N
    refine ⟨hfin.preimage e.injective.injOn,?_⟩
    rw [Set.ncard_preimage_of_injective_subset_range e.injective
      (by rw [e.surjective.range_eq]; exact Set.subset_univ _)]
    exact hcard
  · obtain ⟨o,u,hu,hB⟩ := hlim
    refine ⟨o,fun i n => e.symm (u i n),?_,?_⟩
    · intro i
      change IsGromovSequence o (fun n => e (e.symm (u i n)) • o)
      simpa only [MulEquiv.apply_symm_apply] using hu i
    · intro i j hij
      obtain ⟨B,hB⟩ := hB i j hij
      refine ⟨B,?_⟩
      intro m n
      change gromovProduct o (e (e.symm (u i m)) • o) (e (e.symm (u j n)) • o)≤B
      simpa only [MulEquiv.apply_symm_apply] using hB m n

end HarmonicArtin.ParabolicIntersections

end OAI
