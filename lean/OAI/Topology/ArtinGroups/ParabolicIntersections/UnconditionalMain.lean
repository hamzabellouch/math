import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshMain
import OAI.Topology.ArtinGroups.ParabolicIntersections.SphericalMesh

namespace OAI

/-!
# Unconditional parabolic intersections and closure

The spherical mesh input is proved by weighted path contractions and finite
Jones--Wenzl projections. Together with the proved standard embeddings,
folding, and acyclic evaluation, this discharges every input to Theorem 1.1
and Corollary 1.2 of paper 082-03. The dynamical corollary below still names
its separate published geometric input explicitly.
-/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- The full spherical mesh input, without hypotheses from the literature. -/
theorem spherical_mesh_input : PublishedMeshInput M :=
  fun Y hY => spherical_mesh_nilpotent M Y hY

local instance : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder

/-- The stronger inside-parabolic form used in the rank arguments. -/
theorem unconditional_inside_intersection : InsideIntersectionProperty M :=
  inside_intersection M (relative_embedding_input M)
    (fun X => ((spherical_mesh_input (relativeMatrix M X)).withAlgebra _).withAcyclic _)

/-- Paper 082-03, Theorem 1.1, with every published input discharged. -/
theorem unconditional_parabolic_intersections
    (X Y : Set S) (g h : Artin M) :
    ∃ (Z : Set S) (k : Artin M),
      conjugate g (artinParabolic M X) ⊓ conjugate h (artinParabolic M Y) =
        conjugate k (artinParabolic M Z) :=
  parabolic_intersections_of_mesh M (fun X => spherical_mesh_input (relativeMatrix M X)) X Y g h

/-- Paper 082-03, Corollary 1.2: arbitrary intersections and the rank bound. -/
theorem unconditional_arbitrary_intersections
    (F : Set (Subgroup (Artin M))) (hF : ∀ P ∈ F, IsParabolic M P) :
    (∃ F₀ : Finset (Subgroup (Artin M)),
      (↑F₀ : Set (Subgroup (Artin M))) ⊆ F ∧ F₀.card ≤ Nat.card S ∧
        sInf F = sInf (↑F₀ : Set (Subgroup (Artin M)))) ∧ IsParabolic M (sInf F) :=
  arbitrary_intersections_of_mesh M (fun X => spherical_mesh_input (relativeMatrix M X)) F hF

/-- Paper 082-03, Corollary 1.2: the unique smallest containing parabolic. -/
theorem unconditional_parabolic_closure (E : Set (Artin M)) :
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q :=
  parabolic_closure_of_mesh M (fun X => spherical_mesh_input (relativeMatrix M X)) E

/-- Paper 082-03, Corollary 1.3, conditional only on the geometric criteria
of Charney--Martin--Morris-Wright, Theorem 3.2 and Proposition 4.2. -/
theorem nonclique_dynamics_of_visual_splitting
    (hVisual : PublishedVisualSplitting M)
    (hIrred : IsIrreducible M) (hInf : ∃ s t : S, s ≠ t ∧ M s t=0) :
    AcylindricallyHyperbolic (Artin M) ∧
      ∀ P : Subgroup (Artin M), IsParabolic M P → P ≠ ⊤ → WeaklyMalnormal P :=
  nonclique_dynamics_of_mesh M (fun X => spherical_mesh_input (relativeMatrix M X))
    hVisual hIrred hInf

end HarmonicArtin.ParabolicIntersections

end OAI
