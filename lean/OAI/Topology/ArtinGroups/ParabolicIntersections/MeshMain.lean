import OAI.Topology.ArtinGroups.ParabolicIntersections.ReducedInputsMain
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeEmbedding

namespace OAI

/-! Main results after discharging standard embeddings, acyclic twists,
and folding. Only mesh nilpotence and the dynamical criteria remain. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local instance : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder

/-- Paper 082-03, Theorem 1.1, with all inputs except mesh nilpotence discharged. -/
theorem parabolic_intersections_of_mesh
    (hMesh : ∀ X : Set S, PublishedMeshInput (relativeMatrix M X))
    (X Y : Set S) (g h : Artin M) :
    ∃ (Z : Set S) (k : Artin M),
      conjugate g (artinParabolic M X) ⊓ conjugate h (artinParabolic M Y) =
        conjugate k (artinParabolic M Z) :=
  mesh_parabolic_intersections M (relative_embedding_input M) hMesh X Y g h

/-- Paper 082-03, Corollary 1.2, arbitrary intersections. -/
theorem arbitrary_intersections_of_mesh
    (hMesh : ∀ X : Set S, PublishedMeshInput (relativeMatrix M X))
    (F : Set (Subgroup (Artin M))) (hF : ∀ P ∈ F, IsParabolic M P) :
    (∃ F₀ : Finset (Subgroup (Artin M)),
      (↑F₀ : Set (Subgroup (Artin M))) ⊆ F ∧ F₀.card ≤ Nat.card S ∧
        sInf F = sInf (↑F₀ : Set (Subgroup (Artin M)))) ∧ IsParabolic M (sInf F) :=
  mesh_arbitrary_intersections M (relative_embedding_input M) hMesh F hF

/-- Paper 082-03, Corollary 1.2, parabolic closure. -/
theorem parabolic_closure_of_mesh
    (hMesh : ∀ X : Set S, PublishedMeshInput (relativeMatrix M X))
    (E : Set (Artin M)) :
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q :=
  mesh_parabolic_closure M (relative_embedding_input M) hMesh E

/-- Paper 082-03, Corollary 1.3, with only the mesh and dynamics inputs. -/
theorem nonclique_dynamics_of_mesh
    (hMesh : ∀ X : Set S, PublishedMeshInput (relativeMatrix M X))
    (hVisual : PublishedVisualSplitting M)
    (hIrred : IsIrreducible M) (hInf : ∃ s t : S, s ≠ t ∧ M s t=0) :
    AcylindricallyHyperbolic (Artin M) ∧
      ∀ P : Subgroup (Artin M), IsParabolic M P → P ≠ ⊤ → WeaklyMalnormal P :=
  mesh_nonclique_dynamics M (relative_embedding_input M) hMesh hVisual hIrred hInf

end HarmonicArtin.ParabolicIntersections

end OAI
