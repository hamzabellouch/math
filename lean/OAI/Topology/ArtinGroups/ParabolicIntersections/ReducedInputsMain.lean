import OAI.Topology.ArtinGroups.ParabolicIntersections.ConditionalMain
import OAI.Topology.ArtinGroups.ParabolicIntersections.FoldingGcd

namespace OAI

/-! Main results after discharging the acyclic-twist and folding inputs. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- The remaining finite-type input is positive-degree mesh nilpotence. -/
def PublishedMeshInput : Prop :=
  ∀ Y : Set S, IsSpherical M Y →
    MeshNilpotent (fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M)
      (coxeterFusionEdge_symm M)) (fusionColorRegion (fusionLabelSize M) (Sum.inl '' Y))

theorem PublishedMeshInput.withAlgebra (h : PublishedMeshInput M) :
    PublishedSphericalAlgebraInputs M where
  mesh := h
  folding := folding_gcd_input M

local instance : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder

/-- Theorem 1.1 with both the acyclic and folding inputs discharged. -/
theorem mesh_parabolic_intersections
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hMesh : ∀ X : Set S, PublishedMeshInput (relativeMatrix M X))
    (X Y : Set S) (g h : Artin M) :
    ∃ (Z : Set S) (k : Artin M),
      conjugate g (artinParabolic M X) ⊓ conjugate h (artinParabolic M Y) =
        conjugate k (artinParabolic M Z) :=
  main_parabolic_intersections M hEmb (fun X => (hMesh X).withAlgebra _) X Y g h

/-- Corollary 1.2: every intersection is parabolic and is already a finite
intersection of at most the rank many members. -/
theorem mesh_arbitrary_intersections
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hMesh : ∀ X : Set S, PublishedMeshInput (relativeMatrix M X))
    (F : Set (Subgroup (Artin M))) (hF : ∀ P ∈ F, IsParabolic M P) :
    (∃ F₀ : Finset (Subgroup (Artin M)),
      (↑F₀ : Set (Subgroup (Artin M))) ⊆ F ∧ F₀.card ≤ Nat.card S ∧
        sInf F = sInf (↑F₀ : Set (Subgroup (Artin M)))) ∧ IsParabolic M (sInf F) :=
  main_arbitrary_intersections M hEmb (fun X => (hMesh X).withAlgebra _) F hF

/-- Corollary 1.2: every subset has a unique smallest containing parabolic. -/
theorem mesh_parabolic_closure
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hMesh : ∀ X : Set S, PublishedMeshInput (relativeMatrix M X))
    (E : Set (Artin M)) :
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q :=
  main_parabolic_closure M hEmb (fun X => (hMesh X).withAlgebra _) E

/-- Corollary 1.3 with both categorical inputs discharged. -/
theorem mesh_nonclique_dynamics
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hMesh : ∀ X : Set S, PublishedMeshInput (relativeMatrix M X))
    (hVisual : PublishedVisualSplitting M)
    (hIrred : IsIrreducible M) (hInf : ∃ s t : S, s ≠ t ∧ M s t=0) :
    AcylindricallyHyperbolic (Artin M) ∧
      ∀ P : Subgroup (Artin M), IsParabolic M P → P ≠ ⊤ → WeaklyMalnormal P :=
  main_nonclique_dynamics M hEmb (fun X => (hMesh X).withAlgebra _) hVisual hIrred hInf

end HarmonicArtin.ParabolicIntersections

end OAI
