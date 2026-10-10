import OAI.Topology.ArtinGroups.ParabolicIntersections.NonCliqueDynamics
import OAI.Topology.ArtinGroups.ParabolicIntersections.AcyclicTwist

namespace OAI

/-! Main statements with the acyclic-evaluation input already discharged. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [fS : Fintype S] [oS : LinearOrder S] (M : CoxeterMatrix S)

/-- The two remaining published finite-type algebra inputs. -/
structure PublishedSphericalAlgebraInputs : Prop where
  mesh : ∀ Y : Set S, IsSpherical M Y →
    MeshNilpotent (fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M)
      (coxeterFusionEdge_symm M)) (fusionColorRegion (fusionLabelSize M) (Sum.inl '' Y))
  folding : ∀ (Y : Set S) (hY : IsSpherical M Y), PublishedFoldingGcd M Y hY

theorem PublishedSphericalAlgebraInputs.withAcyclic (h : PublishedSphericalAlgebraInputs M) :
    PublishedSphericalInputs M where
  mesh := h.mesh
  folding := h.folding
  acyclic := acyclic_twist_input _

local instance conditionalSumOrder : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder

/-- Paper 082-03, Theorem 1.1. -/
theorem main_parabolic_intersections
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hAlg : ∀ X : Set S, PublishedSphericalAlgebraInputs (relativeMatrix M X))
    (X Y : Set S) (g h : Artin M) :
    ∃ (Z : Set S) (k : Artin M),
      conjugate g (artinParabolic M X) ⊓ conjugate h (artinParabolic M Y) =
        conjugate k (artinParabolic M Z) :=
  parabolic_intersections M hEmb (fun X => (hAlg X).withAcyclic _) X Y g h

/-- Paper 082-03, Corollary 1.2, including the empty family. -/
theorem main_arbitrary_intersections
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hAlg : ∀ X : Set S, PublishedSphericalAlgebraInputs (relativeMatrix M X))
    (F : Set (Subgroup (Artin M))) (hF : ∀ P ∈ F, IsParabolic M P) :
    (∃ F₀ : Finset (Subgroup (Artin M)),
      (↑F₀ : Set (Subgroup (Artin M))) ⊆ F ∧ F₀.card ≤ Nat.card S ∧
        sInf F = sInf (↑F₀ : Set (Subgroup (Artin M)))) ∧ IsParabolic M (sInf F) :=
  arbitrary_parabolic_intersections M hEmb (fun X => (hAlg X).withAcyclic _) F hF

/-- Paper 082-03, Corollary 1.2, the closure assertion for every subset. -/
theorem main_parabolic_closure
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hAlg : ∀ X : Set S, PublishedSphericalAlgebraInputs (relativeMatrix M X))
    (E : Set (Artin M)) :
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q :=
  parabolic_closure M hEmb (fun X => (hAlg X).withAcyclic _) E

/-- Paper 082-03, Corollary 1.3, both dynamical assertions. -/
theorem main_nonclique_dynamics
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hAlg : ∀ X : Set S, PublishedSphericalAlgebraInputs (relativeMatrix M X))
    (hVisual : PublishedVisualSplitting M)
    (hIrred : IsIrreducible M) (hInf : ∃ s t : S, s ≠ t ∧ M s t=0) :
    AcylindricallyHyperbolic (Artin M) ∧
      ∀ P : Subgroup (Artin M), IsParabolic M P → P ≠ ⊤ → WeaklyMalnormal P :=
  nonclique_dynamics M hEmb (fun X => (hAlg X).withAcyclic _) hVisual hIrred hInf

end HarmonicArtin.ParabolicIntersections

end OAI
