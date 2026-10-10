import OAI.Topology.ArtinGroups.ParabolicIntersections.MainIntersection
import OAI.Topology.ArtinGroups.ParabolicIntersections.DynamicsDefinitions

namespace OAI

/-!
# Corollary 1.3 of paper 082-03

The published inputs are Charney--Martin--Morris-Wright,
*Acylindrical hyperbolicity for Artin groups with a visual splitting*,
Algebraic & Geometric Topology 26 (2026), 1507--1528,
Theorem 3.2 and Proposition 4.2; also arXiv:2404.11393, pp. 9, 14.
https://msp.org/agt/2026/26-4/agt-v26-n4-p08-p.pdf
https://arxiv.org/pdf/2404.11393

Their hypotheses concern the edge group of an actual visual splitting.
The required parabolic-intersection premise is proved by `parabolic_intersections`,
rather than postulated as part of these published inputs.
-/
namespace HarmonicArtin.ParabolicIntersections
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- The exact two published implications used by the target corollary. -/
structure PublishedVisualSplitting : Prop where
  edge_criterion : IsIrreducible M → ∀ Y Z : Set S, IsVisualSplit M Y Z →
    (∀ g h : Artin M, IsParabolic M
      (conjugate g (artinParabolic M (Y ∩ Z)) ⊓ conjugate h (artinParabolic M (Y ∩ Z)))) →
    AcylindricallyHyperbolic (Artin M) ∧ WeaklyMalnormal (artinParabolic M (Y ∩ Z))
  proper_criterion : IsIrreducible M → ∀ Y Z : Set S, IsVisualSplit M Y Z →
    WeaklyMalnormal (artinParabolic M (Y ∩ Z)) →
    ∀ P : Subgroup (Artin M), IsParabolic M P → P ≠ ⊤ → WeaklyMalnormal P

local instance : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder

/-- Corollary 1.3 in full: acylindrical hyperbolicity and weak malnormality
of every proper parabolic for every irreducible non-clique Artin matrix. -/
theorem nonclique_dynamics
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hPub : ∀ X : Set S, PublishedSphericalInputs (relativeMatrix M X))
    (hVisual : PublishedVisualSplitting M)
    (hIrred : IsIrreducible M) (hInf : ∃ s t : S, s ≠ t ∧ M s t=0) :
    AcylindricallyHyperbolic (Artin M) ∧
      ∀ P : Subgroup (Artin M), IsParabolic M P → P ≠ ⊤ → WeaklyMalnormal P := by
  obtain ⟨s,t,hst,hlabel⟩ := hInf
  have hsplit := infinite_pair_visual_split M s t hst hlabel
  obtain ⟨hAH,hEdge⟩ := hVisual.edge_criterion hIrred {s}ᶜ {t}ᶜ hsplit (by
    intro g h
    exact parabolic_intersections M hEmb hPub _ _ g h)
  exact ⟨hAH,hVisual.proper_criterion hIrred {s}ᶜ {t}ᶜ hsplit hEdge⟩

end HarmonicArtin.ParabolicIntersections

end OAI
