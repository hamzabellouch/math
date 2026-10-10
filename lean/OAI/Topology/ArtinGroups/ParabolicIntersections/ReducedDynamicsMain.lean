import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualAmalgamProperties
import OAI.Topology.ArtinGroups.ParabolicIntersections.DynamicsEquivalence

namespace OAI

/-!
# The remaining published geometric inputs

The Artin-specific edge-intersection argument of CMMW Theorem 3.2 is now
proved locally. The following statements isolate the still-undischarged
inputs: the general amalgam criterion (Minasyan--Osin, *Acylindrical
hyperbolicity of groups acting on trees*, 2015, Corollary 2.2; stated as
CMMW 2026, Theorem 3.1), and CMMW 2026, Proposition 4.2.

The first is stated for an arbitrary group explicitly isomorphic to a
nontrivial amalgam. The second transfers weak malnormality from the edge
group to all proper parabolics. Neither assumes the parabolic intersection
theorem or its new argument. The local proofs supply the actual amalgam,
injectivity, proper inclusions, exclusion of virtually cyclic groups, and
weak malnormality of the edge group.

Sources: https://arxiv.org/abs/1310.6289
https://msp.org/agt/2026/26-4/agt-v26-n4-p08-p.pdf
-/
namespace HarmonicArtin.ParabolicIntersections

/-- Minasyan--Osin's general nontrivial-amalgam criterion, with the
virtually cyclic alternative explicitly excluded. -/
structure PublishedAmalgamCriterion : Prop where
  criterion : ∀ (G : Type) [Group G] (A : Bool → Type) [∀ b, Group (A b)]
    (C : Type) [Group C] (φ : ∀ b, C →* A b) (e : G ≃* Monoid.PushoutI φ),
    (∀ b, Function.Injective (φ b)) → (∀ b, (φ b).range≠⊤) →
    ¬Group.IsVirtuallyCyclic G →
    WeaklyMalnormal ((Monoid.PushoutI.base φ).range.comap e.toMonoidHom) →
    AcylindricallyHyperbolic G

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- CMMW (2026), Proposition 4.2, stated separately from its edge criterion. -/
structure PublishedProperParabolicCriterion : Prop where
  criterion : IsIrreducible M → ∀ Y Z : Set S, IsVisualSplit M Y Z →
    WeaklyMalnormal (artinParabolic M (Y∩Z)) →
    ∀ P : Subgroup (Artin M), IsParabolic M P → P≠⊤ → WeaklyMalnormal P

/-- Every hypothesis in the general amalgam criterion is supplied by
unconditional theorems for the actual Artin visual splitting. -/
theorem visual_acylindricallyHyperbolic_of_amalgam (hMO : PublishedAmalgamCriterion)
    (hIrred : IsIrreducible M) (Y Z : Set S) (hsplit : IsVisualSplit M Y Z) :
    AcylindricallyHyperbolic (Artin M) := by
  let : Fact (IsVisualSplit M Y Z) := ⟨hsplit⟩
  apply hMO.criterion (Artin M) (fun b => artinParabolic M (visualSide Y Z b))
    (artinParabolic M (Y∩Z)) (visualEdgeInclusion M Y Z)
    (visualArtinEquiv M Y Z hsplit)
  · intro b
    exact Subgroup.inclusion_injective _
  · exact visual_edge_inclusion_proper M Y Z
  · exact visual_not_virtuallyCyclic M Y Z
  · change WeaklyMalnormal ((Monoid.PushoutI.base (visualEdgeInclusion M Y Z)).range.comap
      (visualFromArtin M Y Z hsplit))
    rw [visual_edge_comap]
    exact visual_edge_weaklyMalnormal M Y Z hIrred

/-- Reconstruction of the original published input after discharging its
Artin-specific edge criterion. -/
theorem visualSplitting_of_amalgam_and_proper (hMO : PublishedAmalgamCriterion)
    (hProper : PublishedProperParabolicCriterion M) : PublishedVisualSplitting M where
  edge_criterion hIrred Y Z hsplit _ := by
    let : Fact (IsVisualSplit M Y Z) := ⟨hsplit⟩
    exact ⟨visual_acylindricallyHyperbolic_of_amalgam M hMO hIrred Y Z hsplit,
      visual_edge_weaklyMalnormal M Y Z hIrred⟩
  proper_criterion := hProper.criterion

/-- Paper 082-03, Corollary 1.3, with all algebraic and Artin-specific edge
arguments discharged. Only the two identified geometric inputs remain. -/
theorem nonclique_dynamics_of_amalgam_and_proper (hMO : PublishedAmalgamCriterion)
    (hProper : PublishedProperParabolicCriterion M)
    (hIrred : IsIrreducible M) (hInf : ∃ s t : S, s≠t ∧ M s t=0) :
    AcylindricallyHyperbolic (Artin M) ∧
      ∀ P : Subgroup (Artin M), IsParabolic M P → P≠⊤ → WeaklyMalnormal P :=
  nonclique_dynamics_of_visual_splitting M
    (visualSplitting_of_amalgam_and_proper M hMO hProper) hIrred hInf

end HarmonicArtin.ParabolicIntersections

end OAI
