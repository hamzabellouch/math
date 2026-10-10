import OAI.Topology.ArtinGroups.ParabolicIntersections.ReducedDynamicsMain
import OAI.Topology.ArtinGroups.ParabolicIntersections.ProperParabolicMalnormal

namespace OAI

/-!
# Corollary 1.3 with only the general amalgam criterion remaining

The Artin-specific statements of Charney--Martin--Morris-Wright,
Theorem 3.2 and Proposition 4.2, are proved in this development.
The only remaining published input is Minasyan--Osin (2015), Corollary 2.2,
for arbitrary amalgamated products. In particular the weak-malnormality
half of the corollary has no published hypotheses.
-/
namespace HarmonicArtin.ParabolicIntersections
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- The sufficient case of CMMW Proposition 4.2, now proved locally. -/
theorem proper_parabolic_criterion : PublishedProperParabolicCriterion M where
  criterion hIrred Y Z hsplit _ P hP hne := by
    let : Fact (IsVisualSplit M Y Z) := ⟨hsplit⟩
    exact proper_parabolic_weaklyMalnormal M Y Z hIrred P hP hne

/-- The weak-malnormality assertion of paper 082-03, Corollary 1.3,
without any published input. -/
theorem unconditional_nonclique_weaklyMalnormal
    (hIrred : IsIrreducible M) (hInf : ∃ s t : S,s≠t ∧ M s t=0)
    (P : Subgroup (Artin M)) (hP : IsParabolic M P) (hne : P≠⊤) : WeaklyMalnormal P := by
  obtain ⟨s,t,hst,hm⟩ := hInf
  let : Fact (IsVisualSplit M {s}ᶜ {t}ᶜ) := ⟨infinite_pair_visual_split M s t hst hm⟩
  exact proper_parabolic_weaklyMalnormal M {s}ᶜ {t}ᶜ hIrred P hP hne

/-- Paper 082-03, Corollary 1.3, conditional only on the general published
amalgam theorem of Minasyan--Osin, with every Artin-specific input discharged. -/
theorem nonclique_dynamics_of_amalgam
    (hMO : PublishedAmalgamCriterion)
    (hIrred : IsIrreducible M) (hInf : ∃ s t : S,s≠t ∧ M s t=0) :
    AcylindricallyHyperbolic (Artin M) ∧
      ∀ P : Subgroup (Artin M),IsParabolic M P → P≠⊤ → WeaklyMalnormal P :=
  nonclique_dynamics_of_amalgam_and_proper M hMO (proper_parabolic_criterion M) hIrred hInf

end HarmonicArtin.ParabolicIntersections

end OAI
