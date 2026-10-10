import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualAcylindrical
import OAI.Topology.ArtinGroups.ParabolicIntersections.DynamicsMain

namespace OAI

/-!
# Paper 082-03, Corollary 1.3, without published hypotheses

For a finite-rank irreducible Artin group whose defining graph is not a
clique, the group is acylindrically hyperbolic and every proper parabolic
subgroup is weakly malnormal. The acylindrical action is constructed from
the genuine visual tree; the algebraic intersection theorem supplies a
segment with trivial stabilizer. All metric, boundary, and malnormality
arguments are proved in the imported development.
-/
namespace HarmonicArtin.ParabolicIntersections
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- The full third main result of *Parabolic intersections in Artin groups*. -/
theorem unconditional_nonclique_dynamics
    (hIrred : IsIrreducible M) (hInf : ∃ s t : S,s≠t ∧ M s t=0) :
    AcylindricallyHyperbolic (Artin M) ∧
      ∀ P : Subgroup (Artin M),IsParabolic M P → P≠⊤ → WeaklyMalnormal P := by
  constructor
  · obtain ⟨s,t,hst,hm⟩ := hInf
    let : Fact (IsVisualSplit M {s}ᶜ {t}ᶜ) := ⟨infinite_pair_visual_split M s t hst hm⟩
    exact visual_acylindricallyHyperbolic M {s}ᶜ {t}ᶜ hIrred
  · exact unconditional_nonclique_weaklyMalnormal M hIrred hInf

end HarmonicArtin.ParabolicIntersections

end OAI
