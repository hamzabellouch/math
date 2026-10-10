import OAI.Topology.ArtinGroups.Harmonic.UnfoldedHom
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedInclusion
import OAI.Topology.ArtinGroups.Harmonic.PositivePrefix
import OAI.Topology.ArtinGroups.Complexes.PositiveTopDivisor

namespace OAI

/-!
# Published gcd input for an admissible folding

Castella, *Admissible submonoids of Artin--Tits monoids* (2008),
Proposition 41(2), states that an admissible folding preserves left and
right gcds. Source: https://arxiv.org/pdf/0804.0704, p. 15.
The field below is exactly its common-left-atom consequence: if two
expanded positive words have a common left atom, their original words
have a common left atom. The folding here is the color partition.
Its required Coxeter admissibility is already established by
`unfoldedHom_right_ascent` (constant ascent sign on every color).

The field involves positive words and braid relations only. It contains
no tests, family action, height, stabilizer, or intersection assertion.
-/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

/-- The precise part of published gcd preservation needed below. The
sphericity proof is retained in the type to identify the admissible
finite-type folding to which the source theorem is applied. -/
structure PublishedFoldingGcd (Y : Set S) (_hY : IsSpherical M Y) : Prop where
  common_atom : ∀ (u v : List Y) (α : FusionVertex (V := S⊕Unit) m)
    (r s : List (FusionVertex (V := S⊕Unit) m)),
    PositiveBraidRel Q (fusionExpandedWord m (u.map fun j : Y => (Sum.inl (j:S) : S⊕Unit))) (α::r) →
    PositiveBraidRel Q (fusionExpandedWord m (v.map fun j : Y => (Sum.inl (j:S) : S⊕Unit))) (α::s) →
    ∃ i : Y, PositivePrefix (restrictedMatrix M Y) (positiveGenerator _ i) (wordPositive _ u) ∧
      PositivePrefix (restrictedMatrix M Y) (positiveGenerator _ i) (wordPositive _ v)

/-- The Coxeter admissibility condition is proved, rather than included
as a categorical assumption: all vertices of a color have the same
right-ascent behavior on every element of the folded Coxeter group. -/
theorem unfolded_color_admissible (Y : Set S) (hY : IsSpherical M Y)
    (w : (restrictedMatrix M Y).Group) (i : Y) (L H : FusionLabel m) :
    let N := (unfoldedMatrix M Y).toCoxeterSystem
    N.length (unfoldedHom M Y hY w * N.simple (i,L)) =
        N.length (unfoldedHom M Y hY w)+1 ↔
      N.length (unfoldedHom M Y hY w * N.simple (i,H)) =
        N.length (unfoldedHom M Y hY w)+1 := by
  exact (unfoldedHom_right_ascent M Y hY w (i,L)).trans
    (unfoldedHom_right_ascent M Y hY w (i,H)).symm

end HarmonicArtin.ParabolicIntersections

end OAI
