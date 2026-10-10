import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeNullLayer

namespace OAI

/-! The relative null obstruction for actual group elements avoiding the frame. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd diag

/-- Proposition 5.1 of 082-03, expressed using the pointed group orbit.
The avoidance hypothesis is automatic in the relative enlarged diagram. -/
theorem pointed_null_obstruction (I J : Set S) (hI : I.Nonempty) (hf : f ∉ I)
    (hJI : J ⊆ I) (hJ : IsSpherical M J) (x : Artin M)
    (hx : x ∈ artinParabolic M {f}ᶜ) (q : ℤ)
    (c : S ⊕ Unit → ℝ) (hc : ∀ v, 0 ≤ c v)
    (hcSupp : ∀ v, v ∉ Sum.inl '' I → c v = 0)
    (hcPos : ∀ v, v ∈ Sum.inl '' I → 0 < c v)
    (hcNull : ∀ v, v ∈ Sum.inl '' I → (framedCartan M *ᵥ c) v = 0)
    (hE : ∀ L, ClassCapOn Q (pointedFamily M f x L)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' J)) q)
    (hdata : ∀ v, (v ∈ Sum.inl '' I ∧ v ∉ Sum.inl '' J) ∨
      (v ∉ Sum.inl '' I ∧ ∃ u ∈ Sum.inl '' I, framedCartan M v u < 0) →
        pointedMultiplicity M f x q v = c v)
    (huniv : ∀ g ∈ artinParabolic M J,
      (∀ L, ClassCapOn Q (pointedFamily M f (g*x) L)
        (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q) →
      ∀ j : J, c (.inl (j:S)) < pointedMultiplicity M f (g*x) q (.inl (j:S))) : False := by
  obtain ⟨w, hw, rfl⟩ := artinParabolic_signed_word M {f}ᶜ x hx
  have hC : fusionFoldedCartan m d = framedCartan M := by
    convert fusionFoldedCartan_eq_framedCartan M using 1
    congr 1
    exact Subsingleton.elim _ _
  apply relative_null_layer M I J hI hJI hJ (sourcePacketWord w) (.inl f)
    (by rintro ⟨i, hi, he⟩; exact hf (Sum.inl.inj he ▸ hi))
    (by
      intro a ha he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hw b hb (Sum.inl.inj he)) q c hc hcSupp hcPos
    (by simpa only [hC] using hcNull)
    (by simpa only [pointedFamily_word] using hE)
    (by simpa only [pointedMultiplicity_word, hC] using hdata)
  intro g hg hcap j
  have he : pointedFamily M f (g * sourceSignedWord M w) =
      fun L => sourceArtinAction M g (O (sourcePacketWord w) (.inl f) L) := by
    funext L
    rw [pointedFamily_mul, pointedFamily_word]
  have h := huniv g hg (by simpa only [he] using hcap) j
  simpa only [pointedMultiplicity, he] using h

end HarmonicArtin.ParabolicIntersections

end OAI
