import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedTypeComponent
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCosetExteriorCap
import OAI.Topology.ArtinGroups.Harmonic.NeighborhoodProject

namespace OAI

/-! Boundary caps for commuting closed components at any integer cutoff. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S) (cutoff:ℤ)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma pointedBlock_boundary_cap (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀i∈B,∀j∈P.val.1\B,M i j=2) (q:ℕ) (hq:∀i∈B,relativePeak M f cutoff P i=q)
    (x:Artin M) (hx:x∈P.val.2) :
    ∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M B))\Set.range (unfoldedInclusion M B)) (cutoff+q) := by
  intro H
  rw [classCapOn_iff_level_zero]
  intro α hα k hk
  have ha:α∈closedNeighborhood Q (fusionColorRegion m (Sum.inl '' B)):=by
    simpa only [unfoldedInclusion_range] using hα.1
  have ho':α∉fusionColorRegion m (Sum.inl '' B):=by simpa only [unfoldedInclusion_range] using hα.2
  have ho:α.1∉Sum.inl '' B:=ho'
  have hv:=sourceNeighborhood_project M (Sum.inl '' B) ha
  have hout:=sourceBlock_boundary_outside M P B hB hc α.1 hv ho
  have hnb:∃i∈B,framedCartan M (.inl i) α.1<0:=by
    rcases hv with hv|⟨u,hu,huv⟩
    · exact (ho hv).elim
    · obtain ⟨i,hi,rfl⟩:=hu
      exact ⟨i,hi,by rwa [framedCartan_symm]⟩
  have hn : 0 ≤ k-cutoff := by omega
  have he : cutoff+((k-cutoff).toNat:ℤ)=k := by rw [Int.toNat_of_nonneg hn];omega
  have hz:=pointedBlock_above_boundary M f cutoff P B hB q hq α.1 hnb (k-cutoff).toNat (by omega)
  change pointedCosetVector M f P (cutoff+(k-cutoff).toNat) α.1=0 at hz
  rw [he,pointedCosetVector_open_at M f P x hx α.1 hout k] at hz
  exact (pointedMultiplicity_zero_iff M f x k α.1).mp hz H α.2

end HarmonicArtin.ParabolicIntersections

end OAI
