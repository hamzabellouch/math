import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.IsolatedHarmonicLayer
import OAI.Topology.ArtinGroups.Harmonic.FrameFamily

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

omit [Fintype S] in
lemma sourceFoldedCartan_eq :
    fusionFoldedCartan m (coxeterFusionEdge M)=framedCartan M := by
  convert fusionFoldedCartan_eq_framedCartan M using 1
  congr 1
  exact Subsingleton.elim _ _

theorem sourceGroup_isolated_harmonic_layer (I J:Set S) (hI:I.Nonempty)
    (hJI:J⊆I) (hJ:IsSpherical M J) (x:Artin M) (q:ℤ) (hq:0<q)
    (c:S⊕Unit→ℝ) (hc:∀v,0≤c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀v,v∈Sum.inl '' I→0<c v)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hE:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' J)) q)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→
      sourceMultiplicity M x q v=c v)
    (huniv:∀g∈artinParabolic M J,
      (∀H,ClassCapOn Q (sourceFrameFamily M (g*x) H)
        (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q)→
      ∀j:J,c (.inl (j:S))<sourceMultiplicity M (g*x) q (.inl (j:S))) : False := by
  obtain ⟨w,rfl⟩:=sourceSignedWord_surjective M x
  apply source_isolated_harmonic_layer M I J hI hJI hJ w q hq c hc hcSupp hcPos
  · simpa only [sourceFoldedCartan_eq] using hcNull
  · simpa only [sourceFrameFamily_word] using hE
  · simpa only [sourceFoldedCartan_eq,sourceMultiplicity_word,sourcePacketMultiplicity] using hdata
  · intro g hg hcap j
    have he:sourceFrameFamily M (g*sourceSignedWord M w)=
        (fun H=>sourceArtinAction M g (fusionPacketOrbit m (coxeterFusionEdge M)
          (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (sourcePacketWord w) (.inr ()) H)) := by
      funext H
      rw [sourceFrameFamily_mul,sourceFrameFamily_word]
    have hh:=huniv g hg (by simpa only [he] using hcap) j
    simpa only [sourceMultiplicity,he] using hh

end HarmonicArtin

end OAI
