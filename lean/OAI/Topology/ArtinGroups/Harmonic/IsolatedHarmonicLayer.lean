import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CosetOrbitCap
import OAI.Topology.ArtinGroups.Harmonic.Contradiction

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d
local notation "aw" => sourceArtinAction M (K:=ℂ)

theorem source_isolated_harmonic_layer (I J:Set S) (hI:I.Nonempty)
    (hJI:J⊆I) (hJ:IsSpherical M J) (w:List (S×Bool)) (q:ℤ) (hq:0<q)
    (c:S⊕Unit→ℝ) (hc:∀ v,0≤c v) (hcSupp:∀ v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀ v,v∈Sum.inl '' I→0<c v)
    (hcNull:∀ v,v∈Sum.inl '' I→(C *ᵥ c) v=0)
    (hE:∀ L,ClassCapOn Q (O (sourcePacketWord w) (.inr ()) L)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' J)) q)
    (hdata:∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→
      μ (sourcePacketWord w) (.inr ()) q v=c v)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (aw g (O (sourcePacketWord w) (.inr ()) L))
        (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>aw g (O (sourcePacketWord w) (.inr ()) L)) q (.inl (j:S))) : False := by
  let z₀:=sourcePacketWord w
  have hstrict:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (aw g (O z₀ (.inr ()) L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>aw g (O z₀ (.inr ()) L)) q (.inl (j:S)) := by
    intro g hg hcap
    apply huniv g hg
    intro L
    apply source_cap_closed_of_cap_parts M I J hJI _ q (hcap L)
    exact sourceArtinAction_cap_exterior M J g hg (O z₀ (.inr ()) L) _
      (fun α hα=>hα.2) q (hE L)
  let D:=isolatedDataOfCoset M I J hJI hJ z₀ (.inr ()) q c hc hcSupp hcPos hcNull hdata hstrict
  obtain ⟨z,hz,hcap⟩:=sourceCosetOrbit_exists_cap M I J hJI hJ z₀ (.inr ()) q hE
  apply D.contradiction hI hq _ z hz hcap
  intro z' hz'
  have he:=sourceCosetOrbit_multiplicity_exterior M J z₀ (.inr ()) z' hz'
    (.inr ()) (by rintro ⟨_,_,he⟩; exact Sum.inl_ne_inr he) 0
  exact he.trans (sourcePacket_frame M w)

end HarmonicArtin

end OAI
