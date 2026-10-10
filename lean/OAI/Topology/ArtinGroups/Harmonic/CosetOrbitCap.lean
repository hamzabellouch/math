import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CosetOrbit

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
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "aw" => sourceArtinAction M (K:=ℂ)

theorem sourceCosetOrbit_exists_cap (I J:Set S) (hJI:J⊆I) (hJ:IsSpherical M J)
    (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ)
    (hE:∀ L,ClassCapOn Q (O z₀ s L)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' J)) q) :
    ∃ z,SourceCosetOrbit M J z₀ s z ∧
      ∀ L,ClassCapOn Q (O z s L)
        (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q := by
  have hsub:fusionColorRegion (V:=S⊕Unit) m (Sum.inl '' J)⊆fusionColorRegion m (Sum.inl '' I) :=
    fun _ hα=>Set.image_mono hJI hα
  have hb:∀ L,ClassCapOn Q (O z₀ s L)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J)) \
        Set.range (unfoldedInclusion M J)) q := by
    intro L
    apply ClassCapOn.mono Q (hE L)
    rw [unfoldedInclusion_range]
    intro α hα
    exact ⟨closedNeighborhood_mono Q hsub hα.1,hα.2⟩
  obtain ⟨g,hg,hcap⟩:=source_finiteFamily_cap_accessible M J hJ (O z₀ s) q hb
  obtain ⟨w,_,he⟩:=artinParabolic_signed_word M J g hg
  let z:=sourcePacketWord w++z₀
  have hz:SourceCosetOrbit M J z₀ s z := by
    refine ⟨g,hg,fun L=>?_⟩
    rw [← he]
    exact sourcePacketOrbit_signedPrepend M w z₀ s L
  refine ⟨z,hz,fun L=>?_⟩
  apply source_cap_closed_of_cap_parts M I J hJI (O z s L) q
  · have hact:O z s L=aw g (O z₀ s L) := by
      rw [← he]
      exact sourcePacketOrbit_signedPrepend M w z₀ s L
    rw [hact]
    exact hcap L
  · apply sourceCosetOrbit_cap_exterior M J z₀ s z hz _ _ q hE L
    intro α hα
    exact hα.2

end HarmonicArtin

end OAI
