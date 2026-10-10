import Mathlib
import OAI.Topology.ArtinGroups.Complexes.ComplexPacketLowerBound
import OAI.Topology.ArtinGroups.Complexes.BottomSocleZero
import OAI.Topology.ArtinGroups.Harmonic.IsolatedBoundaryAbsent
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedInclusionRange
import OAI.Topology.ArtinGroups.Harmonic.FusionOrbitColorSecondary
import OAI.Topology.ArtinGroups.Harmonic.FusionOrbitColorTop
import OAI.Topology.ArtinGroups.Complexes.PacketTwistRaisedGenerator2

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
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d
local notation "T" => fusionPacketPerm m d hd hdiag (K:=ℂ)
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

structure IsolatedIterationData where
  I : Set S
  J : Set S
  hJI : J⊆I
  hJ : IsSpherical M J
  s : S⊕Unit
  q : ℤ
  c : S⊕Unit→ℝ
  hc : ∀ v,0≤c v
  hcSupp : ∀ v,v∉Sum.inl '' I→c v=0
  hcPos : ∀ v,v∈Sum.inl '' I→0<c v
  hcNull : ∀ v,v∈Sum.inl '' I→(C *ᵥ c) v=0
  valid : List ((S⊕Unit)×Bool)→Prop
  move : ∀ z,valid z→∀ j:J,valid ((.inl j,true)::z)
  data : ∀ z,valid z→∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
    (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→μ z s q v=c v
  strict : ∀ z,valid z→∀ g∈artinParabolic M J,
    (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
    ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
      (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))

namespace IsolatedIterationData
variable {M} (D:IsolatedIterationData M)

abbrev region : Set (FusionVertex (V:=S⊕Unit) m) := fusionColorRegion m (Sum.inl '' D.I)
abbrev operated : Set (FusionVertex (V:=S⊕Unit) m) := fusionColorRegion m (Sum.inl '' D.J)
def capped (z:List ((S⊕Unit)×Bool)) : Prop :=
  ∀ L,ClassCapOn Q (O z D.s L) (closedNeighborhood Q D.region) D.q
def openSocle (z:List ((S⊕Unit)×Bool)) (k:ℤ) : Prop :=
  ∀ H,ClassBottomSocleZero Q k D.operated (O z D.s H)

lemma boundary (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) :
    ∀ L i,((Y z D.s L D.q).placement i).color∉colorBoundary Q D.region :=
  source_isolated_boundary_absent M D.I D.J z D.s D.q D.c D.hcSupp (D.data z hz)

noncomputable abbrev fullRegion (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (L:FusionLabel m) :=
  fusionOrbitColorLayer m d hd hdiag z D.s D.q (Sum.inl '' D.I) (D.boundary z hz) L

lemma capJ (z:List ((S⊕Unit)×Bool)) (hc:D.capped z) :
    ∀ L,ClassCapOn Q (O z D.s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M D.J))) D.q := by
  intro L
  apply (hc L).mono
  apply closedNeighborhood_mono
  rw [unfoldedInclusion_range]
  exact fun α hα=>Set.image_mono D.hJI hα

lemma separation (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (k:ℤ) (hs:D.openSocle z k) :
    (∀ v∉Sum.inl '' D.I,(∃ u∈Sum.inl '' D.I,C v u<0)→μ z D.s k v=0) ∧
    (∀ j∈Sum.inl '' D.J,(C *ᵥ μ z D.s k) j=0) ∧
    fusionWeightedHom m d hd (D.fullRegion z hz) (fun H=>Y z D.s H k) (k-D.q)=0 ∧
    fusionWeightedHom m d hd (fun H=>Y z D.s H k) (D.fullRegion z hz) (D.q-k)=0 := by
  apply source_isolated_separation M D.I D.J D.hJI D.hJ z D.s D.q k D.c
    D.hc D.hcSupp D.hcPos D.hcNull (D.data z hz) (D.capJ z hc) (D.strict z hz)
  intro H α hα r
  exact Submodule.finrank_eq_zero.mp (hs H α hα r)

lemma lower_bound_move (z:List ((S⊕Unit)×Bool)) (j:D.J) (b:ℤ)
    (hb:∀ L,ClassLowerBound Q b (O z D.s L)) :
    ∀ L,ClassLowerBound Q b (O ((.inl j,true)::z) D.s L) := by
  intro L
  exact classPacketPerm_lower_bound Q hn (fun H=>(Sum.inl (j:S),H))
    (fusionColor_orthogonal m d hd hdiag (.inl j)) (O z D.s L) (hb L)

lemma socle_below (z:List ((S⊕Unit)×Bool)) (b k:ℤ)
    (hb:∀ L,ClassLowerBound Q b (O z D.s L)) (hk:k<b) : D.openSocle z k := by
  intro H α hα c
  exact classLayerSocleDimension_below Q (O z D.s H) b k (hb H) hk α c

lemma cap_move (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (k:ℤ) (hk:k<D.q) (hp:D.openSocle z (k-1)) (j:D.J)
    (hs:∃ H L c,0<classLayerSocleDimension Q k (.inl j,L) c (O z D.s H)) :
    D.capped ((.inl j,true)::z) := by
  have hrev: fusionWeightedHom m d hd (fun H=>Y z D.s H (k-1))
      (D.fullRegion z hz) (D.q-k+1)=0 := by
    convert (D.separation z hz hc (k-1) hp).2.2.2 using 1
    congr 1
    omega
  have hf:=fusionOrbitColor_Hom_zero_of_previous m d hd hdiag hm z D.s D.q k
    (Sum.inl '' D.I) (D.boundary z hz)
    (fun L=>ClassCapOn.mono Q (hc L) (fun α hα=>Or.inl hα)) hk hrev
  obtain ⟨H,L,c,hs⟩:=hs
  have ht:=fusionOrbitColor_top_zero_of_Hom_zero m d hd hdiag hm z D.s (.inl j) D.q k c
    (Sum.inl '' D.I) ⟨j,D.hJI j.property,rfl⟩ (D.boundary z hz) hs hf
  intro Hout
  exact classPacketPerm_local_cap_of_top_zero Q hn (fun L=>(Sum.inl (j:S),L))
    (fusionColor_orthogonal m d hd hdiag (.inl j)) (O z D.s Hout) D.region (hc Hout)
    (fun L=>⟨j,D.hJI j.property,rfl⟩) (fun L c=>ht L Hout c)

end IsolatedIterationData
end HarmonicArtin

end OAI
