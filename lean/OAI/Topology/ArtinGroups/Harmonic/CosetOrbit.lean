import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.IsolatedIterationData

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

def SourceCosetOrbit (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (z:List ((S⊕Unit)×Bool)) : Prop :=
  ∃ g∈artinParabolic M J,∀ L,O z s L=aw g (O z₀ s L)

lemma sourceCosetOrbit_self (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit) :
    SourceCosetOrbit M J z₀ s z₀ := by
  exact ⟨1,(artinParabolic M J).one_mem,fun _=>by rw [map_one]; rfl⟩

lemma sourceCosetOrbit_move (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (z:List ((S⊕Unit)×Bool)) (hz:SourceCosetOrbit M J z₀ s z) (j:J) :
    SourceCosetOrbit M J z₀ s ((.inl j,true)::z) := by
  obtain ⟨g,hg,he⟩:=hz
  refine ⟨generator M j*g,(artinParabolic M J).mul_mem
    (Subgroup.subset_closure ⟨j,j.property,rfl⟩) hg,fun L=>?_⟩
  change fusionPacketPerm m d hd hdiag (.inl j) (O z s L)=_
  rw [he,map_mul,sourceArtinAction_generator]
  rfl

lemma sourceCosetOrbit_multiplicity_exterior (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (z:List ((S⊕Unit)×Bool)) (hz:SourceCosetOrbit M J z₀ s z)
    (v:S⊕Unit) (hv:v∉Sum.inl '' J) (k:ℤ) : μ z s k v=μ z₀ s k v := by
  obtain ⟨g,hg,he⟩:=hz
  rw [← fusionFamilyMultiplicity_orbit m d hd hm hdiag z s k,
    ← fusionFamilyMultiplicity_orbit m d hd hm hdiag z₀ s k]
  have hf:(O z s)=(fun L=>aw g (O z₀ s L)):=funext he
  rw [hf]
  exact sourceArtinAction_multiplicity_exterior M J g hg (O z₀ s) v hv k

lemma sourceCosetOrbit_cap_exterior (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (z:List ((S⊕Unit)×Bool)) (hz:SourceCosetOrbit M J z₀ s z)
    (U:Set (FusionVertex (V:=S⊕Unit) m)) (hU:∀ α∈U,α.1∉Sum.inl '' J) (q:ℤ)
    (hc:∀ L,ClassCapOn Q (O z₀ s L) U q) : ∀ L,ClassCapOn Q (O z s L) U q := by
  obtain ⟨g,hg,he⟩:=hz
  intro L
  rw [he]
  exact sourceArtinAction_cap_exterior M J g hg (O z₀ s L) U hU q (hc L)

lemma sourceCosetOrbit_strict (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (q:ℤ) (c:S⊕Unit→ℝ)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (aw g (O z₀ s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>aw g (O z₀ s L)) q (.inl (j:S)))
    (z:List ((S⊕Unit)×Bool)) (hz:SourceCosetOrbit M J z₀ s z) :
    ∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (aw g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>aw g (O z s L)) q (.inl (j:S)) := by
  obtain ⟨a,ha,he⟩:=hz
  intro g hg hc j
  have hf:(fun L=>aw g (O z s L))=(fun L=>aw (g*a) (O z₀ s L)) := by
    funext L
    rw [he,map_mul]
    rfl
  rw [hf]
  apply huniv (g*a) ((artinParabolic M J).mul_mem hg ha) _ j
  intro label
  rw [← congrFun hf label]
  exact hc label

noncomputable def isolatedDataOfCoset (I J:Set S) (hJI:J⊆I) (hJ:IsSpherical M J)
    (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (c:S⊕Unit→ℝ)
    (hc:∀ v,0≤c v) (hcSupp:∀ v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀ v,v∈Sum.inl '' I→0<c v)
    (hcNull:∀ v,v∈Sum.inl '' I→(C *ᵥ c) v=0)
    (hdata:∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→μ z₀ s q v=c v)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (aw g (O z₀ s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>aw g (O z₀ s L)) q (.inl (j:S))) : IsolatedIterationData M where
  I:=I
  J:=J
  hJI:=hJI
  hJ:=hJ
  s:=s
  q:=q
  c:=c
  hc:=hc
  hcSupp:=hcSupp
  hcPos:=hcPos
  hcNull:=hcNull
  valid:=SourceCosetOrbit M J z₀ s
  move:=sourceCosetOrbit_move M J z₀ s
  data:=by
    intro z hz v hv
    have hj:v∉Sum.inl '' J := by
      rcases hv with h|h
      · exact h.2
      · exact fun hj=>h.1 (Set.image_mono hJI hj)
    rw [sourceCosetOrbit_multiplicity_exterior M J z₀ s z hz v hj q]
    exact hdata v hv
  strict:=sourceCosetOrbit_strict M J z₀ s q c huniv

end HarmonicArtin

end OAI
