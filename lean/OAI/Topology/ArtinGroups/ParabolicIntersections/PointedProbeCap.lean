import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedTop
import OAI.Topology.ArtinGroups.Harmonic.FrameFamilyCapTop
import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PacketTwistRaisedGenerator2
import OAI.Topology.ArtinGroups.Harmonic.MapPacket
import OAI.Topology.ArtinGroups.Harmonic.ProbePacketExterior
import OAI.Topology.ArtinGroups.Harmonic.FrameFamilyTopProportional
import OAI.Topology.ArtinGroups.Functors.TopZeroProbeSocle

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "aw" => sourceArtinAction M (K:=ℂ)
local notation "bw" => sourceProbeAction M (K:=ℂ)

lemma pointedFamily_cap_of_top_zero (T:Set S) (z:Artin M) (q:ℤ)
    (hz:∀H,ClassCapOn Q (pointedFamily M f z H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q)
    (j:S) (hj:j∈T)
    (ht:∀H L c,classLayerTopDimension Q q (.inl j,L) c (pointedFamily M f z H)=0) :
    ∀H,ClassCapOn Q (pointedFamily M f (generator M j*z) H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q := by
  intro H
  rw [pointedFamily_mul,sourceArtinAction_generator]
  exact classPacketPerm_local_cap_of_top_zero Q hn (fun L:FusionLabel m=>(.inl j,L))
    (fusionColor_orthogonal m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (.inl j))
    _ _ (hz H) (fun L=>⟨(⟨j,hj⟩,L),rfl⟩) (ht H)

theorem pointedProbe_socle_cap_move (T J:Set S) (hJT:J⊆T)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q l:ℤ) (hl:l≤0)
    (hz:∀H,ClassCapOn Q (pointedFamily M f z H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q)
    (hzh:∀H,ClassCapOn Q (pointedFamily M f (h*z) H)
      (Set.range (unfoldedInclusion M T)) q)
    (α:FusionVertex (V:=S⊕Unit) m) (ha:α∈Set.range (unfoldedInclusion M T)) (b:Bool)
    (hy:ClassLowerBound R l (bw h⁻¹ (initialClass R (.inr (α,b)))))
    (j:S) (hj:j∈J) (L:FusionLabel m) (c:ℤ)
    (hs:0<classLayerSocleDimension R l (.inl (.inl j,L)) c
      (bw h⁻¹ (initialClass R (.inr (α,b))))) :
    ∀H,ClassCapOn Q (pointedFamily M f (generator M j*z) H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q := by
  apply pointedFamily_cap_of_top_zero M f T z q hz j (hJT hj)
  apply pointedFamily_top_zero_of_label M f z (.inl j) q L
  intro H
  refine top_zero_of_probe_socle Q _ _ (Set.range (unfoldedInclusion M T)) l q hy
    ?_ ?_ ?_ (.inl j,L) c hs
  · exact ClassCapOn.mono Q (hz H) (fun _ ha=>Or.inl ha)
  · exact sourceProbeOrbit_support M T h⁻¹ ((artinParabolic M T).inv_mem hh) α b
  · intro n v hnv
    rw [sourceProbeAction_hom_reading,← pointedFamily_mul]
    apply classGeneratorArray_zero_of_cap Q _ _ q (hzh H) _ ha
    change q<n+(v-1)
    omega

end HarmonicArtin.ParabolicIntersections

end OAI
