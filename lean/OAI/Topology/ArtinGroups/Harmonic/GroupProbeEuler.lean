import Mathlib
import OAI.Topology.ArtinGroups.Realizations.FrameFamilyWeightedLevel
import OAI.Topology.ArtinGroups.Geometry.ConvexHullSupportedComp
import OAI.Topology.ArtinGroups.Geometry.ProbeConvexEuler
import OAI.Topology.ArtinGroups.Harmonic.ProbeActionLevelExterior

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "R" => probeQuiver Q
local notation "aw" => sourceArtinAction M (K:=ℂ)
local notation "bw" => sourceProbeAction M (K:=ℂ)
local notation "C" => fusionFoldedCartan m d

theorem sourceGroup_probe_euler
    (J T:Set S) (hJ:IsSpherical M J) (z g:Artin M) (hg:g∈artinParabolic M T)
    (q:ℤ) (p:S⊕Unit→ℝ)
    (hz:∀H,ClassCapOn Q (sourceFrameFamily M z H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀v,v∉Sum.inl '' J→sourceMultiplicity M z q v=p v)
    (huniv:∀a∈artinParabolic M J,
      (∀H,ClassCapOn Q (sourceFrameFamily M (a*z) H)
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀j:J,p (.inl (j:S))≤ sourceMultiplicity M (a*z) q (.inl (j:S)))
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ)
    (hsoc:∀j:J,∀L c,coefficientSocle R
      ((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
        (minimalClassModel_minimal R _) l) (.inl (.inl (j:S),L)) c=⊥) :
    let N:=((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l);
    (if l=0 then fusionWeight m α.2*p α.1 else 0)-
      (fun β=>generatorVector R N (.inl β)) ⬝ᵥ fusionFold m (C *ᵥ p) ≤
      fusionWeight m α.2*sourceMultiplicity M (g*z) (q-l) α.1 := by
  obtain ⟨w,rfl⟩:=sourceSignedWord_surjective M z
  have hc:=source_convex_subobjects_full M J hJ (sourcePacketWord w) (.inr ()) q p
    (by simpa only [sourceFrameFamily_word] using hz) hp
    (by simpa only [sourceMultiplicity_word,sourcePacketMultiplicity] using hext)
    (by
      intro a ha hcap j
      have family_eq : sourceFrameFamily M (a*sourceSignedWord M w)=
          (fun L=>aw a (fusionPacketOrbit m d hd hdiag (sourcePacketWord w) (.inr ()) L)) := by
        funext label
        rw [sourceFrameFamily_mul,sourceFrameFamily_word]
      have translated_cap : ∀ label,
          ClassCapOn Q (sourceFrameFamily M (a*sourceSignedWord M w) label)
            (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q := by
        simpa only [family_eq] using hcap
      simpa only [sourceMultiplicity,family_eq] using huniv a ha translated_cap j)
  have hh:=sourceProbe_convex_euler M J hJ (sourcePacketWord w) (.inr ()) q p hc g α b l hsoc
  have hcart:=sourceProbeOrbit_cartan M (K:=ℂ) T g⁻¹ ((artinParabolic M T).inv_mem hg) α b l p
  dsimp only at hh hcart ⊢
  rw [hcart,neg_sub] at hh
  have hw:=sourceFrameFamily_weighted_level M (g*sourceSignedWord M w) (q-l) α
  simp only [sourceFrameFamily_mul,sourceFrameFamily_word] at hw
  exact hh.trans_eq hw

end HarmonicArtin

end OAI
