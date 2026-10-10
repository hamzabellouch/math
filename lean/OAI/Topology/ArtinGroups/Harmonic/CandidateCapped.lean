import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ProbeRaiseLower

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=ℂ)
local notation "C" => fusionFoldedCartan m d

theorem sourceCandidate_le_capped (T J:Set S) (z h:Artin M) (q:ℤ) (p:S⊕Unit→ℝ)
    (X:SourceCappedCandidate M T J z q p) (hh:h∈artinParabolic M T)
    (hzh:∀H,ClassCapOn Q (sourceFrameFamily M (h*z) H)
      (Set.range (unfoldedInclusion M T)) q) (s:S) (hs:s∈T) :
    p (.inl s)≤ sourceMultiplicity M (h*z) q (.inl s) := by
  let L:=fusionZeroLabel m (fusionLabelSize_ge_two M)
  let α:FusionVertex (V:=S⊕Unit) m:=(.inl s,L)
  obtain ⟨a,ha,hcap,_,hsoc⟩:=sourceProbe_zero_saturation M T J z h q p X hh hzh
    (fun _:Unit=>α) (fun _=>⟨(⟨s,hs⟩,L),rfl⟩) (fun _=>false)
  have haT:=artinParabolic_mono M X.subset ha
  have hg:(h*a⁻¹)∈artinParabolic M T:=
    (artinParabolic M T).mul_mem hh ((artinParabolic M T).inv_mem haT)
  have hei:(h*a⁻¹)⁻¹=a*h⁻¹:=by simp only [_root_.mul_inv_rev,inv_inv]
  have he:(h*a⁻¹)*(a*z)=h*z:=by simp only [_root_.mul_assoc,inv_mul_cancel_left]
  have hu:=(X.move a ha hcap).probe_euler (h*a⁻¹) hg α false 0 (by rw [hei];exact hsoc ())
  have hn:=sourceProbe_core_dot_nonpos M (K:=ℂ) T (h*a⁻¹)⁻¹
    ((artinParabolic M T).inv_mem hg) α false 0 p X.cartan_nonpos
  dsimp only at hu hn
  rw [ite_eq_left rfl,sub_zero,he] at hu
  have hw:fusionWeight m α.2*p α.1≤fusionWeight m α.2*sourceMultiplicity M (h*z) q α.1:=by linarith
  exact (mul_le_mul_iff_right₀ (fusionWeight_pos m (fusionLabelSize_ge_two M) L)).mp hw

end HarmonicArtin

end OAI
