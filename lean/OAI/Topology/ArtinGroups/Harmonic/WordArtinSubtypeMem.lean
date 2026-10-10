import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWord
import OAI.Topology.ArtinGroups.Harmonic.FrameFamilyCapTop

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=ℂ)

omit [Fintype S] [LinearOrder S] in
lemma wordArtin_subtype_mem (J:Set S) (w:List J) :
    wordArtin M (w.map Subtype.val)∈artinParabolic M J :=
  wordArtin_mem_parabolic M J _ (by
    intro s hs
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp hs
    exact j.property)

theorem sourceProbe_cap_saturation {B:Type*}
    (T J:Set S) (hJT:J⊆T) (hJ:IsSpherical M J)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q l:ℤ) (hl:l≤0)
    (hz:∀H,ClassCapOn Q (sourceFrameFamily M z H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q)
    (hzh:∀H,ClassCapOn Q (sourceFrameFamily M (h*z) H)
      (Set.range (unfoldedInclusion M T)) q)
    (α:B→FusionVertex (V:=S⊕Unit) m) (ha:∀r,α r∈Set.range (unfoldedInclusion M T))
    (b:B→Bool)
    (hy:∀r,ClassLowerBound R l (bw h⁻¹ (initialClass R (.inr (α r,b r))))) :
    ∃ a∈artinParabolic M J,
      (∀H,ClassCapOn Q (sourceFrameFamily M (a*z) H)
        (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q) ∧
      (∀r,ClassLowerBound R l (bw (a*h⁻¹) (initialClass R (.inr (α r,b r))))) ∧
      ∀r (j:J) L c,classLayerSocleDimension R l (.inl (.inl j,L)) c
        (bw (a*h⁻¹) (initialClass R (.inr (α r,b r))))=0 := by
  let x:=fun r=>bw h⁻¹ (initialClass R (.inr (α r,b r)))
  let P:List J→Prop:=fun w=>∀H,ClassCapOn Q
    (sourceFrameFamily M (wordArtin M (w.map Subtype.val)*z) H)
    (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q
  have hP:P []:=by simpa only [P,List.map_nil,wordArtin,List.prod_nil,_root_.one_mul] using hz
  have he (w:List J) (r:B) : probePositiveWord M J w (x r)=
      bw (h*(wordArtin M (w.map Subtype.val))⁻¹)⁻¹ (initialClass R (.inr (α r,b r))) := by
    simp only [probePositiveWord,x,mul_inv_rev,inv_inv,map_mul,Equiv.Perm.mul_apply]
  have step:∀w,(restrictedMatrix M J).toCoxeterSystem.IsReduced w→P w→
      ∀j:J,(∃r L c,0<classLayerSocleDimension R l (.inl (.inl j,L)) c
        (probeBottomWord M J l w (x r)))→P (j::w) := by
    intro w _ hp j hs
    obtain ⟨r,L,c,hs⟩:=hs
    rw [probeBottomWord,classLayerSocleDimension_layer,he] at hs
    have hb:=probePositiveWord_lowerBound M J w (x r) l (hy r)
    rw [he] at hb
    have hwT:wordArtin M (w.map Subtype.val)∈artinParabolic M T:=
      artinParabolic_mono M hJT (wordArtin_subtype_mem M J w)
    have hprod:(h*(wordArtin M (w.map Subtype.val))⁻¹)*(wordArtin M (w.map Subtype.val)*z)=h*z:=by
      simp only [_root_.mul_assoc,inv_mul_cancel_left]
    have hm:=sourceProbe_socle_cap_move M T J hJT
      (wordArtin M (w.map Subtype.val)*z) (h*(wordArtin M (w.map Subtype.val))⁻¹)
      ((artinParabolic M T).mul_mem hh ((artinParabolic M T).inv_mem hwT)) q l hl hp
      (by rw [hprod]; exact hzh) (α r) (ha r) (b r) hb j j.property L c hs
    simpa only [P,List.map_cons,wordArtin,List.prod_cons,_root_.mul_assoc] using hm
  obtain ⟨w,_,hp,hs⟩:=probe_family_socle_finite_termination M J hJ l x hy P hP step
  refine ⟨wordArtin M (w.map Subtype.val),wordArtin_subtype_mem M J w,hp,?_,?_⟩
  · intro r
    have hb:=probePositiveWord_lowerBound M J w (x r) l (hy r)
    simpa only [probePositiveWord,x,map_mul,Equiv.Perm.mul_apply] using hb
  · intro r j L c
    have hh:=hs r j L c
    simpa only [probeBottomWord,classLayerSocleDimension_layer,probePositiveWord,x,map_mul,
      Equiv.Perm.mul_apply] using hh

end HarmonicArtin

end OAI
