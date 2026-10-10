import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Harmonic
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWordLeft

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

omit [Fintype S] [LinearOrder S] in
lemma source_spherical_mono {J T:Set S} (h:J⊆T) (hT:IsSpherical M T) : IsSpherical M J := by
  let :Finite (coxeterParabolic M T):=hT
  have hm:coxeterParabolic M J≤coxeterParabolic M T:=Subgroup.closure_mono (Set.image_mono h)
  exact Finite.of_injective (fun z:coxeterParabolic M J=>(⟨z,hm z.property⟩:coxeterParabolic M T))
    (fun a b h=>Subtype.ext (congrArg (fun z:coxeterParabolic M T => (z:M.Group)) h))

structure SourceCandidate (T J:Set S) (z:Artin M) (q:ℤ) : Prop where
  proper : J⊂T
  cap : ∀H,ClassCapOn Q (sourceFrameFamily M z H) (closedNeighborhood Q (U T) \ U J) q
  negative : ∀s∈T,s∉J→(framedCartan M *ᵥ sourceHarmonicAt M J z q) (.inl s)<0
  representatives : ∀y∈rightCoset M J z,
    (∀H,ClassCapOn Q (sourceFrameFamily M y H) (U T) q)→
      ∀j:J,sourceHarmonicAt M J z q (.inl (j:S))≤ sourceMultiplicity M y q (.inl (j:S))

lemma sourceCandidate_capped (T J:Set S) (hT:IsSpherical M T) (z:Artin M) (q:ℤ)
    (X:SourceCandidate M T J z q) :
    ∃a∈artinParabolic M J,
      SourceCappedCandidate M T J (a*z) q (sourceHarmonicAt M J z q) := by
  have hJ:=source_spherical_mono M X.proper.subset hT
  obtain ⟨a,ha,hcap⟩:=source_finiteFamily_cap_accessible M J hJ (sourceFrameFamily M z) q
    (by intro H i hi; exact X.cap H i ⟨closedNeighborhood_mono Q
      (unfoldedInclusion_range_mono M X.proper.subset) hi.1,hi.2⟩)
  have hc:∀H,ClassCapOn Q (sourceFrameFamily M (a*z) H) (closedNeighborhood Q (U T)) q := by
    intro H
    dsimp only
    rw [unfoldedInclusion_range M T]
    apply source_cap_closed_of_cap_parts M T J X.proper.subset _ q
    · rw [sourceFrameFamily_mul]; exact hcap H
    · rw [sourceFrameFamily_mul]
      apply sourceArtinAction_cap_exterior M J a ha _ _ (fun _ membership=>membership.2) q
      simpa only [unfoldedInclusion_range M T,unfoldedInclusion_range M J] using X.cap H
  have hC : fusionFoldedCartan m (coxeterFusionEdge M) = framedCartan M := by
    convert fusionFoldedCartan_eq_framedCartan M using 1
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨a,ha,X.proper.subset,hJ,hc,?_,?_,?_,?_⟩
  · intro j
    rw [hC]
    exact sourceHarmonicAt_harmonic M J hJ z q ⟨.inl (j:S),⟨j,j.property,rfl⟩⟩
  · intro v hv
    rw [sourceMultiplicity_exterior M J a ha z v hv q,sourceHarmonicAt_outside M J z q v hv]
  · rw [hC]
    exact X.negative
  · intro b hb hbc j
    apply X.representatives (b*(a*z)) _ hbc j
    change b*(a*z)*z⁻¹∈artinParabolic M J
    simpa only [mul_assoc,mul_inv_cancel,mul_one] using (artinParabolic M J).mul_mem hb ha

omit [Fintype S] [LinearOrder S] in
lemma rightCoset_mul_eq (J:Set S) (g z:Artin M) (hg:g∈artinParabolic M J) :
    rightCoset M J (g*z)=rightCoset M J z := by
  ext y
  change y*(g*z)⁻¹∈artinParabolic M J ↔ y*z⁻¹∈artinParabolic M J
  rw [_root_.mul_inv_rev,←mul_assoc]
  exact (artinParabolic M J).mul_mem_cancel_right ((artinParabolic M J).inv_mem hg)

theorem sourceCandidate_unique (T J J':Set S) (hT:IsSpherical M T)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q:ℤ)
    (X:SourceCandidate M T J z q) (Y:SourceCandidate M T J' (h*z) q) :
    J=J' ∧ rightCoset M J z=rightCoset M J' (h*z) := by
  obtain ⟨a,ha,hX⟩:=sourceCandidate_capped M T J hT z q X
  obtain ⟨b,hb,hY⟩:=sourceCandidate_capped M T J' hT (h*z) q Y
  let k:=b*h*a⁻¹
  have hk:k∈artinParabolic M T := (artinParabolic M T).mul_mem
    ((artinParabolic M T).mul_mem (artinParabolic_mono M Y.proper.subset hb) hh)
    ((artinParabolic M T).inv_mem (artinParabolic_mono M X.proper.subset ha))
  have he:k*(a*z)=b*(h*z) := by dsimp [k]; group
  have hY':SourceCappedCandidate M T J' (k*(a*z)) q (sourceHarmonicAt M J' (h*z) q) := by
    rw [he]; exact hY
  obtain ⟨_,hj,hkJ⟩:=sourceCandidate_comparison_parabolic M T J J' hT (a*z) k hk q _ _ hX hY'
  subst J'
  have heh:h=b⁻¹*k*a := by dsimp [k]; group
  have hhJ:h∈artinParabolic M J := by
    rw [heh]
    exact (artinParabolic M J).mul_mem ((artinParabolic M J).mul_mem
      ((artinParabolic M J).inv_mem hb) hkJ) ha
  exact ⟨rfl,(rightCoset_mul_eq M J h z hhJ).symm⟩

end HarmonicArtin

end OAI
