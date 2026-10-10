import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FiniteArtinPositiveLeft
import OAI.Topology.ArtinGroups.Harmonic.InitialProbe
import OAI.Topology.ArtinGroups.Harmonic.ProbeFixedDiagonal

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q

lemma probePositiveWord_left_fraction_fixed (T:Set S) (g:Artin M) (a b:List T)
    (he:g=(wordArtin M (a.map Subtype.val))⁻¹*wordArtin M (b.map Subtype.val))
    (x:FiniteHomotopyClass R (K:=K)) (hx:sourceProbeAction M g x=x) :
    probePositiveWord M T a x=probePositiveWord M T b x := by
  have hw:wordArtin M (b.map Subtype.val)=wordArtin M (a.map Subtype.val)*g := by
    rw [he]; group
  unfold probePositiveWord
  rw [hw,map_mul,Equiv.Perm.mul_apply,hx]

theorem sourceProbe_parabolic_detector (T J:Set S) (hT:IsSpherical M T)
    (g:Artin M) (hg:g∈artinParabolic M T)
    (hfix:∀s∈T,s∉J→∀L b,
      sourceProbeAction M (K:=K) g (sourceInitialProbe M s L b)=sourceInitialProbe M s L b) :
    g∈artinParabolic M J := by
  rw [←restrictedArtinHom_range M T] at hg
  obtain ⟨z,hz⟩:=hg
  let :Finite (restrictedMatrix M T).Group:=restricted_finite M T hT
  obtain ⟨a,b,hfrac⟩:=finiteArtin_positive_left_fraction (restrictedMatrix M T) z
  have hgf:g=(wordArtin M (a.map Subtype.val))⁻¹*wordArtin M (b.map Subtype.val) := by
    rw [←hz,hfrac,map_mul,map_inv,restrictedArtinHom_word,restrictedArtinHom_word]
  have he:∀s:T,(s:S)∈T\J→∀L d,
      probePositiveWord M T a (sourceInitialProbe M (K:=K) s L d)=
        probePositiveWord M T b (sourceInitialProbe M s L d) := by
    intro s hs L d
    exact probePositiveWord_left_fraction_fixed M T g a b hgf _ (hfix s s.property hs.2 L d)
  obtain ⟨u,v,hu,hv,heq⟩:=positive_equal_probe_fraction M T hT (T\J) a b he
  have hword (w:List T) (hw:∀s∈w,(s:S)∉T\J) :
      restrictedArtinHom M T (wordArtin (restrictedMatrix M T) w)∈artinParabolic M J := by
    rw [restrictedArtinHom_word]
    apply wordArtin_mem_parabolic M J
    intro s hs
    obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hs
    by_contra hn
    exact hw t ht ⟨t.property,hn⟩
  rw [←hz,hfrac,heq,map_mul,map_inv]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hword u hu)) (hword v hv)

theorem sourceCandidate_comparison_parabolic (T J J':Set S) (hT:IsSpherical M T)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:SourceCappedCandidate M T J z q p) (Y:SourceCappedCandidate M T J' (h*z) q p') :
    p=p' ∧ J=J' ∧ h∈artinParabolic M J := by
  obtain ⟨hp,hj,hfix⟩:=sourceCandidate_fixed_probes M T J J' hT z h hh q p p' X Y
  exact ⟨hp,hj,sourceProbe_parabolic_detector M T J hT h hh hfix⟩

end HarmonicArtin

end OAI
