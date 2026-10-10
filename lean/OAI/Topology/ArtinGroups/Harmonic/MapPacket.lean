import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ArtinAction
import OAI.Topology.ArtinGroups.Harmonic.ProbePacket
import OAI.Topology.ArtinGroups.Functors.HomDimensionFlexible

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "aw" => sourceArtinAction M (K:=K)
local notation "bw" => sourceProbeAction M (K:=K)

lemma classMap_sourcePacket (s:S) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (aw (generator M s) x)=sourceProbePacket M s (classMap Q x) := by
  have h:=classMap_twistProd Q hn (K:=K) (fusionExpandedWord m [Sum.inl s]) x
  erw [fusionExpandedWord_perm m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)] at h
  simpa only [sourceArtinAction_generator,List.map_cons,List.map_nil,
    fusionWordPacketPerm,fusionSignedPacketPerm,ite_true,sourceProbePacket,_root_.mul_one] using h

lemma classMap_sourceArtinAction (g:Artin M) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (aw g x)=bw g (classMap Q x) := by
  let H:Subgroup (Artin M):=
    { carrier:={g|∀x,classMap Q (aw g x)=bw g (classMap Q x)}
      one_mem':=by intro x; simp
      mul_mem':=by
        intro a b ha hb x
        simp only [map_mul,Equiv.Perm.mul_apply]
        exact (ha (aw b x)).trans (congrArg (bw a) (hb x))
      inv_mem':=by
        intro a ha x
        apply (bw a).injective
        have h:=ha (aw a⁻¹ x)
        simpa only [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using h.symm }
  have hg:g∈H:=PresentedGroup.generated_by (braidRelators M) H (by
    intro s
    change ∀x,classMap Q (aw (generator M s) x)=bw (generator M s) (classMap Q x)
    intro x
    rw [sourceProbeAction_generator]
    exact classMap_sourcePacket M s x) g
  exact hg x

lemma sourceProbeAction_homDimension (g:Artin M) (x y:FiniteHomotopyClass R (K:=K)) (n v:ℤ) :
    classHomDimension R n v (bw g x) (bw g y)=classHomDimension R n v x y := by
  let H:Subgroup (Artin M):=
    { carrier:={g|∀x y,classHomDimension R n v (bw g x) (bw g y)=classHomDimension R n v x y}
      one_mem':=by intro x y; simp
      mul_mem':=by
        intro a b ha hb x y
        simp only [map_mul,Equiv.Perm.mul_apply]
        exact (ha (bw b x) (bw b y)).trans (hb x y)
      inv_mem':=by
        intro a ha x y
        have h:=ha (bw a⁻¹ x) (bw a⁻¹ y)
        simpa only [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using h.symm }
  have hg:g∈H:=PresentedGroup.generated_by (braidRelators M) H (by
    intro s
    change ∀x y,classHomDimension R n v (bw (generator M s) x) (bw (generator M s) y)=_
    intro x y
    rw [sourceProbeAction_generator]
    exact twistProd_homDimension Q hn (fusionExpandedWord m [Sum.inl s]) x y n v) g
  exact hg x y

lemma sourceProbeAction_hom_reading (g:Artin M) (x:FiniteHomotopyClass Q (K:=K))
    (α:(S⊕Unit)×FusionLabel m) (b:Bool) (n v:ℤ) :
    classHomDimension R n v (bw g⁻¹ (initialClass R (.inr (α,b)))) (classMap Q x)=
      classGeneratorArray Q (aw g x) ⟨α,n,v-1⟩ := by
  have hd : classHomDimension R n v (initialClass R (.inr (α,b)))
      (classMap Q (aw g x))=classGeneratorArray Q (aw g x) ⟨α,n,v-1⟩ :=
    classHom_dimension_flexible Q (aw g x) α b n v
  rw [← hd,classMap_sourceArtinAction]
  simpa only [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using
    (sourceProbeAction_homDimension M g
      (bw g⁻¹ (initialClass R (.inr (α,b)))) (classMap Q x) n v).symm

end HarmonicArtin

end OAI
