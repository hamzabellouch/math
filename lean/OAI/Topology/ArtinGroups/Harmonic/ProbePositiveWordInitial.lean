import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWordAppend
import OAI.Topology.ArtinGroups.Complexes.InitialProbeTestUpper

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q

lemma probePositiveWord_initial_avoiding (T:Set S) (w:List T) (s:S)
    (hw:∀t∈w,(t:S)≠s) (L:FusionLabel m) (b:Bool) :
    probePositiveWord M T w (initialClass R (K:=K) (.inr ((.inl s,L),b)))=
      initialClass R (.inr ((.inl s,L),b)) := by
  rw [probePositiveWord_core_expanded]
  have ho:∀α∈(fusionExpandedWord m w).map (probeCoreInclusion M T),
      OrthogonalVertices R α (.inr ((.inl s,L),b)) := by
    intro α hα
    obtain ⟨⟨t,H⟩,ht,rfl⟩:=List.mem_map.mp hα
    apply probe_core_leaf_orthogonal Q _ b
    intro he
    apply hw t _ (Sum.inl.inj (congrArg Prod.fst he))
    exact fusionExpandedWord_mem m w (t,H) ht
  generalize (fusionExpandedWord m w).map (probeCoreInclusion M T)=v at *
  induction v with
  | nil=>rfl
  | cons α v ih=>
    change classPositiveTwist R α (positiveWordAction R v _)=_
    rw [ih (fun β hβ=>ho β (List.mem_cons_of_mem _ hβ))]
    exact classPositiveTwist_initial_orthogonal R (ho α (by simp))

lemma probePositiveWord_initial_avoiding_subtype (T:Set S) (w:List T) (s:T)
    (hw:s∉w) (L:FusionLabel m) (b:Bool) :
    probePositiveWord M T w (initialClass R (K:=K) (.inr ((.inl s,L),b)))=
      initialClass R (.inr ((.inl s,L),b)) := by
  apply probePositiveWord_initial_avoiding M T w s _ L b
  intro t ht he
  exact hw ((Subtype.ext he : t=s) ▸ ht)

lemma sourceProbePacket_testUpper_reflect (T:Set S) (t:T)
    (x:FiniteHomotopyClass R (K:=K)) (q:ℤ)
    (h:ClassTestUpper R (sourceProbePacket M t x) (Set.range (probeCoreInclusion M T)) q) :
    ClassTestUpper R x (Set.range (probeCoreInclusion M T)) q := by
  rw [sourceProbePacket_as_packet] at h
  exact classPacketPerm_testUpper_reflect R
    (probeQuiver_no_loops Q (fusionQuiver_no_loops m (coxeterFusionEdge M)
      (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M))) _ _
    (Set.range (probeCoreInclusion M T)) (fun H=>⟨(t,H),rfl⟩) x h

lemma probePositiveWord_initial_cap_not_mem (T:Set S) (w:List T) (s:T)
    (L:FusionLabel m) (b:Bool)
    (hc:ClassTestUpper R (probePositiveWord M T w (initialClass R (K:=K) (.inr ((.inl s,L),b))))
      (Set.range (probeCoreInclusion M T)) 1) : s∉w := by
  induction w with
  | nil=>simp
  | cons t w ih=>
    rw [probePositiveWord_cons] at hc
    have hw:s∉w:=ih (sourceProbePacket_testUpper_reflect M T t _ 1 hc)
    have hst:s≠t:=by
      rintro rfl
      rw [probePositiveWord_initial_avoiding_subtype M T w s hw] at hc
      exact initialProbe_top_not_exact Q (K:=K) (.inl s,L) b
        (sourceProbePacket_top_exact_of_cap M T s _ hc L 0)
    simpa only [List.mem_cons,not_or] using And.intro hst hw

lemma probePositiveWord_initial_cap_iff (T:Set S) (w:List T) (s:T)
    (L:FusionLabel m) (b:Bool) :
    ClassTestUpper R (probePositiveWord M T w (initialClass R (K:=K) (.inr ((.inl s,L),b))))
      (Set.range (probeCoreInclusion M T)) 1 ↔ s∉w := by
  constructor
  · exact probePositiveWord_initial_cap_not_mem M T w s L b
  · intro hw
    rw [probePositiveWord_initial_avoiding_subtype M T w s hw]
    exact initialProbe_test_upper Q (K:=K) _ b _ (by rintro _ ⟨α,rfl⟩; exact ⟨_,rfl⟩)

end HarmonicArtin

end OAI
