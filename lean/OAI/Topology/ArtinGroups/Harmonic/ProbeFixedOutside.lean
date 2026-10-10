import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWordLeft

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q

lemma sourceProbe_fixed_outside (B:Set S) (g:Artin M) (hg:g∈artinParabolic M B)
    (s:S) (hs:s∉B) (L:FusionLabel m) (b:Bool) :
    sourceProbeAction M (K:=ℂ) g (sourceInitialProbe M s L b)=sourceInitialProbe M s L b := by
  apply probeClass_fixed_of_no_diagonal Q
  · intro n u
    rw [sourceProbeAction_exterior M B g hg _ _ (by
      intro t ht H he
      have hh:t=s:=Sum.inl.inj (congrArg (fun x:FusionVertex (V:=S⊕Unit) m=>x.1) (Sum.inl.inj he))
      exact hs (hh ▸ ht)),sourceProbeInitial_array]
    simp
  · intro n u
    rw [sourceProbeAction_exterior M B g hg _ _ (by intros;exact Sum.inl_ne_inr),sourceProbeInitial_array]
    simp only [GeneratorPlacement.mk.injEq,true_and]
  · rw [sourceProbeAction_homDimension]
    exact initial_homDimension_le_one R
      (probeQuiver_no_loops Q (fusionQuiver_no_loops m (coxeterFusionEdge M)
        (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M))) _ 0 0

theorem sourceParabolic_inter (T B C:Set S) (hT:IsSpherical M T)
    (hB:B⊆T) (_hC:C⊆T) :
    artinParabolic M B ⊓ artinParabolic M C=artinParabolic M (B∩C) := by
  apply le_antisymm
  · intro g hg
    apply sourceProbe_parabolic_detector M (K:=ℂ) T (B∩C) hT g
      (artinParabolic_mono M hB hg.1)
    intro s _ hs L b
    by_cases hb:s∈B
    · exact sourceProbe_fixed_outside M C g hg.2 s (fun hc=>hs ⟨hb,hc⟩) L b
    · exact sourceProbe_fixed_outside M B g hg.1 s hb L b
  · exact le_inf (artinParabolic_mono M Set.inter_subset_left)
      (artinParabolic_mono M Set.inter_subset_right)

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolic_iUnion {J:Type*} (B:J→Set S) :
    artinParabolic M (⋃j,B j)=⨆j,artinParabolic M (B j) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨j,hj⟩:=Set.mem_iUnion.mp hs
    exact (le_iSup (fun j=>artinParabolic M (B j)) j) (Subgroup.subset_closure ⟨s,hj,rfl⟩)
  · exact iSup_le (fun j=>artinParabolic_mono M (Set.subset_iUnion B j))

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolic_empty : artinParabolic M ∅=⊥ := by simp [artinParabolic]

lemma sourceParabolic_independent {J:Type*} (T:Set S) (hT:IsSpherical M T)
    (B:J→Set S) (hb:∀j,B j⊆T) (hd:Pairwise fun i j=>Disjoint (B i) (B j)) :
    iSupIndep (fun j=>artinParabolic M (B j)) := by
  intro i
  rw [←iSup_subtype (f:=fun j:{j //j≠i}=>artinParabolic M (B j))]
  rw [←sourceParabolic_iUnion M (fun j:{j //j≠i}=>B j)]
  rw [disjoint_iff_inf_le,sourceParabolic_inter M T (B i) (⋃j:{j //j≠i},B j) hT (hb i)
    (by intro s hs;obtain ⟨j,hj⟩:=Set.mem_iUnion.mp hs;exact hb j hj)]
  have he:B i∩(⋃j:{j //j≠i},B j)=∅:=by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro s ⟨hs,hj⟩
    obtain ⟨j,hj⟩:=Set.mem_iUnion.mp hj
    exact Set.disjoint_left.mp (hd j.property.symm) hs hj
  rw [he,sourceParabolic_empty]

end HarmonicArtin

end OAI
