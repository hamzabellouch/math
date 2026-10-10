import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.TieCode
import OAI.Topology.ArtinGroups.Harmonic.Eligible

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceLower_ineligible_later {P Q:Deligne M} (h:Q<P)
    (ha:∀i∈P.val.1,i∉Q.val.1→¬SourceEligible M P Q i) : SourceEarlier M P Q := by
  apply (sourceEarlier_iff_of_comparable M (Or.inr h)).mpr
  apply (sourceHeight_lt_iff M P Q).mpr
  refine ⟨sourceLowerLevel M P Q,fun d hd=>(sourceBlock_eq_above_lower M h.le hd).symm,?_⟩
  let H:=sourceLowerLevel M P Q
  by_cases hv:sourceCosetVector M Q H=sourceCosetVector M P H
  · have hs(i:S)(hi:i∈P.val.1)(hq:i∉Q.val.1):sourceCosetSign M P H (.inl i)≤0:=by
      rcases eq_or_lt_of_le (sourcePeak_le_lowerLevel M P Q i hi hq).1 with he|he
      · rw [source_ineligible_tie_sign M i hi hq (ha i hi hq) he hv]
        norm_num
      · have hz:sourceCosetSign M P H (.inl i)=0:=sourceSignAt_zero M
          (fun d=>sourceCosetVector M P (d:ℤ)) H (.inl i) (sourcePeak_above M P i he)
        rw [hz]
    have hp:(∑i∈P.val.1.toFinset \ Q.val.1.toFinset,sourceCosetSign M P H (.inl i))<0:=by
      apply Finset.sum_neg'
      · intro i hi
        have ht:=Finset.mem_sdiff.mp hi
        exact hs i (Set.mem_toFinset.mp ht.1) (fun hq=>ht.2 (Set.mem_toFinset.mpr hq))
      · obtain ⟨i,hi,hq,he⟩:=sourceLowerLevel_prescribed_at_tie M h hv
        refine ⟨i,by simp [hi,hq],?_⟩
        rw [source_ineligible_tie_sign M i hi hq (ha i hi hq) he hv]
        norm_num
    apply sourceBlock_lt_of_secondary_lt M hv.symm
    have hh:=sourceSecondary_upper_change M h.le H
      (fun i=>(sourceCosetSign_eq_at_lower_tie M h.le hv i).symm)
    have hsign(i:S):sourceCosetSign M Q H (.inl i)=sourceCosetSign M P H (.inl i):=
      sourceCosetSign_eq_at_lower_tie M h.le hv (.inl i)
    simp only [hsign] at hh
    rw [hh]
    exact add_lt_of_neg_right _ hp
  · apply sourceBlock_lt_of_sum_lt
    exact harmonic_sum_lt_of_lt _ _
      (sourceCosetVector_lower_comparison M h.le H (source_ineligible_top_ge M ha)) (Ne.symm hv)

theorem sourceLower_earlier_has_eligible {P Q:Deligne M} (h:Q<P) (he:SourceEarlier M Q P) :
    ∃i,SourceEligible M P Q i := by
  by_contra hn
  have hl:=sourceLower_ineligible_later M h (fun i _ _ hi=>hn ⟨i,hi⟩)
  exact lt_asymm hl he

theorem sourceLower_eligible_earlier {P Q:Deligne M} (h:Q<P)
    (ha:∀i∈P.val.1,i∉Q.val.1→SourceEligible M P Q i) : SourceEarlier M Q P := by
  apply (sourceEarlier_iff_of_comparable M (Or.inl h)).mpr
  apply (sourceHeight_lt_iff M Q P).mpr
  refine ⟨sourceLowerLevel M P Q,fun d hd=>sourceBlock_eq_above_lower M h.le hd,?_⟩
  let H:=sourceLowerLevel M P Q
  by_cases hv:sourceCosetVector M Q H=sourceCosetVector M P H
  · have hs(i:S)(hi:i∈P.val.1)(hq:i∉Q.val.1):0≤ sourceCosetSign M P H (.inl i):=by
      rcases eq_or_lt_of_le (sourcePeak_le_lowerLevel M P Q i hi hq).1 with he|he
      · rw [source_eligible_tie_sign M i (ha i hi hq) he hv]
        norm_num
      · have hz:sourceCosetSign M P H (.inl i)=0:=sourceSignAt_zero M
          (fun d=>sourceCosetVector M P (d:ℤ)) H (.inl i) (sourcePeak_above M P i he)
        rw [hz]
    have hp:0<∑i∈P.val.1.toFinset \ Q.val.1.toFinset,sourceCosetSign M P H (.inl i):=by
      apply Finset.sum_pos'
      · intro i hi
        have ht:=Finset.mem_sdiff.mp hi
        exact hs i (Set.mem_toFinset.mp ht.1) (fun hq=>ht.2 (Set.mem_toFinset.mpr hq))
      · obtain ⟨i,hi,hq,he⟩:=sourceLowerLevel_prescribed_at_tie M h hv
        refine ⟨i,by simp [hi,hq],?_⟩
        rw [source_eligible_tie_sign M i (ha i hi hq) he hv]
        norm_num
    apply sourceBlock_lt_of_secondary_lt M hv
    have hh:=sourceSecondary_upper_change M h.le H
      (fun i=>(sourceCosetSign_eq_at_lower_tie M h.le hv i).symm)
    have hsign(i:S):sourceCosetSign M Q H (.inl i)=sourceCosetSign M P H (.inl i):=
      sourceCosetSign_eq_at_lower_tie M h.le hv (.inl i)
    simp only [hsign] at hh
    rw [hh]
    exact lt_add_of_pos_right _ hp
  · apply sourceBlock_lt_of_sum_lt
    exact harmonic_sum_lt_of_lt _ _
      (sourceCosetVector_lower_comparison_rev M h.le H (source_eligible_top_le M ha)) hv

end HarmonicArtin

end OAI
