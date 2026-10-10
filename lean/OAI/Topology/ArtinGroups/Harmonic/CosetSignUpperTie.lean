import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.TieCode
import OAI.Topology.ArtinGroups.Harmonic.SecondaryAsSum
import OAI.Topology.ArtinGroups.Harmonic.IncidentNonnegRowPositive

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceCosetSign_eq_at_upper_tie {P R:Deligne M} (h:P≤R)
    (hv:sourceCosetVector M R (sourceUpperLevel M P R)=sourceCosetVector M P (sourceUpperLevel M P R))
    (i:S⊕Unit) : sourceCosetSign M R (sourceUpperLevel M P R) i=
      sourceCosetSign M P (sourceUpperLevel M P R) i := by
  apply sourceSignAt_congr_above
  intro d hd
  rcases eq_or_lt_of_le hd with rfl|hd
  · exact hv
  · exact sourceCosetVector_eq_above_upper M h hd

theorem sourceUpper_inactive_later {P R:Deligne M} (h:P<R)
    (ha:∀i∈R.val.1,i∉P.val.1→i∉sourceActive M P) : SourceEarlier M P R := by
  apply (sourceEarlier_iff_of_comparable M (Or.inl h)).mpr
  apply (sourceHeight_lt_iff M P R).mpr
  refine ⟨sourceUpperLevel M P R,fun d hd=>(sourceBlock_eq_above_upper M h.le hd).symm,?_⟩
  let H:=sourceUpperLevel M P R
  by_cases hv:sourceCosetVector M R H=sourceCosetVector M P H
  · have hr(i:S)(hi:i∈R.val.1):(framedCartan M *ᵥ sourceCosetVector M P H) (.inl i)=0:=by
      rw [←hv]
      exact sourceCosetVector_harmonic M R H ⟨.inl i,⟨i,hi,rfl⟩⟩
    have hs(i:S)(hi:i∈R.val.1)(ht:i∉P.val.1):0≤ sourceCosetSign M P H (.inl i):=by
      rcases eq_or_lt_of_le (sourceIncidence_le_upperLevel M P R i hi ht) with he|he
      · have hh:=source_inactive_sign M P i ht (ha i hi ht)
          (by rw [he]; exact hr i hi)
        rw [he] at hh
        rw [hh]; norm_num
      · rw [(source_no_incidence M he).2.2]
    have hp:0<∑i∈(R.val.1.toFinset \ P.val.1.toFinset),sourceCosetSign M P H (.inl i):=by
      apply Finset.sum_pos'
      · intro i hi
        have ht:=Finset.mem_sdiff.mp hi
        exact hs i (Set.mem_toFinset.mp ht.1) (fun hi=>ht.2 (Set.mem_toFinset.mpr hi))
      · obtain ⟨i,hi,ht,he⟩:=sourceUpperLevel_attained M h
        refine ⟨i,by simp [hi,ht],?_⟩
        have hh:=source_inactive_sign M P i ht (ha i hi ht)
          (by rw [he]; exact hr i hi)
        rw [he] at hh
        rw [hh]; norm_num
    apply sourceBlock_lt_of_secondary_lt M hv.symm
    rw [sourceSecondary_upper_change M h.le H (sourceCosetSign_eq_at_upper_tie M h.le hv)]
    exact lt_add_of_pos_right _ hp
  · apply sourceBlock_lt_of_sum_lt
    exact harmonic_sum_lt_of_lt _ _
      (sourceCosetVector_upper_monotone M h.le H (source_inactive_top_rows M h.le ha)) (Ne.symm hv)

theorem sourceUpper_earlier_has_active {P R:Deligne M} (h:P<R) (he:SourceEarlier M R P) :
    ∃i,i∈R.val.1 ∧ i∉P.val.1 ∧ i∈sourceActive M P := by
  by_contra hn
  have hl:SourceEarlier M P R:=sourceUpper_inactive_later M h
    (fun i hi ht ha=>hn ⟨i,hi,ht,ha⟩)
  exact lt_asymm hl he

theorem sourceUpper_active_earlier {P R:Deligne M} (h:P<R)
    (ha:∀i∈R.val.1,i∉P.val.1→i∈sourceActive M P) : SourceEarlier M R P := by
  apply (sourceEarlier_iff_of_comparable M (Or.inr h)).mpr
  apply (sourceHeight_lt_iff M R P).mpr
  refine ⟨sourceUpperLevel M P R,fun d hd=>sourceBlock_eq_above_upper M h.le hd,?_⟩
  let H:=sourceUpperLevel M P R
  by_cases hv:sourceCosetVector M R H=sourceCosetVector M P H
  · have hr(i:S)(hi:i∈R.val.1):(framedCartan M *ᵥ sourceCosetVector M P H) (.inl i)=0:=by
      rw [←hv]
      exact sourceCosetVector_harmonic M R H ⟨.inl i,⟨i,hi,rfl⟩⟩
    have hs(i:S)(hi:i∈R.val.1)(ht:i∉P.val.1):sourceCosetSign M P H (.inl i)≤0:=by
      rcases eq_or_lt_of_le (sourceIncidence_le_upperLevel M P R i hi ht) with he|he
      · have hh:=source_active_sign M P i (ha i hi ht) (by rw [he]; exact hr i hi)
        rw [he] at hh
        rw [hh]; norm_num
      · rw [(source_no_incidence M he).2.2]
    have hp:(∑i∈(R.val.1.toFinset \ P.val.1.toFinset),sourceCosetSign M P H (.inl i))<0:=by
      apply Finset.sum_neg'
      · intro i hi
        have ht:=Finset.mem_sdiff.mp hi
        exact hs i (Set.mem_toFinset.mp ht.1) (fun hi=>ht.2 (Set.mem_toFinset.mpr hi))
      · obtain ⟨i,hi,ht,he⟩:=sourceUpperLevel_attained M h
        refine ⟨i,by simp [hi,ht],?_⟩
        have hh:=source_active_sign M P i (ha i hi ht) (by rw [he]; exact hr i hi)
        rw [he] at hh
        rw [hh]; norm_num
    apply sourceBlock_lt_of_secondary_lt M hv
    rw [sourceSecondary_upper_change M h.le H (sourceCosetSign_eq_at_upper_tie M h.le hv)]
    exact add_lt_of_neg_right _ hp
  · apply sourceBlock_lt_of_sum_lt
    exact harmonic_sum_lt_of_lt _ _
      (sourceCosetVector_upper_antitone M h.le H (source_active_top_rows M h.le ha)) hv

end HarmonicArtin

end OAI
