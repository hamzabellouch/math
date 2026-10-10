import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.SecondaryAsSum

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourcePeakSupport (P:Deligne M) (i:S) : Finset ℕ :=
  (sourceCosetProfile M P).support.filter (fun k=>sourceCosetVector M P k (.inl i)≠0)

noncomputable def sourcePeak (P:Deligne M) (i:S) : ℕ :=
  (sourcePeakSupport M P i).sup id

lemma sourcePeakSupport_mem (P:Deligne M) (i:S) (k:ℕ) :
    k∈sourcePeakSupport M P i ↔ sourceCosetVector M P k (.inl i)≠0 := by
  simp only [sourcePeakSupport,Finset.mem_filter,Finsupp.mem_support_iff,sourceCosetProfile_apply]
  constructor
  · exact And.right
  · intro h
    exact ⟨fun he=>h (congrFun he (.inl i)),h⟩

lemma sourcePeak_bound (P:Deligne M) (i:S) (k:ℕ)
    (h:sourceCosetVector M P k (.inl i)≠0) : k≤ sourcePeak M P i :=
  Finset.le_sup (f:=id) ((sourcePeakSupport_mem M P i k).mpr h)

lemma sourcePeak_above (P:Deligne M) (i:S) {k:ℕ} (h:sourcePeak M P i<k) :
    sourceCosetVector M P k (.inl i)=0 := by
  by_contra hn
  exact Nat.not_lt_of_ge (sourcePeak_bound M P i k hn) h

lemma sourcePeak_nonzero (P:Deligne M) (i:S)
    (h:(sourcePeakSupport M P i).Nonempty) :
    sourceCosetVector M P (sourcePeak M P i) (.inl i)≠0 := by
  apply (sourcePeakSupport_mem M P i _).mp
  obtain ⟨k,hk,he⟩:=Finset.exists_mem_eq_sup _ h id
  change (sourcePeakSupport M P i).sup id∈sourcePeakSupport M P i
  rw [he]
  exact hk

lemma sourcePeak_positive (P:Deligne M) (i:S) (hi:i∈P.val.1) :
    0<sourceCosetVector M P (sourcePeak M P i) (.inl i) := by
  have hn:sourceCosetVector M P (sourcePeak M P i) (.inl i)≠0:=
    sourcePeak_nonzero M P i ⟨0,(sourcePeakSupport_mem M P i 0).mpr
      (ne_of_gt (sourceCosetVector_zero_positive M P i hi))⟩
  exact lt_of_le_of_ne (sourceCosetVector_nonneg M P _ _) (Ne.symm hn)

lemma sourcePeak_nonzero_of_pos (P:Deligne M) (i:S) (h:0<sourcePeak M P i) :
    sourceCosetVector M P (sourcePeak M P i) (.inl i)≠0 := by
  apply sourcePeak_nonzero M P i
  by_contra hn
  have he:sourcePeakSupport M P i=∅:=Finset.not_nonempty_iff_eq_empty.mp hn
  simp only [sourcePeak,he,Finset.sup_empty] at h
  exact Nat.not_lt_zero _ h

noncomputable def sourceLowerLevel (P Q:Deligne M) : ℕ :=
  (P.val.1.toFinset \ Q.val.1.toFinset).sup (fun i=>max (sourcePeak M P i) (sourcePeak M Q i))

lemma sourcePeak_le_lowerLevel (P Q:Deligne M) (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1) :
    sourcePeak M P i≤ sourceLowerLevel M P Q ∧ sourcePeak M Q i≤ sourceLowerLevel M P Q := by
  have hh:=Finset.le_sup (f:=fun i=>max (sourcePeak M P i) (sourcePeak M Q i))
    (show i∈P.val.1.toFinset \ Q.val.1.toFinset by simp [hi,hq])
  exact ⟨(le_max_left _ _).trans hh,(le_max_right _ _).trans hh⟩

lemma sourceLowerLevel_attained {P Q:Deligne M} (h:Q<P) :
    ∃i,i∈P.val.1 ∧ i∉Q.val.1 ∧
      (0<sourceCosetVector M P (sourceLowerLevel M P Q) (.inl i) ∨
       0<sourceCosetVector M Q (sourceLowerLevel M P Q) (.inl i)) := by
  obtain ⟨j,hj,hq⟩:=Set.exists_of_ssubset (deligne_lt_type M h)
  have hn:(P.val.1.toFinset \ Q.val.1.toFinset).Nonempty:=⟨j,by simp [hj,hq]⟩
  obtain ⟨i,hi,he⟩:=Finset.exists_mem_eq_sup _ hn
    (fun i=>max (sourcePeak M P i) (sourcePeak M Q i))
  have ha:=Finset.mem_sdiff.mp hi
  have hip:i∈P.val.1:=Set.mem_toFinset.mp ha.1
  have hiq:i∉Q.val.1:=fun hh=>ha.2 (Set.mem_toFinset.mpr hh)
  refine ⟨i,hip,hiq,?_⟩
  by_cases hle:sourcePeak M Q i≤ sourcePeak M P i
  · have hh:sourceLowerLevel M P Q=sourcePeak M P i:=he.trans (max_eq_left hle)
    rw [hh]
    exact Or.inl (sourcePeak_positive M P i hip)
  · have hp:0<sourcePeak M Q i:=(Nat.zero_le _).trans_lt (lt_of_not_ge hle)
    have hh:sourceLowerLevel M P Q=sourcePeak M Q i:=he.trans (max_eq_right (lt_of_not_ge hle).le)
    rw [hh]
    exact Or.inr (lt_of_le_of_ne (sourceCosetVector_nonneg M Q _ _)
      (Ne.symm (sourcePeak_nonzero_of_pos M Q i hp)))

lemma sourceCosetVector_eq_of_lower_open {P Q:Deligne M} (h:Q≤P) (k:ℕ)
    (ho:∀i∈P.val.1,i∉Q.val.1→sourceCosetVector M Q k (.inl i)=sourceCosetVector M P k (.inl i)) :
    sourceCosetVector M Q k=sourceCosetVector M P k := by
  have hext(i:S⊕Unit)(hi:i∉(Sum.inl:S→S⊕Unit) '' Q.val.1):
      sourceCosetVector M Q k i=sourceCosetVector M P k i:=by
    by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
    · obtain ⟨j,hj,rfl⟩:=hp
      exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
    · exact (sourceCosetVector_upper_outside M h k i hp).symm
  have hq:=harmonicExtension_unique (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (sourceCosetVector M P k)
    (sourceCosetVector M Q k) hext (sourceCosetVector_harmonic M Q k)
  have hp:=harmonicExtension_unique (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (sourceCosetVector M P k)
    (sourceCosetVector M P k) (fun _ _=>rfl)
    (fun i=>sourceCosetVector_harmonic M P k ⟨i,Set.image_mono h.1 i.property⟩)
  exact hq.trans hp.symm

lemma sourceCosetVector_lower_comparison {P Q:Deligne M} (h:Q≤P) (k:ℕ)
    (ho:∀i∈P.val.1,i∉Q.val.1→sourceCosetVector M P k (.inl i)≤ sourceCosetVector M Q k (.inl i)) :
    sourceCosetVector M P k≤ sourceCosetVector M Q k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (sourceCosetVector M P k) (sourceCosetVector M Q k)
    (fun i=>sourceCosetVector_harmonic M P k ⟨i,Set.image_mono h.1 i.property⟩)
    (sourceCosetVector_harmonic M Q k)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (sourceCosetVector_upper_outside M h k i hp).le

lemma sourceCosetVector_lower_comparison_rev {P Q:Deligne M} (h:Q≤P) (k:ℕ)
    (ho:∀i∈P.val.1,i∉Q.val.1→sourceCosetVector M Q k (.inl i)≤ sourceCosetVector M P k (.inl i)) :
    sourceCosetVector M Q k≤ sourceCosetVector M P k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (sourceCosetVector M Q k) (sourceCosetVector M P k)
    (sourceCosetVector_harmonic M Q k)
    (fun i=>sourceCosetVector_harmonic M P k ⟨i,Set.image_mono h.1 i.property⟩)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (sourceCosetVector_upper_outside M h k i hp).symm.le

lemma sourceCosetVector_eq_above_lower {P Q:Deligne M} (h:Q≤P) {k:ℕ}
    (hk:sourceLowerLevel M P Q<k) : sourceCosetVector M Q k=sourceCosetVector M P k := by
  apply sourceCosetVector_eq_of_lower_open M h k
  intro i hi hq
  have hb:=sourcePeak_le_lowerLevel M P Q i hi hq
  rw [sourcePeak_above M Q i (hb.2.trans_lt hk),sourcePeak_above M P i (hb.1.trans_lt hk)]

lemma sourceBlock_eq_above_lower {P Q:Deligne M} (h:Q≤P) {k:ℕ}
    (hk:sourceLowerLevel M P Q<k) : sourceBlock M Q k=sourceBlock M P k := by
  have hv:=sourceCosetVector_eq_above_lower M h hk
  have hs:∀i,sourceCosetSign M P k i=sourceCosetSign M Q k i:=by
    apply sourceSignAt_congr_above
    intro d hd
    exact (sourceCosetVector_eq_above_lower M h (hk.trans_le hd)).symm
  have hz:(∑i∈P.val.1.toFinset \ Q.val.1.toFinset,sourceCosetSign M Q k (.inl i))=0:=by
    apply Finset.sum_eq_zero
    intro i hi
    have ht:=Finset.mem_sdiff.mp hi
    exact sourceSignAt_zero M _ _ _ (sourcePeak_above M Q i
      ((sourcePeak_le_lowerLevel M P Q i (Set.mem_toFinset.mp ht.1)
        (fun hq=>ht.2 (Set.mem_toFinset.mpr hq))).2.trans_lt hk))
  have hsec:=sourceSecondary_upper_change M h k hs
  rw [hz,add_zero] at hsec
  simp only [sourceBlock,sourceCosetSum,hv,hsec]

end HarmonicArtin

end OAI
