import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.LowerIneligibleLater

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

abbrev SourceEarlierLower (P:Deligne M) := {Q:Deligne M // Q<P ∧ SourceEarlier M Q P}

def sourceEligibleSet (P Q:Deligne M) : Set S := {i | SourceEligible M P Q i}

lemma sourceEligible_shared {P Q R:Deligne M} (h:Q≤R) (i:S) (hi:i∉R.val.1) :
    SourceEligible M P Q i ↔ SourceEligible M P R i := by
  have hq:i∉Q.val.1:=fun hh=>hi (h.1 hh)
  have he(k:ℕ):sourceCosetVector M Q k (.inl i)=sourceCosetVector M R k (.inl i):=
    (sourceCosetVector_upper_outside M h k (.inl i) (by
      rintro ⟨j,hj,hh⟩; exact hi ((Sum.inl_injective hh) ▸ hj))).symm
  simp only [SourceEligible,he,hq,hi,not_false_eq_true,true_and]

noncomputable def sourceLowerClose (P Q:Deligne M) : Deligne M :=
  sourceCoset M (P.val.1 \ sourceEligibleSet M P Q)
    (source_spherical_mono M Set.sdiff_subset P.property.1) (sourceCosetRepresentative M Q)

lemma le_sourceLowerClose {P Q:Deligne M} (h:Q≤P) : Q≤ sourceLowerClose M P Q := by
  have he:=sourceCoset_eq M Q _ (sourceCosetRepresentative_mem M Q)
  nth_rw 1 [←he]
  exact sourceCoset_le M (show Q.val.1⊆P.val.1 \ sourceEligibleSet M P Q from
    fun i hi=>⟨h.1 hi,fun he=>he.2.1 hi⟩) _

lemma sourceLowerClose_le {P Q:Deligne M} (h:Q≤P) : sourceLowerClose M P Q≤P := by
  have he:=sourceCoset_eq M P _ (h.2 (sourceCosetRepresentative_mem M Q))
  calc
    sourceLowerClose M P Q≤ sourceCoset M P.val.1 P.property.1 (sourceCosetRepresentative M Q):=
      sourceCoset_le M Set.sdiff_subset _
    _=P:=he

lemma sourceLowerClose_all_eligible {P Q:Deligne M} (h:Q≤P) :
    ∀i∈P.val.1,i∉(sourceLowerClose M P Q).val.1→SourceEligible M P (sourceLowerClose M P Q) i := by
  intro i hi hn
  have hh:SourceEligible M P Q i:=by
    by_contra he
    exact hn ⟨hi,he⟩
  exact (sourceEligible_shared M (le_sourceLowerClose M h) i hn).mp hh

lemma sourceLowerClose_mem {P Q:Deligne M} (h:Q<P) (he:SourceEarlier M Q P) :
    sourceLowerClose M P Q<P ∧ SourceEarlier M (sourceLowerClose M P Q) P := by
  obtain ⟨i,hi⟩:=sourceLower_earlier_has_eligible M h he
  have hl:sourceLowerClose M P Q<P:=by
    apply lt_of_le_of_ne (sourceLowerClose_le M h.le)
    intro hh
    have ht:=congrArg (fun K:Deligne M=>K.val.1) hh
    have hm:i∈(sourceLowerClose M P Q).val.1:=by rw [ht]; exact hi.1
    exact hm.2 hi
  exact ⟨hl,sourceLower_eligible_earlier M hl (sourceLowerClose_all_eligible M h.le)⟩

lemma sourceLowerClose_monotone {P Q R:Deligne M} (h:Q≤R) (hr:R≤P) :
    sourceLowerClose M P Q≤ sourceLowerClose M P R := by
  have ht:P.val.1 \ sourceEligibleSet M P Q⊆P.val.1 \ sourceEligibleSet M P R:=by
    intro i hi
    refine ⟨hi.1,?_⟩
    intro hh
    exact hi.2 ((sourceEligible_shared M h i hh.2.1).mpr hh)
  have hx:(sourceCosetRepresentative M Q)∈(sourceLowerClose M P R).val.2:=
    (le_sourceLowerClose M hr).2 (h.2 (sourceCosetRepresentative_mem M Q))
  have he:=sourceCoset_eq M (sourceLowerClose M P R) _ hx
  rw [←he]
  exact sourceCoset_le M ht _

noncomputable def sourceLowerRetraction (P:Deligne M) :
    SourceEarlierLower M P →o SourceEarlierLower M P where
  toFun Q:=⟨sourceLowerClose M P Q,sourceLowerClose_mem M Q.property.1 Q.property.2⟩
  monotone':=fun _ R h=>sourceLowerClose_monotone M h R.property.1.le

lemma le_sourceLowerRetraction (P:Deligne M) (Q:SourceEarlierLower M P) :
    Q≤ sourceLowerRetraction M P Q := le_sourceLowerClose M Q.property.1.le

lemma sourceLowerClose_eq_of_all {P Q:Deligne M}
    (he:∀i∈P.val.1,i∉Q.val.1→SourceEligible M P Q i) (h:Q≤P) : sourceLowerClose M P Q=Q := by
  symm
  apply deligne_eq_of_le_type_eq M (le_sourceLowerClose M h)
  ext i
  change i∈Q.val.1 ↔ i∈P.val.1 ∧ ¬SourceEligible M P Q i
  constructor
  · intro hi
    exact ⟨h.1 hi,fun hh=>hh.2.1 hi⟩
  · rintro ⟨hi,hn⟩
    by_contra hq
    exact hn (he i hi hq)

lemma sourceLowerRetraction_idem (P:Deligne M) (Q:SourceEarlierLower M P) :
    sourceLowerRetraction M P (sourceLowerRetraction M P Q)=sourceLowerRetraction M P Q := by
  apply Subtype.ext
  exact sourceLowerClose_eq_of_all M (sourceLowerClose_all_eligible M Q.property.1.le)
    (sourceLowerClose_le M Q.property.1.le)

end HarmonicArtin

end OAI
