import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeLowerComparison

namespace OAI

/-! Closing the ineligible colors retracts descending lower faces onto eligible faces. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

abbrev RelativeDescendingLower (P:Deligne M) := {Q:Deligne M // Q<P ∧ relativeHeight M f U cutoff Q < relativeHeight M f U cutoff P}

def relativeEligibleSet (P Q:Deligne M) : Set S := {i | RelativeEligible M f U cutoff P Q i}

lemma relativeEligible_shared {P Q R:Deligne M} (h:Q≤R) (i:S) (hi:i∉R.val.1) :
    RelativeEligible M f U cutoff P Q i ↔ RelativeEligible M f U cutoff P R i := by
  have hq:i∉Q.val.1:=fun hh=>hi (h.1 hh)
  have he(k:ℕ):pointedProfile M f Q cutoff k (.inl i)=pointedProfile M f R cutoff k (.inl i):=
    (pointedCosetVector_upper_outside M f h (cutoff+k) (.inl i) (by
      rintro ⟨j,hj,hh⟩; exact hi ((Sum.inl_injective hh) ▸ hj))).symm
  simp only [RelativeEligible,he,hq,hi,not_false_eq_true,true_and]

noncomputable def relativeLowerClose (P Q:Deligne M) : Deligne M :=
  sourceCoset M (P.val.1 \ relativeEligibleSet M f U cutoff P Q)
    (source_spherical_mono M Set.sdiff_subset P.property.1) (sourceCosetRepresentative M Q)

lemma le_relativeLowerClose {P Q:Deligne M} (h:Q≤P) : Q≤ relativeLowerClose M f U cutoff P Q := by
  have he:=sourceCoset_eq M Q _ (sourceCosetRepresentative_mem M Q)
  nth_rw 1 [←he]
  exact sourceCoset_le M (show Q.val.1⊆P.val.1 \ relativeEligibleSet M f U cutoff P Q from
    fun i hi=>⟨h.1 hi,fun he=>he.2.1 hi⟩) _

lemma relativeLowerClose_le {P Q:Deligne M} (h:Q≤P) : relativeLowerClose M f U cutoff P Q≤P := by
  have he:=sourceCoset_eq M P _ (h.2 (sourceCosetRepresentative_mem M Q))
  calc
    relativeLowerClose M f U cutoff P Q≤ sourceCoset M P.val.1 P.property.1 (sourceCosetRepresentative M Q):=
      sourceCoset_le M Set.sdiff_subset _
    _=P:=he

lemma relativeLowerClose_all_eligible {P Q:Deligne M} (h:Q≤P) :
    ∀i∈P.val.1,i∉(relativeLowerClose M f U cutoff P Q).val.1→RelativeEligible M f U cutoff P (relativeLowerClose M f U cutoff P Q) i := by
  intro i hi hn
  have hh:RelativeEligible M f U cutoff P Q i:=by
    by_contra he
    exact hn ⟨hi,he⟩
  exact (relativeEligible_shared M f U cutoff (le_relativeLowerClose M f U cutoff h) i hn).mp hh

lemma relativeLowerClose_mem {P Q:Deligne M} (h:Q<P) (he:relativeHeight M f U cutoff Q < relativeHeight M f U cutoff P) :
    relativeLowerClose M f U cutoff P Q<P ∧ relativeHeight M f U cutoff (relativeLowerClose M f U cutoff P Q) < relativeHeight M f U cutoff P := by
  obtain ⟨i,hi⟩:=relativeLower_descending_has_eligible M f U cutoff h he
  have hl:relativeLowerClose M f U cutoff P Q<P:=by
    apply lt_of_le_of_ne (relativeLowerClose_le M f U cutoff h.le)
    intro hh
    have ht:=congrArg (fun K:Deligne M=>K.val.1) hh
    have hm:i∈(relativeLowerClose M f U cutoff P Q).val.1:=by rw [ht]; exact hi.1
    exact hm.2 hi
  exact ⟨hl,relativeLower_eligible_descending M f U cutoff hl (relativeLowerClose_all_eligible M f U cutoff h.le)⟩

lemma relativeLowerClose_monotone {P Q R:Deligne M} (h:Q≤R) (hr:R≤P) :
    relativeLowerClose M f U cutoff P Q≤ relativeLowerClose M f U cutoff P R := by
  have ht:P.val.1 \ relativeEligibleSet M f U cutoff P Q⊆P.val.1 \ relativeEligibleSet M f U cutoff P R:=by
    intro i hi
    refine ⟨hi.1,?_⟩
    intro hh
    exact hi.2 ((relativeEligible_shared M f U cutoff h i hh.2.1).mpr hh)
  have hx:(sourceCosetRepresentative M Q)∈(relativeLowerClose M f U cutoff P R).val.2:=
    (le_relativeLowerClose M f U cutoff hr).2 (h.2 (sourceCosetRepresentative_mem M Q))
  have he:=sourceCoset_eq M (relativeLowerClose M f U cutoff P R) _ hx
  rw [←he]
  exact sourceCoset_le M ht _

noncomputable def relativeLowerRetraction (P:Deligne M) :
    RelativeDescendingLower M f U cutoff P →o RelativeDescendingLower M f U cutoff P where
  toFun Q:=⟨relativeLowerClose M f U cutoff P Q,relativeLowerClose_mem M f U cutoff Q.property.1 Q.property.2⟩
  monotone':=fun _ R h=>relativeLowerClose_monotone M f U cutoff h R.property.1.le

lemma le_relativeLowerRetraction (P:Deligne M) (Q:RelativeDescendingLower M f U cutoff P) :
    Q≤ relativeLowerRetraction M f U cutoff P Q := le_relativeLowerClose M f U cutoff Q.property.1.le

lemma relativeLowerClose_eq_of_all {P Q:Deligne M}
    (he:∀i∈P.val.1,i∉Q.val.1→RelativeEligible M f U cutoff P Q i) (h:Q≤P) : relativeLowerClose M f U cutoff P Q=Q := by
  symm
  apply deligne_eq_of_le_type_eq M (le_relativeLowerClose M f U cutoff h)
  ext i
  change i∈Q.val.1 ↔ i∈P.val.1 ∧ ¬RelativeEligible M f U cutoff P Q i
  constructor
  · intro hi
    exact ⟨h.1 hi,fun hh=>hh.2.1 hi⟩
  · rintro ⟨hi,hn⟩
    by_contra hq
    exact hn (he i hi hq)

lemma relativeLowerRetraction_idem (P:Deligne M) (Q:RelativeDescendingLower M f U cutoff P) :
    relativeLowerRetraction M f U cutoff P (relativeLowerRetraction M f U cutoff P Q)=relativeLowerRetraction M f U cutoff P Q := by
  apply Subtype.ext
  exact relativeLowerClose_eq_of_all M f U cutoff (relativeLowerClose_all_eligible M f U cutoff Q.property.1.le)
    (relativeLowerClose_le M f U cutoff Q.property.1.le)


end HarmonicArtin.ParabolicIntersections

end OAI
