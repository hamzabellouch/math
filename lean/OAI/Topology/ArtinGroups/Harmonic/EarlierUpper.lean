import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CosetSignUpperTie

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

abbrev SourceEarlierUpper (P:Deligne M) := {R:Deligne M // P<R ∧ SourceEarlier M R P}

noncomputable def sourceActiveTop (P:Deligne M) : Deligne M :=
  sourceCoset M (P.val.1 ∪ sourceActive M P) (sourceActive_spherical M P)
    (sourceCosetRepresentative M P)

noncomputable def sourceUpperClip (P R:Deligne M) : Deligne M :=
  sourceCoset M (R.val.1 ∩ (P.val.1 ∪ sourceActive M P))
    (source_spherical_mono M Set.inter_subset_left R.property.1)
    (sourceCosetRepresentative M P)

lemma sourceUpperClip_le {P R:Deligne M} (h:P≤ R) : sourceUpperClip M P R≤ R := by
  have he:=sourceCoset_eq M R _ (h.2 (sourceCosetRepresentative_mem M P))
  rw [←he]
  exact sourceCoset_le M Set.inter_subset_left _

lemma le_sourceUpperClip {P R:Deligne M} (h:P≤ R) : P≤ sourceUpperClip M P R := by
  have he:=sourceCoset_eq M P _ (sourceCosetRepresentative_mem M P)
  nth_rw 1 [←he]
  exact sourceCoset_le M (show P.val.1 ⊆ R.val.1 ∩ (P.val.1 ∪ sourceActive M P) from fun i hi=>⟨h.1 hi,Or.inl hi⟩) _

lemma sourceUpperClip_le_top (P R:Deligne M) : sourceUpperClip M P R≤ sourceActiveTop M P :=
  sourceCoset_le M Set.inter_subset_right _

lemma sourceUpperClip_monotone (P:Deligne M) : Monotone (sourceUpperClip M P) := by
  intro R Q h
  exact sourceCoset_le M (show R.val.1 ∩ (P.val.1 ∪ sourceActive M P) ⊆ Q.val.1 ∩ (P.val.1 ∪ sourceActive M P) from fun i hi=>⟨h.1 hi.1,hi.2⟩) _

lemma sourceUpperClip_mem {P R:Deligne M} (h:P<R) (he:SourceEarlier M R P) :
    P<sourceUpperClip M P R ∧ SourceEarlier M (sourceUpperClip M P R) P := by
  obtain ⟨i,hi,ht,ha⟩:=sourceUpper_earlier_has_active M h he
  have hl:P<sourceUpperClip M P R:=by
    apply lt_of_le_of_ne (le_sourceUpperClip M h.le)
    intro hh
    have hm:i∈(sourceUpperClip M P R).val.1:=⟨hi,Or.inr ha⟩
    rw [←hh] at hm
    exact ht hm
  refine ⟨hl,sourceUpper_active_earlier M hl ?_⟩
  intro j hj hn
  exact hj.2.resolve_left hn

noncomputable def sourceUpperRetraction (P:Deligne M) :
    SourceEarlierUpper M P →o SourceEarlierUpper M P where
  toFun R:=⟨sourceUpperClip M P R,sourceUpperClip_mem M R.property.1 R.property.2⟩
  monotone' := fun _ _ h=>sourceUpperClip_monotone M P h

lemma sourceUpperRetraction_le (P:Deligne M) (R:SourceEarlierUpper M P) :
    sourceUpperRetraction M P R≤ R := sourceUpperClip_le M R.property.1.le

lemma sourceUpperClip_idem (P R:Deligne M) :
    sourceUpperClip M P (sourceUpperClip M P R)=sourceUpperClip M P R := by
  apply Subtype.ext
  simp only [sourceUpperClip,sourceCoset,Set.inter_assoc,Set.inter_self]

lemma sourceUpperRetraction_idem (P:Deligne M) (R:SourceEarlierUpper M P) :
    sourceUpperRetraction M P (sourceUpperRetraction M P R)=sourceUpperRetraction M P R := by
  apply Subtype.ext
  exact sourceUpperClip_idem M P R

lemma sourceActiveTop_mem (P:Deligne M) (ha:(sourceActive M P).Nonempty) :
    P<sourceActiveTop M P ∧ SourceEarlier M (sourceActiveTop M P) P := by
  have hl:P<sourceActiveTop M P:=by
    apply lt_of_le_of_ne
    · have he:=sourceCoset_eq M P _ (sourceCosetRepresentative_mem M P)
      nth_rw 1 [←he]
      exact sourceCoset_le M Set.subset_union_left _
    · intro he
      obtain ⟨i,hi⟩:=ha
      have hm:i∈(sourceActiveTop M P).val.1:=Or.inr hi
      rw [←he] at hm
      exact hi.1 hm
  exact ⟨hl,sourceUpper_active_earlier M hl (fun _ hi hn=>hi.resolve_left hn)⟩

noncomputable def sourceUpperCenter (P:Deligne M) (ha:(sourceActive M P).Nonempty) :
    SourceEarlierUpper M P:=⟨sourceActiveTop M P,sourceActiveTop_mem M P ha⟩

lemma sourceUpperRetraction_le_center (P:Deligne M) (ha:(sourceActive M P).Nonempty)
    (R:SourceEarlierUpper M P) : sourceUpperRetraction M P R≤ sourceUpperCenter M P ha :=
  sourceUpperClip_le_top M P R

lemma sourceEarlierUpper_nonempty_iff (P:Deligne M) :
    Nonempty (SourceEarlierUpper M P) ↔ (sourceActive M P).Nonempty := by
  constructor
  · rintro ⟨R⟩
    obtain ⟨i,_,_,hi⟩:=sourceUpper_earlier_has_active M R.property.1 R.property.2
    exact ⟨i,hi⟩
  · intro h
    exact ⟨sourceUpperCenter M P h⟩

end HarmonicArtin

end OAI
