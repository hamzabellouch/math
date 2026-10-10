import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveComponentPositive
import OAI.Topology.ArtinGroups.Harmonic.Incidence

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma source_incident_nonneg_row_positive (P:Deligne M) (k:ℕ) (i:S)
    (hi:levelIncident (framedCartan M) (sourceCosetProfile M P) k (.inl i))
    (hr:0≤(framedCartan M *ᵥ sourceCosetVector M P k) (.inl i)) :
    0<sourceCosetVector M P k (.inl i) := by
  rcases hi with hi|⟨j,hij,hj⟩
  · exact hi
  by_contra hn
  have hz:sourceCosetVector M P k (.inl i)=0:=
    le_antisymm (le_of_not_gt hn) (sourceCosetVector_nonneg M P k _)
  have ht:∀l∈(Finset.univ:Finset (S⊕Unit)),
      framedCartan M (.inl i) l*sourceCosetVector M P k l≤0:=by
    intro l _
    by_cases hl:(.inl i:S⊕Unit)=l
    · subst l; rw [hz,mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (framedCartan_off M _ _ hl)
        (sourceCosetVector_nonneg M P k l)
  exact (not_lt_of_ge hr) (Finset.sum_neg' ht
    ⟨j,Finset.mem_univ _,mul_neg_of_neg_of_pos hij hj⟩)

lemma sourceActive_iff (P:Deligne M) (i:S) :
    i∈sourceActive M P ↔ i∉P.val.1 ∧
      (0<(framedCartan M *ᵥ sourceCosetVector M P (sourceIncidence M P i)) (.inl i) ∨
       (framedCartan M *ᵥ sourceCosetVector M P (sourceIncidence M P i)) (.inl i)=0 ∧
       sourceCosetSign M P (sourceIncidence M P i) (.inl i)= -1) := by
  have hs:=sourceSignAt_neg_iff M (sourceCosetProfile M P) (sourceIncidence M P i)
    (.inl i) (sourceCosetVector_nonneg M P _ _)
  constructor
  · rintro ⟨ht,hr|⟨hz,hpos,hnot⟩⟩
    · exact ⟨ht,Or.inl hr⟩
    · exact ⟨ht,Or.inr ⟨hz,hs.mpr ⟨hpos,hnot⟩⟩⟩
  · rintro ⟨ht,hr|⟨hz,hneg⟩⟩
    · exact ⟨ht,Or.inl hr⟩
    · exact ⟨ht,Or.inr ⟨hz,hs.mp hneg⟩⟩

lemma sourceCosetSign_eq_one_of_not_negative (P:Deligne M) (k:ℕ) (i:S⊕Unit)
    (hi:0<sourceCosetVector M P k i) (hn:sourceCosetSign M P k i≠ -1) :
    sourceCosetSign M P k i=1 := by
  change (if sourceCosetVector M P k i=0 then 0 else if _ then 1 else -1)=1
  rw [ite_eq_right (ne_of_gt hi)]
  split_ifs with h
  · rfl
  · exact (hn (by simp only [sourceCosetSign,sourceSignAt,ite_eq_right (ne_of_gt hi),
      ite_eq_right h])).elim

lemma source_inactive_top_rows {P R:Deligne M} (_h:P≤R)
    (ha:∀i∈R.val.1,i∉P.val.1→i∉sourceActive M P) (i:S) (hi:i∈R.val.1) (ht:i∉P.val.1) :
    (framedCartan M *ᵥ sourceCosetVector M P (sourceUpperLevel M P R)) (.inl i)≤0 := by
  have hb:=sourceIncidence_le_upperLevel M P R i hi ht
  rcases eq_or_lt_of_le hb with he|he
  · have hn:=ha i hi ht
    rw [sourceActive_iff] at hn
    have hnrow:¬0<(framedCartan M *ᵥ sourceCosetVector M P (sourceIncidence M P i)) (.inl i):=
      fun hh=>hn ⟨ht,Or.inl hh⟩
    rw [←he]
    exact le_of_not_gt hnrow
  · rw [(source_no_incidence M he).2.1]

lemma source_active_top_rows {P R:Deligne M} (_h:P≤R)
    (ha:∀i∈R.val.1,i∉P.val.1→i∈sourceActive M P) (i:S) (hi:i∈R.val.1) (ht:i∉P.val.1) :
    0≤(framedCartan M *ᵥ sourceCosetVector M P (sourceUpperLevel M P R)) (.inl i) := by
  have hb:=sourceIncidence_le_upperLevel M P R i hi ht
  rcases eq_or_lt_of_le hb with he|he
  · have hh:=((sourceActive_iff M P i).mp (ha i hi ht)).2
    rw [he] at hh
    rcases hh with hh|⟨hh,_⟩
    · exact hh.le
    · exact le_of_eq hh.symm
  · rw [(source_no_incidence M he).2.1]

lemma source_inactive_sign (P:Deligne M) (i:S) (ht:i∉P.val.1)
    (hn:i∉sourceActive M P)
    (hr:(framedCartan M *ᵥ sourceCosetVector M P (sourceIncidence M P i)) (.inl i)=0) :
    sourceCosetSign M P (sourceIncidence M P i) (.inl i)=1 := by
  apply sourceCosetSign_eq_one_of_not_negative
  · exact source_incident_nonneg_row_positive M P _ i (sourceIncidence_incident M P i)
      (le_of_eq hr.symm)
  · intro hs
    exact hn ((sourceActive_iff M P i).mpr ⟨ht,Or.inr ⟨hr,hs⟩⟩)

lemma source_active_sign (P:Deligne M) (i:S) (ha:i∈sourceActive M P)
    (hr:(framedCartan M *ᵥ sourceCosetVector M P (sourceIncidence M P i)) (.inl i)=0) :
    sourceCosetSign M P (sourceIncidence M P i) (.inl i)= -1 := by
  rcases ((sourceActive_iff M P i).mp ha).2 with h|h
  · rw [hr] at h
    exact (lt_irrefl _ h).elim
  · exact h.2

end HarmonicArtin

end OAI
