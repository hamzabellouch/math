import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveComponent
import OAI.Topology.ArtinGroups.Harmonic.Coset
import OAI.Topology.ArtinGroups.Harmonic.CosetProfile

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceIncidence (P:Deligne M) (i:S) : ℕ :=
  incidenceLevel (framedCartan M) (sourceCosetProfile M P) (.inl i)

lemma sourceIncidence_incident (P:Deligne M) (i:S) :
    levelIncident (framedCartan M) (sourceCosetProfile M P) (sourceIncidence M P i) (.inl i) := by
  apply incidenceLevel_incident
  refine ⟨0,Or.inr ⟨.inr (),?_,?_⟩⟩
  · norm_num [framedCartan]
  · rw [sourceCosetProfile_apply,sourceCosetVector_frame]; norm_num

lemma source_incidence_le (P:Deligne M) {k:ℕ} {i:S}
    (h:levelIncident (framedCartan M) (sourceCosetProfile M P) k (.inl i)) :
    k≤ sourceIncidence M P i := levelIncident_le _ _ h

lemma source_no_incidence {P:Deligne M} {k:ℕ} {i:S} (h:sourceIncidence M P i<k) :
    sourceCosetVector M P k (.inl i)=0 ∧
    (framedCartan M *ᵥ sourceCosetVector M P k) (.inl i)=0 ∧
    sourceCosetSign M P k (.inl i)=0 := by
  have hn:¬levelIncident (framedCartan M) (sourceCosetProfile M P) k (.inl i):=
    fun hi=>Nat.not_lt_of_ge (source_incidence_le M P hi) h
  have hz:sourceCosetVector M P k (.inl i)=0:=le_antisymm
    (le_of_not_gt (fun hp=>hn (Or.inl hp))) (sourceCosetVector_nonneg M P k _)
  refine ⟨hz,?_,sourceSignAt_zero M _ _ _ hz⟩
  exact no_incidence_row_zero (framedCartan M) (framedCartan_off M)
    (sourceCosetProfile M P) (fun k i=>sourceCosetVector_nonneg M P k i) hn

noncomputable def sourceUpperLevel (P R:Deligne M) : ℕ :=
  (R.val.1.toFinset \ P.val.1.toFinset).sup (sourceIncidence M P)

lemma sourceIncidence_le_upperLevel (P R:Deligne M) (i:S)
    (hi:i∈R.val.1) (ht:i∉P.val.1) : sourceIncidence M P i≤ sourceUpperLevel M P R :=
  Finset.le_sup (f:=sourceIncidence M P) (by simp [hi,ht])

lemma sourceUpperLevel_attained {P R:Deligne M} (h:P<R) :
    ∃i, i∈R.val.1 ∧ i∉P.val.1 ∧ sourceIncidence M P i=sourceUpperLevel M P R := by
  have hs:=deligne_lt_type M h
  obtain ⟨i,hi,ht⟩:=Set.exists_of_ssubset hs
  have hf:(R.val.1.toFinset \ P.val.1.toFinset).Nonempty:=⟨i,by simp [hi,ht]⟩
  obtain ⟨j,hj,he⟩:=Finset.exists_mem_eq_sup _ hf (sourceIncidence M P)
  have hm:=Finset.mem_sdiff.mp hj
  exact ⟨j,by simpa using hm.1,by simpa using hm.2,he.symm⟩

lemma sourceCosetVector_eq_of_upper_rows {P R:Deligne M} (h:P≤R) (k:ℤ)
    (hr:∀i∈R.val.1,i∉P.val.1→(framedCartan M *ᵥ sourceCosetVector M P k) (.inl i)=0) :
    sourceCosetVector M R k=sourceCosetVector M P k := by
  rw [sourceCosetVector_upper_harmonize M h k]
  symm
  apply harmonicExtension_unique (framedCartan M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (sourceCosetVector M P k) (sourceCosetVector M P k)
  · intro _ _; rfl
  · rintro ⟨_,⟨i,hi,rfl⟩⟩
    by_cases ht:i∈P.val.1
    · exact sourceCosetVector_harmonic M P k ⟨.inl i,⟨i,ht,rfl⟩⟩
    · exact hr i hi ht

lemma sourceCosetVector_eq_above_upper {P R:Deligne M} (h:P≤R) {k:ℕ}
    (hk:sourceUpperLevel M P R<k) : sourceCosetVector M R k=sourceCosetVector M P k := by
  apply sourceCosetVector_eq_of_upper_rows M h k
  intro i hi ht
  exact (source_no_incidence M ((sourceIncidence_le_upperLevel M P R i hi ht).trans_lt hk)).2.1

lemma sourceCosetSign_eq_above_upper {P R:Deligne M} (h:P≤R) {k:ℕ}
    (hk:sourceUpperLevel M P R<k) (i:S⊕Unit) :
    sourceCosetSign M R k i=sourceCosetSign M P k i := by
  apply sourceSignAt_congr_above
  intro d hd
  exact sourceCosetVector_eq_above_upper M h (hk.trans_le hd)

end HarmonicArtin

end OAI
