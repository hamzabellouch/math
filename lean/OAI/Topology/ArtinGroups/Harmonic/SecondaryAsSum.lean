import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Block
import OAI.Topology.ArtinGroups.Harmonic.Incidence
import OAI.Topology.ArtinGroups.Harmonic.HarmonicUpperAntitone

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceSecondary_as_sum (P:Deligne M) (k:ℕ) :
    sourceSecondary M P k=∑i∈P.val.1.toFinset,sourceCosetSign M P k (.inl i) :=
  (Finset.sum_subtype P.val.1.toFinset (fun _=>Set.mem_toFinset)
    (fun i=>sourceCosetSign M P k (.inl i))).symm

lemma sourceSecondary_upper_change {P R:Deligne M} (h:P≤R) (k:ℕ)
    (hs:∀i,sourceCosetSign M R k i=sourceCosetSign M P k i) :
    sourceSecondary M R k=sourceSecondary M P k+
      ∑i∈(R.val.1.toFinset \ P.val.1.toFinset),sourceCosetSign M P k (.inl i) := by
  rw [sourceSecondary_as_sum,sourceSecondary_as_sum]
  simp only [hs]
  rw [add_comm]
  exact (Finset.sum_sdiff (Set.toFinset_subset_toFinset.mpr h.1)).symm

lemma sourceBlock_eq_above_upper {P R:Deligne M} (h:P≤R) {k:ℕ}
    (hk:sourceUpperLevel M P R<k) : sourceBlock M R k=sourceBlock M P k := by
  have hv:=sourceCosetVector_eq_above_upper M h hk
  have hs:sourceSecondary M R k=sourceSecondary M P k:=by
    rw [sourceSecondary_upper_change M h k (sourceCosetSign_eq_above_upper M h hk)]
    have hz:(∑i∈(R.val.1.toFinset \ P.val.1.toFinset),sourceCosetSign M P k (.inl i))=0:=by
      apply Finset.sum_eq_zero
      intro i hi
      have hh:=Finset.mem_sdiff.mp hi
      have hb:=sourceIncidence_le_upperLevel M P R i (Set.mem_toFinset.mp hh.1)
        (fun ht=>hh.2 (Set.mem_toFinset.mpr ht))
      exact (source_no_incidence M (hb.trans_lt hk)).2.2
    rw [hz,add_zero]
  simp only [sourceBlock,sourceCosetSum,hv,hs]

lemma sourceCosetVector_upper_antitone {P R:Deligne M} (h:P≤R) (k:ℕ)
    (hr:∀i∈R.val.1,i∉P.val.1→0≤(framedCartan M *ᵥ sourceCosetVector M P k) (.inl i)) :
    sourceCosetVector M R k≤ sourceCosetVector M P k := by
  apply harmonic_upper_antitone (framedCartan M) (framedCartan_off M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (sourceCosetVector M P k) (sourceCosetVector M R k)
    (sourceCosetVector_upper_outside M h k) (sourceCosetVector_harmonic M R k)
  rintro ⟨_,⟨i,hi,rfl⟩⟩
  by_cases ht:i∈P.val.1
  · exact (sourceCosetVector_harmonic M P k ⟨.inl i,⟨i,ht,rfl⟩⟩).ge
  · exact hr i hi ht

lemma sourceCosetVector_upper_monotone {P R:Deligne M} (h:P≤R) (k:ℕ)
    (hr:∀i∈R.val.1,i∉P.val.1→(framedCartan M *ᵥ sourceCosetVector M P k) (.inl i)≤0) :
    sourceCosetVector M P k≤ sourceCosetVector M R k := by
  apply harmonic_upper_monotone (framedCartan M) (framedCartan_off M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (sourceCosetVector M P k) (sourceCosetVector M R k)
    (sourceCosetVector_upper_outside M h k) (sourceCosetVector_harmonic M R k)
  rintro ⟨_,⟨i,hi,rfl⟩⟩
  by_cases ht:i∈P.val.1
  · exact (sourceCosetVector_harmonic M P k ⟨.inl i,⟨i,ht,rfl⟩⟩).le
  · exact hr i hi ht

lemma sourceBlock_lt_of_sum_lt {P R:Deligne M} {k:ℕ}
    (h:sourceCosetSum M P k<sourceCosetSum M R k) : sourceBlock M P k<sourceBlock M R k :=
  Prod.Lex.lt_iff.mpr (Or.inl h)

lemma sourceBlock_lt_of_secondary_lt {P R:Deligne M} {k:ℕ}
    (hv:sourceCosetVector M P k=sourceCosetVector M R k)
    (hs:sourceSecondary M P k<sourceSecondary M R k) : sourceBlock M P k<sourceBlock M R k := by
  unfold sourceBlock
  apply Prod.Lex.lt_iff.mpr
  refine Or.inr ⟨?_,?_⟩
  · change sourceCosetSum M P k=sourceCosetSum M R k
    simp only [sourceCosetSum,hv]
  · exact Prod.Lex.lt_iff.mpr (Or.inr ⟨congrArg toLex hv,hs⟩)

end HarmonicArtin

end OAI
