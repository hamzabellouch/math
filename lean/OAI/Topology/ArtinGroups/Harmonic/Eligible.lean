import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PeakSupport

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

def SourceEligible (P Q:Deligne M) (i:S) : Prop :=
  i∈P.val.1 ∧ i∉Q.val.1 ∧
  (∀d:ℕ,sourcePeak M P i<d→sourceCosetVector M Q d (.inl i)=0) ∧
  (sourceCosetVector M Q (sourcePeak M P i) (.inl i)<sourceCosetVector M P (sourcePeak M P i) (.inl i) ∨
   sourceCosetVector M Q (sourcePeak M P i) (.inl i)=sourceCosetVector M P (sourcePeak M P i) (.inl i) ∧
     sourceCosetSign M P (sourcePeak M P i) (.inl i)=1)

lemma sourceCosetVector_open (Q:Deligne M) (i:S) (hi:i∉Q.val.1) (x:Artin M) (hx:x∈Q.val.2) (k:ℤ) :
    sourceCosetVector M Q k (.inl i)=sourceMultiplicity M x k (.inl i) := by
  rw [sourceCosetVector_eq M Q x hx]
  exact sourceHarmonicAt_outside M Q.val.1 x k _ (by
    rintro ⟨j,hj,he⟩; exact hi ((Sum.inl_injective he) ▸ hj))

lemma source_ineligible_top_ge {P Q:Deligne M}
    (ha:∀i∈P.val.1,i∉Q.val.1→¬SourceEligible M P Q i) :
    ∀i∈P.val.1,i∉Q.val.1→
      sourceCosetVector M P (sourceLowerLevel M P Q) (.inl i)≤
        sourceCosetVector M Q (sourceLowerLevel M P Q) (.inl i) := by
  intro i hi hq
  have hb:=sourcePeak_le_lowerLevel M P Q i hi hq
  rcases eq_or_lt_of_le hb.1 with he|he
  · by_contra hn
    apply ha i hi hq
    refine ⟨hi,hq,?_,Or.inl ?_⟩
    · intro d hd
      exact sourcePeak_above M Q i (hb.2.trans_lt (he ▸ hd))
    · rw [he]
      exact lt_of_not_ge hn
  · rw [sourcePeak_above M P i he]
    exact sourceCosetVector_nonneg M Q _ _

lemma source_eligible_top_le {P Q:Deligne M}
    (ha:∀i∈P.val.1,i∉Q.val.1→SourceEligible M P Q i) :
    ∀i∈P.val.1,i∉Q.val.1→
      sourceCosetVector M Q (sourceLowerLevel M P Q) (.inl i)≤
        sourceCosetVector M P (sourceLowerLevel M P Q) (.inl i) := by
  intro i hi hq
  have hb:=sourcePeak_le_lowerLevel M P Q i hi hq
  have hh:=ha i hi hq
  rcases eq_or_lt_of_le hb.1 with he|he
  · rcases hh.2.2.2 with hl|⟨hl,_⟩
    · rw [he] at hl; exact hl.le
    · rw [he] at hl; exact hl.le
  · rw [sourcePeak_above M P i he,hh.2.2.1 _ he]

lemma sourceCosetSign_eq_at_lower_tie {P Q:Deligne M} (h:Q≤P)
    (hv:sourceCosetVector M Q (sourceLowerLevel M P Q)=sourceCosetVector M P (sourceLowerLevel M P Q))
    (i:S⊕Unit) : sourceCosetSign M Q (sourceLowerLevel M P Q) i=
      sourceCosetSign M P (sourceLowerLevel M P Q) i := by
  apply sourceSignAt_congr_above
  intro d hd
  rcases eq_or_lt_of_le hd with rfl|hd
  · exact hv
  · exact sourceCosetVector_eq_above_lower M h hd

lemma sourceLowerLevel_prescribed_at_tie {P Q:Deligne M} (h:Q<P)
    (hv:sourceCosetVector M Q (sourceLowerLevel M P Q)=sourceCosetVector M P (sourceLowerLevel M P Q)) :
    ∃i,i∈P.val.1 ∧ i∉Q.val.1 ∧ sourcePeak M P i=sourceLowerLevel M P Q := by
  obtain ⟨i,hi,hq,hp⟩:=sourceLowerLevel_attained M h
  have hn:0<sourceCosetVector M P (sourceLowerLevel M P Q) (.inl i):=by
    rcases hp with hp|hp
    · exact hp
    · rwa [hv] at hp
  exact ⟨i,hi,hq,le_antisymm (sourcePeak_le_lowerLevel M P Q i hi hq).1
    (sourcePeak_bound M P i _ (ne_of_gt hn))⟩

lemma source_ineligible_tie_sign {P Q:Deligne M} (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1)
    (ha:¬SourceEligible M P Q i)
    (he:sourcePeak M P i=sourceLowerLevel M P Q)
    (hv:sourceCosetVector M Q (sourceLowerLevel M P Q)=sourceCosetVector M P (sourceLowerLevel M P Q)) :
    sourceCosetSign M P (sourceLowerLevel M P Q) (.inl i)= -1 := by
  have hp:=sourcePeak_positive M P i hi
  rw [he] at hp
  have hn:sourceCosetSign M P (sourceLowerLevel M P Q) (.inl i)≠1:=by
    intro hs
    apply ha
    refine ⟨hi,hq,?_,Or.inr ⟨?_,?_⟩⟩
    · intro d hd
      exact sourcePeak_above M Q i ((sourcePeak_le_lowerLevel M P Q i hi hq).2.trans_lt (he ▸ hd))
    · rw [he,hv]
    · rwa [he]
  dsimp only [sourceCosetSign,sourceSignAt] at hn ⊢
  rw [ite_eq_right (ne_of_gt hp)] at hn ⊢
  split_ifs with hs
  · rw [ite_eq_left hs] at hn
    exact (hn rfl).elim
  · rfl

lemma source_eligible_tie_sign {P Q:Deligne M} (i:S)
    (ha:SourceEligible M P Q i) (he:sourcePeak M P i=sourceLowerLevel M P Q)
    (hv:sourceCosetVector M Q (sourceLowerLevel M P Q)=sourceCosetVector M P (sourceLowerLevel M P Q)) :
    sourceCosetSign M P (sourceLowerLevel M P Q) (.inl i)=1 := by
  rcases ha.2.2.2 with hl|⟨_,hs⟩
  · rw [he,hv] at hl
    exact (lt_irrefl _ hl).elim
  · rwa [he] at hs

end HarmonicArtin

end OAI
