import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Incidence
import OAI.Topology.ArtinGroups.Harmonic.TieCode
import OAI.Topology.ArtinGroups.Harmonic.ResidueHeightZeroVector

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceResidueHeight_range_finite (strict:Bool) (P:Deligne M) (q:ℤ) :
    (Set.range (fun X:SourceResidue M strict P q=>sourceResidueHeight M P X q)).Finite := by
  let A: Set (S⊕Unit→ℝ):={v | ∃X:Deligne M,∃k:ℤ,sourceCosetSum M X k≤ sourceCosetSum M P q ∧ v=sourceCosetVector M X k}
  have hA:A.Finite:=sourceCosetVector_bounded_finite M _
  apply (hA.image (fun v:S⊕Unit→ℝ=>∑i∈P.val.1.toFinset,(v (.inl i)-sourceCosetVector M P q (.inl i)))).subset
  rintro h ⟨X,rfl⟩
  refine ⟨sourceCosetVector M X q,⟨X,q,?_,rfl⟩,rfl⟩
  exact Finset.sum_le_sum (fun i _=>sourceResidueAllowed_le M X.property i)

noncomputable def sourceResidueRank (strict:Bool) (P:Deligne M) (q:ℤ) (h:ℝ) : ℕ :=
  {a:ℝ | a∈Set.range (fun X:SourceResidue M strict P q=>sourceResidueHeight M P X q) ∧ a<h}.ncard

lemma sourceResidueRank_strictMono (strict:Bool) (P:Deligne M) (q:ℤ) {a b:ℝ}
    (ha:a∈Set.range (fun X:SourceResidue M strict P q=>sourceResidueHeight M P X q)) (hab:a<b) :
    sourceResidueRank M strict P q a<sourceResidueRank M strict P q b := by
  apply Set.ncard_lt_ncard _ ((sourceResidueHeight_range_finite M strict P q).subset (fun _ h=>h.1))
  refine ⟨fun _ h=>⟨h.1,h.2.trans hab⟩,?_⟩
  intro h
  exact (h ⟨ha,hab⟩).2.false

lemma sourceResidueRank_lt_iff (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:SourceResidue M strict P q) :
    sourceResidueRank M strict P q (sourceResidueHeight M P X q)<
      sourceResidueRank M strict P q (sourceResidueHeight M P Y q) ↔
      sourceResidueHeight M P X q<sourceResidueHeight M P Y q := by
  constructor
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hh|hh
    · have ht:=sourceResidueRank_strictMono M strict P q ⟨Y,rfl⟩ hh
      exact (not_lt_of_ge h.le) ht
    · rw [hh] at h
      exact h.false
  · exact sourceResidueRank_strictMono M strict P q ⟨X,rfl⟩

lemma sourceResidueRank_eq_iff (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:SourceResidue M strict P q) :
    sourceResidueRank M strict P q (sourceResidueHeight M P X q)=
      sourceResidueRank M strict P q (sourceResidueHeight M P Y q) ↔
      sourceResidueHeight M P X q=sourceResidueHeight M P Y q := by
  constructor
  · intro he
    rcases lt_trichotomy (sourceResidueHeight M P X q) (sourceResidueHeight M P Y q) with h|h|h
    · have :=(sourceResidueRank_lt_iff M strict P q X Y).mpr h;omega
    · exact h
    · have :=(sourceResidueRank_lt_iff M strict P q Y X).mpr h;omega
  · intro h;rw[h]

noncomputable def sourceResidueSecondary (P X:Deligne M) (q:ℤ) : ℕ :=
  if sourceResidueHeight M P X q<0 then Fintype.card S-X.val.1.ncard else X.val.1.ncard

noncomputable def sourceResidueKey (strict:Bool) (P:Deligne M) (q:ℤ)
    (X:SourceResidue M strict P q) : Lex (ℕ × Lex (ℕ×ℕ)) :=
  toLex (sourceResidueRank M strict P q (sourceResidueHeight M P X q),
    toLex (sourceResidueSecondary M P X q,sourceTieCode M X))

def SourceResidueEarlier (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:SourceResidue M strict P q) : Prop := sourceResidueKey M strict P q X<sourceResidueKey M strict P q Y

lemma sourceResidueKey_injective (strict:Bool) (P:Deligne M) (q:ℤ) :
    Function.Injective (sourceResidueKey M strict P q) := by
  intro X Y h
  apply Subtype.ext
  apply sourceTieCode_injective M
  exact congrArg (fun z:Lex (ℕ × Lex (ℕ×ℕ))=>(ofLex (ofLex z).2).2) h

theorem sourceResidueEarlier_wellFounded (strict:Bool) (P:Deligne M) (q:ℤ) :
    WellFounded (SourceResidueEarlier M strict P q) :=
  InvImage.wf (sourceResidueKey M strict P q) wellFounded_lt

lemma sourceResidueEarlier_iff (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:SourceResidue M strict P q) :
    SourceResidueEarlier M strict P q X Y ↔
      sourceResidueHeight M P X q<sourceResidueHeight M P Y q ∨
      sourceResidueHeight M P X q=sourceResidueHeight M P Y q ∧
        (sourceResidueSecondary M P X q<sourceResidueSecondary M P Y q ∨
          sourceResidueSecondary M P X q=sourceResidueSecondary M P Y q ∧ sourceTieCode M X<sourceTieCode M Y) := by
  change _< _ ↔ _
  rw [Prod.Lex.lt_iff]
  simp only [sourceResidueKey,ofLex_toLex,sourceResidueRank_lt_iff,sourceResidueRank_eq_iff,Prod.Lex.lt_iff]

lemma sourceResidueEarlier_lower_negative {strict:Bool} {P:Deligne M} {q:ℤ}
    (X Y:SourceResidue M strict P q) (h:Y.val<X.val) (hh:sourceResidueHeight M P X q<0) :
    SourceResidueEarlier M strict P q Y X ↔ sourceResidueHeight M P Y q<sourceResidueHeight M P X q := by
  rw [sourceResidueEarlier_iff]
  have hn:Y.val.val.1.ncard<X.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  have hb:X.val.val.1.ncard≤Fintype.card S:=by simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card X.val.val.1
  constructor
  · rintro (h|⟨he,h⟩)
    · exact h
    · have hy:sourceResidueHeight M P Y q<0:=he ▸ hh
      simp only [sourceResidueSecondary,hy,hh,ite_eq_left] at h
      omega
  · exact Or.inl

lemma sourceResidueEarlier_upper_negative {strict:Bool} {P:Deligne M} {q:ℤ}
    (X Y:SourceResidue M strict P q) (h:X.val<Y.val) (hh:sourceResidueHeight M P X q<0) :
    SourceResidueEarlier M strict P q Y X ↔ sourceResidueHeight M P Y q≤ sourceResidueHeight M P X q := by
  rw [sourceResidueEarlier_iff]
  have hn:X.val.val.1.ncard<Y.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  have hb:Y.val.val.1.ncard≤Fintype.card S:=by simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card Y.val.val.1
  constructor
  · rintro (h|⟨he,_⟩)
    · exact h.le
    · exact he.le
  · intro h
    rcases lt_or_eq_of_le h with h|he
    · exact Or.inl h
    · refine Or.inr ⟨he,Or.inl ?_⟩
      have hy:sourceResidueHeight M P Y q<0:=he ▸ hh
      simp only [sourceResidueSecondary,hy,hh,ite_eq_left]
      omega

lemma sourceResidueEarlier_lower_zero {P:Deligne M} {q:ℤ}
    (X Y:SourceResidue M false P q) (h:Y.val<X.val) (hh:sourceResidueHeight M P X q=0) :
    SourceResidueEarlier M false P q Y X := by
  rw [sourceResidueEarlier_iff]
  have hn:Y.val.val.1.ncard<X.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  rcases lt_or_eq_of_le (sourceResidueHeight_nonpos M Y.property) with h|he
  · exact Or.inl (hh ▸ h)
  · refine Or.inr ⟨he.trans hh.symm,Or.inl ?_⟩
    simpa only [sourceResidueSecondary,he,hh,lt_self_iff_false,ite_false] using hn

lemma sourceResidueEarlier_upper_zero {P:Deligne M} {q:ℤ}
    (X Y:SourceResidue M false P q) (h:X.val<Y.val) (hh:sourceResidueHeight M P X q=0) :
    ¬SourceResidueEarlier M false P q Y X := by
  have hv:sourceCosetVector M X q=sourceCosetVector M P q:=sourceResidueHeight_zero_vector M X.property hh
  have heV:sourceCosetVector M Y q=sourceCosetVector M X q:=by
    apply sourceCosetVector_eq_of_upper_rows M h.le q
    intro i hi _
    rw [hv]
    exact sourceCosetVector_harmonic M P q ⟨.inl i,⟨i,Y.property.1.le.1 hi,rfl⟩⟩
  have he:sourceResidueHeight M P Y q=0:=by
    unfold sourceResidueHeight at hh ⊢
    rw [heV]
    exact hh
  rw [sourceResidueEarlier_iff,he,hh]
  have hn:X.val.val.1.ncard<Y.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  simp only [sourceResidueSecondary,he,hh,lt_self_iff_false,ite_false,false_or,true_and]
  omega

end HarmonicArtin

end OAI
