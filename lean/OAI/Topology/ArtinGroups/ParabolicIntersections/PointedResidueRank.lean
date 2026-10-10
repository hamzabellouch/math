import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueAllowed
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueHeightZero
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCap
import OAI.Topology.ArtinGroups.Harmonic.ResidueRank
import Mathlib
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedRows
import OAI.Topology.ArtinGroups.Harmonic.TieCode
import OAI.Topology.ArtinGroups.Harmonic.ResidueHeightZeroVector

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedResidueHeight_range_finite (strict:Bool) (P:Deligne M) (q:ℤ) :
    (Set.range (fun X:PointedResidue M f strict P q=>pointedResidueHeight M f P X q)).Finite := by
  let A: Set (S⊕Unit→ℝ):={v | ∃X:Deligne M,∃k:ℤ,pointedCosetSum M f X k≤ pointedCosetSum M f P q ∧ v=pointedCosetVector M f X k}
  have hA:A.Finite:=pointedCosetVector_bounded_finite M f _
  apply (hA.image (fun v:S⊕Unit→ℝ=>∑i∈P.val.1.toFinset,(v (.inl i)-pointedCosetVector M f P q (.inl i)))).subset
  rintro h ⟨X,rfl⟩
  refine ⟨pointedCosetVector M f X q,⟨X,q,?_,rfl⟩,rfl⟩
  exact Finset.sum_le_sum (fun i _=>pointedResidueAllowed_le M f X.property i)

noncomputable def pointedResidueRank (strict:Bool) (P:Deligne M) (q:ℤ) (h:ℝ) : ℕ :=
  {a:ℝ | a∈Set.range (fun X:PointedResidue M f strict P q=>pointedResidueHeight M f P X q) ∧ a<h}.ncard

lemma pointedResidueRank_strictMono (strict:Bool) (P:Deligne M) (q:ℤ) {a b:ℝ}
    (ha:a∈Set.range (fun X:PointedResidue M f strict P q=>pointedResidueHeight M f P X q)) (hab:a<b) :
    pointedResidueRank M f strict P q a<pointedResidueRank M f strict P q b := by
  apply Set.ncard_lt_ncard _ ((pointedResidueHeight_range_finite M f strict P q).subset (fun _ h=>h.1))
  refine ⟨fun _ h=>⟨h.1,h.2.trans hab⟩,?_⟩
  intro h
  exact (h ⟨ha,hab⟩).2.false

lemma pointedResidueRank_lt_iff (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:PointedResidue M f strict P q) :
    pointedResidueRank M f strict P q (pointedResidueHeight M f P X q)<
      pointedResidueRank M f strict P q (pointedResidueHeight M f P Y q) ↔
      pointedResidueHeight M f P X q<pointedResidueHeight M f P Y q := by
  constructor
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hh|hh
    · have ht:=pointedResidueRank_strictMono M f strict P q ⟨Y,rfl⟩ hh
      exact (not_lt_of_ge h.le) ht
    · rw [hh] at h
      exact h.false
  · exact pointedResidueRank_strictMono M f strict P q ⟨X,rfl⟩

lemma pointedResidueRank_eq_iff (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:PointedResidue M f strict P q) :
    pointedResidueRank M f strict P q (pointedResidueHeight M f P X q)=
      pointedResidueRank M f strict P q (pointedResidueHeight M f P Y q) ↔
      pointedResidueHeight M f P X q=pointedResidueHeight M f P Y q := by
  constructor
  · intro he
    rcases lt_trichotomy (pointedResidueHeight M f P X q) (pointedResidueHeight M f P Y q) with h|h|h
    · have :=(pointedResidueRank_lt_iff M f strict P q X Y).mpr h;omega
    · exact h
    · have :=(pointedResidueRank_lt_iff M f strict P q Y X).mpr h;omega
  · intro h;rw[h]

noncomputable def pointedResidueSecondary (P X:Deligne M) (q:ℤ) : ℕ :=
  if pointedResidueHeight M f P X q<0 then Fintype.card S-X.val.1.ncard else X.val.1.ncard

noncomputable def pointedResidueKey (strict:Bool) (P:Deligne M) (q:ℤ)
    (X:PointedResidue M f strict P q) : Lex (ℕ × Lex (ℕ×ℕ)) :=
  toLex (pointedResidueRank M f strict P q (pointedResidueHeight M f P X q),
    toLex (pointedResidueSecondary M f P X q,sourceTieCode M X))

def PointedResidueEarlier (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:PointedResidue M f strict P q) : Prop := pointedResidueKey M f strict P q X<pointedResidueKey M f strict P q Y

lemma pointedResidueKey_injective (strict:Bool) (P:Deligne M) (q:ℤ) :
    Function.Injective (pointedResidueKey M f strict P q) := by
  intro X Y h
  apply Subtype.ext
  apply sourceTieCode_injective M
  exact congrArg (fun z:Lex (ℕ × Lex (ℕ×ℕ))=>(ofLex (ofLex z).2).2) h

theorem pointedResidueEarlier_wellFounded (strict:Bool) (P:Deligne M) (q:ℤ) :
    WellFounded (PointedResidueEarlier M f strict P q) :=
  InvImage.wf (pointedResidueKey M f strict P q) wellFounded_lt

lemma pointedResidueEarlier_iff (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:PointedResidue M f strict P q) :
    PointedResidueEarlier M f strict P q X Y ↔
      pointedResidueHeight M f P X q<pointedResidueHeight M f P Y q ∨
      pointedResidueHeight M f P X q=pointedResidueHeight M f P Y q ∧
        (pointedResidueSecondary M f P X q<pointedResidueSecondary M f P Y q ∨
          pointedResidueSecondary M f P X q=pointedResidueSecondary M f P Y q ∧ sourceTieCode M X<sourceTieCode M Y) := by
  change _< _ ↔ _
  rw [Prod.Lex.lt_iff]
  simp only [pointedResidueKey,ofLex_toLex,pointedResidueRank_lt_iff,pointedResidueRank_eq_iff,Prod.Lex.lt_iff]

lemma pointedResidueEarlier_lower_negative {strict:Bool} {P:Deligne M} {q:ℤ}
    (X Y:PointedResidue M f strict P q) (h:Y.val<X.val) (hh:pointedResidueHeight M f P X q<0) :
    PointedResidueEarlier M f strict P q Y X ↔ pointedResidueHeight M f P Y q<pointedResidueHeight M f P X q := by
  rw [pointedResidueEarlier_iff]
  have hn:Y.val.val.1.ncard<X.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  have hb:X.val.val.1.ncard≤Fintype.card S:=by simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card X.val.val.1
  constructor
  · rintro (h|⟨he,h⟩)
    · exact h
    · have hy:pointedResidueHeight M f P Y q<0:=he ▸ hh
      simp only [pointedResidueSecondary,hy,hh,ite_eq_left] at h
      omega
  · exact Or.inl

lemma pointedResidueEarlier_upper_negative {strict:Bool} {P:Deligne M} {q:ℤ}
    (X Y:PointedResidue M f strict P q) (h:X.val<Y.val) (hh:pointedResidueHeight M f P X q<0) :
    PointedResidueEarlier M f strict P q Y X ↔ pointedResidueHeight M f P Y q≤ pointedResidueHeight M f P X q := by
  rw [pointedResidueEarlier_iff]
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
      have hy:pointedResidueHeight M f P Y q<0:=he ▸ hh
      simp only [pointedResidueSecondary,hy,hh,ite_eq_left]
      omega

lemma pointedResidueEarlier_lower_zero {P:Deligne M} {q:ℤ}
    (X Y:PointedResidue M f false P q) (h:Y.val<X.val) (hh:pointedResidueHeight M f P X q=0) :
    PointedResidueEarlier M f false P q Y X := by
  rw [pointedResidueEarlier_iff]
  have hn:Y.val.val.1.ncard<X.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  rcases lt_or_eq_of_le (pointedResidueHeight_nonpos M f Y.property) with h|he
  · exact Or.inl (hh ▸ h)
  · refine Or.inr ⟨he.trans hh.symm,Or.inl ?_⟩
    simpa only [pointedResidueSecondary,he,hh,lt_self_iff_false,ite_false] using hn

lemma pointedResidueEarlier_upper_zero {P:Deligne M} {q:ℤ}
    (X Y:PointedResidue M f false P q) (h:X.val<Y.val) (hh:pointedResidueHeight M f P X q=0) :
    ¬PointedResidueEarlier M f false P q Y X := by
  have hv:pointedCosetVector M f X q=pointedCosetVector M f P q:=pointedResidueHeight_zero_vector M f X.property hh
  have heV:pointedCosetVector M f Y q=pointedCosetVector M f X q:=by
    apply pointedCosetVector_eq_of_upper_rows M f h.le q
    intro i hi _
    rw [hv]
    exact pointedCosetVector_harmonic M f P q ⟨.inl i,⟨i,Y.property.1.le.1 hi,rfl⟩⟩
  have he:pointedResidueHeight M f P Y q=0:=by
    unfold pointedResidueHeight at hh ⊢
    rw [heV]
    exact hh
  rw [pointedResidueEarlier_iff,he,hh]
  have hn:X.val.val.1.ncard<Y.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  simp only [pointedResidueSecondary,he,hh,lt_self_iff_false,ite_false,false_or,true_and]
  omega

end HarmonicArtin.ParabolicIntersections

end OAI
