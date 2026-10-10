import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CosetSum
import OAI.Topology.ArtinGroups.Harmonic.PositiveComponent

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators

variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

abbrev SourceBlock (S:Type) := Lex (ℝ × Lex (Lex ((Lex (S⊕Unit))→ℝ) × ℤ))

noncomputable def sourceBlock (P:Deligne M) (k:ℕ) : SourceBlock S :=
  toLex (sourceCosetSum M P k,toLex (toLex (sourceCosetVector M P k),sourceSecondary M P k))

noncomputable def sourceZeroBlock : SourceBlock S := toLex (0,toLex (toLex 0,0))

def SourceBlockOccurs (b:SourceBlock S) : Prop :=
  b=sourceZeroBlock (S:=S) ∨ ∃ P:Deligne M,∃ k:ℕ,b=sourceBlock M P k

lemma sourceBlock_of_vector_zero (P:Deligne M) (k:ℕ) (h:sourceCosetVector M P k=0) :
    sourceBlock M P k=sourceZeroBlock (S:=S) := by
  have hh:sourceSecondary M P k=0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply sourceSignAt_zero
    exact congrFun h _
  simp only [sourceBlock,sourceZeroBlock,sourceCosetSum,h,Pi.zero_apply,Finset.sum_const_zero,hh]
  rfl

lemma sourceCosetSum_pos_of_ne_zero (P:Deligne M) (k:ℕ)
    (h:sourceCosetVector M P k≠0) : 0<sourceCosetSum M P k := by
  have hx:∃i,sourceCosetVector M P k i≠0 := by
    by_contra hn
    apply h
    funext i
    exact not_not.mp (fun hi=>hn ⟨i,hi⟩)
  obtain ⟨i,hi⟩:=hx
  exact (lt_of_le_of_ne (sourceCosetVector_nonneg M P k i) (Ne.symm hi)).trans_le
    (sourceCosetVector_le_sum M P k i)

lemma sourceZeroBlock_le (b:SourceBlock S) (h:SourceBlockOccurs M b) :
    sourceZeroBlock (S:=S)≤b := by
  rcases h with rfl|⟨P,k,rfl⟩
  · exact le_rfl
  by_cases hz:sourceCosetVector M P k=0
  · rw [sourceBlock_of_vector_zero M P k hz]
  · exact (Prod.Lex.lt_iff.mpr (Or.inl (sourceCosetSum_pos_of_ne_zero M P k hz))).le

lemma sourceBlock_bounded_finite (B:ℝ) :
    {b:SourceBlock S | SourceBlockOccurs M b ∧ (ofLex b).1≤B}.Finite := by
  let A:= {p:S⊕Unit→ℝ | ∃P:Deligne M,∃k:ℤ,sourceCosetSum M P k≤B ∧ p=sourceCosetVector M P k}
  let Z:Set ℤ:=Set.Icc (-(Fintype.card S:ℤ)) (Fintype.card S)
  have hA:A.Finite:=sourceCosetVector_bounded_finite M B
  have hZ:Z.Finite:=Set.finite_Icc _ _
  let f:(S⊕Unit→ℝ)×ℤ→SourceBlock S:=fun v=>toLex (∑i,v.1 i,toLex (toLex v.1,v.2))
  apply ((hA.prod hZ).image f |>.insert (sourceZeroBlock (S:=S))).subset
  rintro b ⟨(rfl|⟨P,k,rfl⟩),hb⟩
  · exact Set.mem_insert _ _
  · apply Set.mem_insert_of_mem
    refine ⟨(sourceCosetVector M P k,sourceSecondary M P k),⟨?_,?_⟩,rfl⟩
    · exact ⟨P,k,hb,rfl⟩
    · exact sourceSecondary_bounds M P k

lemma sourceBlock_predecessors_finite (b:SourceBlock S) :
    {a:SourceBlock S | SourceBlockOccurs M a ∧ a<b}.Finite := by
  apply (sourceBlock_bounded_finite M (ofLex b).1).subset
  intro a ha
  exact ⟨ha.1,Prod.Lex.monotone_fst_ofLex ha.2.le⟩

noncomputable def sourceBlockRank (b:SourceBlock S) : ℕ :=
  {a:SourceBlock S | SourceBlockOccurs M a ∧ a<b}.ncard

lemma sourceBlockRank_strictMono {b c:SourceBlock S} (hb:SourceBlockOccurs M b) (hbc:b<c) :
    sourceBlockRank M b<sourceBlockRank M c := by
  apply Set.ncard_lt_ncard _ (sourceBlock_predecessors_finite M c)
  refine ⟨fun a ha=>⟨ha.1,ha.2.trans hbc⟩,?_⟩
  intro h
  exact (h ⟨hb,hbc⟩).2.false

lemma sourceBlockRank_lt_iff {b c:SourceBlock S}
    (hb:SourceBlockOccurs M b) (hc:SourceBlockOccurs M c) :
    sourceBlockRank M b<sourceBlockRank M c ↔ b<c := by
  constructor
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with he|rfl
    · exact (Nat.lt_asymm h (sourceBlockRank_strictMono M hc he))
    · exact h.false
  · exact sourceBlockRank_strictMono M hb

lemma sourceBlockRank_eq_iff {b c:SourceBlock S}
    (hb:SourceBlockOccurs M b) (hc:SourceBlockOccurs M c) :
    sourceBlockRank M b=sourceBlockRank M c ↔ b=c := by
  constructor
  · intro he
    rcases lt_trichotomy b c with h|h|h
    · have := sourceBlockRank_strictMono M hb h; omega
    · exact h
    · have := sourceBlockRank_strictMono M hc h; omega
  · exact congrArg _

@[simp] lemma sourceBlockRank_zero : sourceBlockRank M (sourceZeroBlock (S:=S))=0 := by
  have he:{a:SourceBlock S | SourceBlockOccurs M a ∧ a<sourceZeroBlock (S:=S)}=∅ := by
    ext a
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_and]
    intro ha
    exact not_lt_of_ge (sourceZeroBlock_le M a ha)
  simp only [sourceBlockRank,he,Set.ncard_empty]

lemma sourceBlockRank_support_finite (P:Deligne M) :
    {k:ℕ | sourceBlockRank M (sourceBlock M P k)≠0}.Finite := by
  have h:{k:ℕ | sourceCosetVector M P (k:ℤ)≠0}.Finite :=
    (sourceCosetVector_support_finite M P).preimage (by intro a ha b hb he; exact Int.ofNat_inj.mp he)
  apply h.subset
  intro k hk
  change sourceCosetVector M P (k:ℤ)≠0
  intro hz
  apply hk
  rw [sourceBlock_of_vector_zero M P k hz,sourceBlockRank_zero]

noncomputable def sourceHeight (P:Deligne M) : Colex (ℕ→₀ℕ) :=
  toColex (Finsupp.ofSupportFinite (fun k=>sourceBlockRank M (sourceBlock M P k))
    (sourceBlockRank_support_finite M P))

lemma sourceHeight_lt_iff (P R:Deligne M) : sourceHeight M P<sourceHeight M R ↔
    ∃k,(∀d,k<d→sourceBlock M P d=sourceBlock M R d) ∧ sourceBlock M P k<sourceBlock M R k := by
  rw [Finsupp.Colex.lt_iff]
  simp only [sourceHeight]
  constructor
  · rintro ⟨k,hk,hlt⟩
    refine ⟨k,fun d hd=>?_,(sourceBlockRank_lt_iff M (Or.inr ⟨P,k,rfl⟩) (Or.inr ⟨R,k,rfl⟩)).mp hlt⟩
    exact (sourceBlockRank_eq_iff M (Or.inr ⟨P,d,rfl⟩) (Or.inr ⟨R,d,rfl⟩)).mp (hk d hd)
  · rintro ⟨k,hk,hlt⟩
    exact ⟨k,fun d hd=>congrArg (sourceBlockRank M) (hk d hd),
      (sourceBlockRank_lt_iff M (Or.inr ⟨P,k,rfl⟩) (Or.inr ⟨R,k,rfl⟩)).mpr hlt⟩

theorem sourceHeight_wellFounded : WellFounded (fun P R:Deligne M=>sourceHeight M P<sourceHeight M R) :=
  InvImage.wf (sourceHeight M) wellFounded_lt

end HarmonicArtin

end OAI
