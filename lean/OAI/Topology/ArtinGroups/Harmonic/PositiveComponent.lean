import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Harmonic

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

def sourcePositiveComponent (p:S⊕Unit→ℝ) (i:S⊕Unit) : Set (S⊕Unit) :=
  {j | Relation.ReflTransGen (fun a b=>0<p a ∧ framedCartan M a b<0 ∧ 0<p b) i j}

def sourceClosedRegion (I:Set (S⊕Unit)) : Set (S⊕Unit) :=
  {j | j∈I ∨ ∃i∈I,framedCartan M j i<0}

def SourceNullSign (p:ℕ→S⊕Unit→ℝ) (k:ℕ) (i:S⊕Unit) : Prop :=
  0<k ∧ (.inr () : S⊕Unit)∉sourcePositiveComponent M (p k) i ∧
    (∀j∈sourcePositiveComponent M (p k) i,(framedCartan M *ᵥ p k) j=0) ∧
    ∀j∈sourceClosedRegion M (sourcePositiveComponent M (p k) i),∀d,k<d→p d j=0

noncomputable def sourceSignAt (p:ℕ→S⊕Unit→ℝ) (k:ℕ) (i:S⊕Unit) : ℤ :=
  if p k i=0 then 0 else if SourceNullSign M p k i then 1 else -1

omit [LinearOrder S] in
lemma sourceSignAt_zero (p:ℕ→S⊕Unit→ℝ) (k:ℕ) (i:S⊕Unit) (h:p k i=0) :
    sourceSignAt M p k i=0 := by simp [sourceSignAt,h]

omit [LinearOrder S] in
lemma sourceSignAt_bounds (p:ℕ→S⊕Unit→ℝ) (k:ℕ) (i:S⊕Unit) :
    -1≤ sourceSignAt M p k i ∧ sourceSignAt M p k i≤1 := by
  unfold sourceSignAt
  split_ifs <;> norm_num

omit [LinearOrder S] in
lemma sourceSignAt_level_zero (p:ℕ→S⊕Unit→ℝ) (i:S⊕Unit) (h:p 0 i≠0) :
    sourceSignAt M p 0 i= -1 := by
  simp [sourceSignAt,h,SourceNullSign]

omit [LinearOrder S] in
lemma sourceSignAt_congr_above (p r:ℕ→S⊕Unit→ℝ) (k:ℕ)
    (h:∀d,k≤d→p d=r d) (i:S⊕Unit) : sourceSignAt M p k i=sourceSignAt M r k i := by
  have hk:=h k le_rfl
  have hn:SourceNullSign M p k i↔SourceNullSign M r k i := by
    simp only [SourceNullSign,hk]
    constructor
    · rintro ⟨h0,hf,hr,hb⟩
      refine ⟨h0,hf,hr,?_⟩
      intro j hj d hd
      rw [←h d hd.le]
      exact hb j hj d hd
    · rintro ⟨h0,hf,hr,hb⟩
      refine ⟨h0,hf,hr,?_⟩
      intro j hj d hd
      rw [h d hd.le]
      exact hb j hj d hd
  simp only [sourceSignAt,hk,hn]

noncomputable def sourceCosetSign (P:Deligne M) (k:ℕ) (i:S⊕Unit) : ℤ :=
  sourceSignAt M (fun d=>sourceCosetVector M P (d:ℤ)) k i

noncomputable def sourceSecondary (P:Deligne M) (k:ℕ) : ℤ :=
  ∑i:P.val.1,sourceCosetSign M P k (.inl (i:S))

lemma sourceSecondary_bounds (P:Deligne M) (k:ℕ) :
    -(Fintype.card S:ℤ)≤ sourceSecondary M P k ∧ sourceSecondary M P k≤Fintype.card S := by
  have hc:Fintype.card P.val.1≤Fintype.card S:=Fintype.card_le_of_injective _ Subtype.val_injective
  have hl:-(Fintype.card P.val.1:ℤ)≤ sourceSecondary M P k := by
    calc
      _ = ∑_:P.val.1,(-1:ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _=>(sourceSignAt_bounds M _ _ _).1)
  have hu:sourceSecondary M P k≤(Fintype.card P.val.1:ℤ) := by
    calc
      _ ≤ ∑_:P.val.1,(1:ℤ) := Finset.sum_le_sum (fun i _=>(sourceSignAt_bounds M _ _ _).2)
      _ = _ := by simp
  constructor <;> omega

lemma sourceCosetVector_zero_positive (P:Deligne M) (i:S) (hi:i∈P.val.1) :
    0<sourceCosetVector M P 0 (.inl i) := by
  have hp:=sourceCosetVector_nonneg M P 0
  by_contra hn
  have hz:sourceCosetVector M P 0 (.inl i)=0 := le_antisymm (le_of_not_gt hn) (hp _)
  have hrow:(framedCartan M *ᵥ sourceCosetVector M P 0) (.inl i)=0 :=
    sourceHarmonicAt_harmonic M P.val.1 P.property.1 _ 0 ⟨.inl i,⟨i,hi,rfl⟩⟩
  have hneg:(framedCartan M *ᵥ sourceCosetVector M P 0) (.inl i)<0 := by
    change (∑j,framedCartan M (.inl i) j*sourceCosetVector M P 0 j)<0
    have h: (∑j,framedCartan M (.inl i) j*sourceCosetVector M P 0 j)<∑_:S⊕Unit,(0:ℝ) := by
      apply Finset.sum_lt_sum
      · intro j _
        by_cases hj : (.inl i:S⊕Unit)=j
        · subst j; simp [hz]
        · exact mul_nonpos_of_nonpos_of_nonneg (framedCartan_off M _ _ hj) (hp j)
      · refine ⟨.inr (),Finset.mem_univ _,?_⟩
        rw [sourceCosetVector_frame]
        norm_num [framedCartan]
    simpa using h
  linarith

lemma sourceSecondary_zero (P:Deligne M) :
    sourceSecondary M P 0= -(Fintype.card P.val.1:ℤ) := by
  have h:∀i:P.val.1,sourceCosetSign M P 0 (.inl (i:S))= -1 := by
    intro i
    apply sourceSignAt_level_zero
    exact ne_of_gt (sourceCosetVector_zero_positive M P i i.property)
  simp only [sourceSecondary,h,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Int.mul_neg,
    mul_one]

end HarmonicArtin

end OAI
