import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile
import OAI.Topology.ArtinGroups.ParabolicIntersections.ActiveColors

namespace OAI

/-!
# The relative harmonic height

The finite-support, highest-level-first height of §6.2 of paper 082-03.
The last coordinate is the full closed-type sign mask. The cutoff is an
arbitrary integer; null signs can occur at the cutoff itself.
-/

namespace HarmonicArtin.ParabolicIntersections

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

noncomputable def relativeSign (p : ℕ →₀ (S ⊕ Unit → ℝ)) (k : ℕ) (i : S ⊕ Unit) : ℤ :=
  if p k i = 0 then 0 else if relativePositiveSign (framedCartan M) U p k i then 1 else -1

noncomputable def relativeSignMask (P : Deligne M) (k : ℕ) (i : Lex (S ⊕ Unit)) : ℤ :=
  if ofLex i ∈ Sum.inl '' P.val.1 then
    relativeSign M U (pointedProfile M f P cutoff) k (ofLex i) else 0

abbrev RelativeBlock (S : Type) :=
  Lex (ℝ × Lex (Lex (Lex (S ⊕ Unit) → ℝ) × Lex (Lex (S ⊕ Unit) → ℤ)))

noncomputable def relativeBlock (P : Deligne M) (k : ℕ) : RelativeBlock S :=
  toLex (pointedCosetSum M f P (cutoff + k),
    toLex (toLex (pointedProfile M f P cutoff k), toLex (relativeSignMask M f U cutoff P k)))

def relativeZeroBlock : RelativeBlock S := toLex (0, toLex (toLex 0, toLex 0))

def RelativeBlockOccurs (b : RelativeBlock S) : Prop :=
  b = relativeZeroBlock (S := S) ∨ ∃ P : Deligne M, ∃ k : ℕ, b = relativeBlock M f U cutoff P k

lemma relativeSignMask_bounds (P : Deligne M) (k : ℕ) (i : Lex (S ⊕ Unit)) :
    relativeSignMask M f U cutoff P k i ∈ Set.Icc (-1 : ℤ) 1 := by
  unfold relativeSignMask relativeSign
  split_ifs <;> norm_num

lemma relativeBlock_of_vector_zero (P : Deligne M) (k : ℕ)
    (hz : pointedProfile M f P cutoff k = 0) :
    relativeBlock M f U cutoff P k = relativeZeroBlock (S := S) := by
  have hmask : relativeSignMask M f U cutoff P k = 0 := by
    funext i
    simp only [relativeSignMask, relativeSign, hz, Pi.zero_apply, ↓reduceIte, ite_self]
  have hsum : pointedCosetSum M f P (cutoff + k) = 0 := by
    change (∑ i, pointedProfile M f P cutoff k i) = 0
    simp only [hz, Pi.zero_apply, Finset.sum_const_zero]
  simp only [relativeBlock, relativeZeroBlock, hz, hmask, hsum]
  rfl

lemma relativeZeroBlock_le (b : RelativeBlock S) (hb : RelativeBlockOccurs M f U cutoff b) :
    relativeZeroBlock (S := S) ≤ b := by
  rcases hb with rfl | ⟨P, k, rfl⟩
  · exact le_rfl
  by_cases hz : pointedProfile M f P cutoff k = 0
  · rw [relativeBlock_of_vector_zero M f U cutoff P k hz]
  · have hex : ∃ i, pointedProfile M f P cutoff k i ≠ 0 := by
      by_contra hn
      apply hz
      funext i
      exact not_not.mp (fun hi => hn ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hex
    have hp : 0 < pointedCosetSum M f P (cutoff + k) :=
      (lt_of_le_of_ne (pointedCosetVector_nonneg M f P (cutoff + k) i) (Ne.symm hi)).trans_le
        (pointedCosetVector_le_sum M f P (cutoff + k) i)
    exact (Prod.Lex.lt_iff.mpr (Or.inl hp)).le

lemma relativeBlock_bounded_finite (B : ℝ) :
    {b : RelativeBlock S | RelativeBlockOccurs M f U cutoff b ∧ (ofLex b).1 ≤ B}.Finite := by
  let A := {p : S ⊕ Unit → ℝ | ∃ P : Deligne M, ∃ k : ℤ,
    pointedCosetSum M f P k ≤ B ∧ p = pointedCosetVector M f P k}
  let Z := {z : Lex (S ⊕ Unit) → ℤ | ∀ i, z i ∈ Set.Icc (-1 : ℤ) 1}
  have hA : A.Finite := pointedCosetVector_bounded_finite M f B
  have hZ : Z.Finite := Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
  let bfun : (S ⊕ Unit → ℝ) × (Lex (S ⊕ Unit) → ℤ) → RelativeBlock S :=
    fun v => toLex (∑ i, v.1 i, toLex (toLex v.1, toLex v.2))
  apply ((hA.prod hZ).image bfun |>.insert (relativeZeroBlock (S := S))).subset
  rintro b ⟨(rfl | ⟨P, k, rfl⟩), hb⟩
  · exact Set.mem_insert _ _
  · apply Set.mem_insert_of_mem
    refine ⟨(pointedCosetVector M f P (cutoff + k), relativeSignMask M f U cutoff P k),
      ⟨⟨P, cutoff + k, hb, rfl⟩, fun i => relativeSignMask_bounds M f U cutoff P k i⟩, rfl⟩

lemma relativeBlock_predecessors_finite (b : RelativeBlock S) :
    {a : RelativeBlock S | RelativeBlockOccurs M f U cutoff a ∧ a < b}.Finite := by
  apply (relativeBlock_bounded_finite M f U cutoff (ofLex b).1).subset
  intro a ha
  exact ⟨ha.1, Prod.Lex.monotone_fst_ofLex ha.2.le⟩

noncomputable def relativeBlockRank (b : RelativeBlock S) : ℕ :=
  {a : RelativeBlock S | RelativeBlockOccurs M f U cutoff a ∧ a < b}.ncard

lemma relativeBlockRank_strictMono {b c : RelativeBlock S}
    (hb : RelativeBlockOccurs M f U cutoff b) (hbc : b < c) :
    relativeBlockRank M f U cutoff b < relativeBlockRank M f U cutoff c := by
  apply Set.ncard_lt_ncard _ (relativeBlock_predecessors_finite M f U cutoff c)
  refine ⟨fun a ha => ⟨ha.1, ha.2.trans hbc⟩, ?_⟩
  intro h
  exact (h ⟨hb, hbc⟩).2.false

lemma relativeBlockRank_eq_iff {b c : RelativeBlock S}
    (hb : RelativeBlockOccurs M f U cutoff b) (hc : RelativeBlockOccurs M f U cutoff c) :
    relativeBlockRank M f U cutoff b = relativeBlockRank M f U cutoff c ↔ b = c := by
  constructor
  · intro he
    rcases lt_trichotomy b c with h | h | h
    · have := relativeBlockRank_strictMono M f U cutoff hb h
      omega
    · exact h
    · have := relativeBlockRank_strictMono M f U cutoff hc h
      omega
  · exact congrArg _

lemma relativeBlockRank_lt_iff {b c : RelativeBlock S}
    (hb : RelativeBlockOccurs M f U cutoff b) (hc : RelativeBlockOccurs M f U cutoff c) :
    relativeBlockRank M f U cutoff b < relativeBlockRank M f U cutoff c ↔ b < c := by
  constructor
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with he | rfl
    · exact Nat.lt_asymm h (relativeBlockRank_strictMono M f U cutoff hc he)
    · exact h.false
  · exact relativeBlockRank_strictMono M f U cutoff hb

@[simp] lemma relativeBlockRank_zero :
    relativeBlockRank M f U cutoff (relativeZeroBlock (S := S)) = 0 := by
  have he : {a : RelativeBlock S | RelativeBlockOccurs M f U cutoff a ∧
      a < relativeZeroBlock (S := S)} = ∅ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro ha
    exact not_lt_of_ge (relativeZeroBlock_le M f U cutoff a ha)
  simp only [relativeBlockRank, he, Set.ncard_empty]

lemma relativeBlockRank_support_finite (P : Deligne M) :
    {k : ℕ | relativeBlockRank M f U cutoff (relativeBlock M f U cutoff P k) ≠ 0}.Finite := by
  apply (pointedProfile M f P cutoff).hasFiniteSupport.subset
  intro k hk
  change pointedProfile M f P cutoff k ≠ 0
  intro hz
  apply hk
  rw [relativeBlock_of_vector_zero M f U cutoff P k hz, relativeBlockRank_zero]

noncomputable def relativeHeight (P : Deligne M) : Colex (ℕ →₀ ℕ) :=
  toColex (Finsupp.ofSupportFinite
    (fun k => relativeBlockRank M f U cutoff (relativeBlock M f U cutoff P k))
    (relativeBlockRank_support_finite M f U cutoff P))

lemma relativeHeight_eq_blocks {P R : Deligne M}
    (he : relativeHeight M f U cutoff P = relativeHeight M f U cutoff R) (k : ℕ) :
    relativeBlock M f U cutoff P k = relativeBlock M f U cutoff R k := by
  apply (relativeBlockRank_eq_iff M f U cutoff (Or.inr ⟨P, k, rfl⟩) (Or.inr ⟨R, k, rfl⟩)).mp
  exact congrArg (fun h : Colex (ℕ →₀ ℕ) => ofColex h k) he

theorem relativeHeight_wellFounded :
    WellFounded (fun P R : Deligne M => relativeHeight M f U cutoff P < relativeHeight M f U cutoff R) :=
  InvImage.wf (relativeHeight M f U cutoff) wellFounded_lt

end HarmonicArtin.ParabolicIntersections

end OAI
