import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedInitialCounts
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeTranslation

namespace OAI

/-! The initial singleton is a minimum of the full relative harmonic height. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)

private lemma vector_eq_single_of_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (o : ι) (hn : ∀ i, 0 ≤ v i) (ho : v o = 1)
    (hs : ∑ i, v i = 1) : v = (Pi.single o (1:ℝ) : ι → ℝ) := by
  have hnon (i : ι) : 0 ≤ v i - (Pi.single o (1:ℝ) : ι → ℝ) i := by
    by_cases hi : i = o
    · subst i
      simp only [Pi.single_eq_same, ho, sub_self, le_refl]
    · simpa only [Pi.single_eq_of_ne hi, sub_zero] using hn i
  have hsum : ∑ i, (v i - (Pi.single o (1:ℝ) : ι → ℝ) i) = 0 := by
    rw [Finset.sum_sub_distrib, hs]
    simp
  funext i
  exact sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnon i)).mp hsum i
    (Finset.mem_univ i))

lemma initial_profile (cutoff : ℤ) (k : ℕ) :
    pointedProfile M f (sourceCoset M ∅ (spherical_empty M) 1) cutoff k =
      if cutoff+k = 0 then Pi.single (.inl f) 1 else 0 := by
  ext i
  change pointedCosetVector M f (sourceCoset M ∅ (spherical_empty M) 1) (cutoff+k) i = _
  rw [pointedCosetVector_empty, pointedMultiplicity_one]
  by_cases hk : cutoff+k = 0 <;> simp [hk, Pi.single_apply]

lemma pointedCosetVector_frame_of_relative (Y : Set S) (hf : f ∉ Y)
    (P : RelativeVertex M Y 1) (k : ℤ) :
    pointedCosetVector M f P.val k (.inl f) = if k = 0 then 1 else 0 := by
  have hfP : (.inl f : S ⊕ Unit) ∉ Sum.inl '' P.val.val.1 := by
    rintro ⟨i, hi, he⟩
    exact hf (Sum.inl.inj he ▸ P.property.1 hi)
  have hz : sourceCosetRepresentative M P.val ∈ artinParabolic M Y := by
    have h := P.property.2 (sourceCosetRepresentative_mem M P.val)
    simpa only [rightCoset, Set.mem_ofPred_eq, inv_one, _root_.mul_one] using h
  change pointedHarmonicAt M f P.val.val.1 _ k (.inl f) = _
  rw [pointedHarmonicAt_outside M f _ _ k _ hfP]
  exact pointedMultiplicity_frame M Y f hf _ hz k

lemma initial_block_le (U : Set (S ⊕ Unit)) (cutoff : ℤ) (Y : Set S) (hf : f ∉ Y)
    (P : RelativeVertex M Y 1) (k : ℕ) :
    relativeBlock M f U cutoff (sourceCoset M ∅ (spherical_empty M) 1) k ≤
      relativeBlock M f U cutoff P.val k := by
  let P₀ := sourceCoset M ∅ (spherical_empty M) 1
  change relativeBlock M f U cutoff P₀ k ≤ relativeBlock M f U cutoff P.val k
  have hmask₀ : relativeSignMask M f U cutoff P₀ k = 0 := by
    funext i
    simp only [relativeSignMask, P₀, sourceCoset, Set.image_empty, Set.notMem_empty,
      ↓reduceIte, Pi.zero_apply]
  by_cases hk : cutoff+k = 0
  · have hv₀ : pointedProfile M f P₀ cutoff k = Pi.single (.inl f) 1 := by
      simpa only [hk, ite_true] using initial_profile M f cutoff k
    have hs₀ : pointedCosetSum M f P₀ (cutoff+k) = 1 := by
      change (∑ i, pointedProfile M f P₀ cutoff k i) = 1
      rw [hv₀]
      simp
    have hframe : pointedProfile M f P.val cutoff k (.inl f) = 1 := by
      change pointedCosetVector M f P.val (cutoff+k) (.inl f) = 1
      rw [pointedCosetVector_frame_of_relative M f Y hf P, hk, ite_eq_left rfl]
    have hs : 1 ≤ pointedCosetSum M f P.val (cutoff+k) := by
      rw [←hframe]
      exact pointedCosetVector_le_sum M f P.val (cutoff+k) (.inl f)
    rcases lt_or_eq_of_le hs with hlt | heq
    · have hh : pointedCosetSum M f P₀ (cutoff+k) < pointedCosetSum M f P.val (cutoff+k) := by
        rw [hs₀]
        exact hlt
      exact (Prod.Lex.lt_iff.mpr (Or.inl hh)).le
    · have hv : pointedProfile M f P.val cutoff k = Pi.single (.inl f) 1 :=
        vector_eq_single_of_sum _ _ (pointedCosetVector_nonneg M f P.val (cutoff+k)) hframe heq.symm
      have hm : relativeSignMask M f U cutoff P.val k = 0 := by
        funext i
        unfold relativeSignMask
        by_cases hi : ofLex i ∈ Sum.inl '' P.val.val.1
        · have hne : ofLex i ≠ (.inl f : S ⊕ Unit) := by
            intro h
            obtain ⟨j, hj, hjf⟩ := hi
            exact hf (Sum.inl.inj (hjf.trans h) ▸ P.property.1 hj)
          simp only [hi, ↓reduceIte, relativeSign, hv, Pi.single_eq_of_ne hne,
            ↓reduceIte, Pi.zero_apply]
        · simp only [hi, ↓reduceIte, Pi.zero_apply]
      unfold relativeBlock
      rw [hs₀, ←heq, hv₀, hv, hmask₀, hm]
  · have hz : pointedProfile M f P₀ cutoff k = 0 := by
      simpa only [hk, ite_false] using initial_profile M f cutoff k
    rw [relativeBlock_of_vector_zero M f U cutoff P₀ k hz]
    exact relativeZeroBlock_le M f U cutoff _ (Or.inr ⟨P.val,k,rfl⟩)

/-- The minimum-height assertion in the proof of the initial stabilizer,
including the full vector and full sign mask. -/
theorem initial_height_minimum (U : Set (S ⊕ Unit)) (cutoff : ℤ) (Y : Set S) (hf : f ∉ Y)
    (P : RelativeVertex M Y 1) :
    relativeHeight M f U cutoff (sourceCoset M ∅ (spherical_empty M) 1) ≤
      relativeHeight M f U cutoff P.val := by
  apply Finsupp.toColex_monotone
  intro k
  have hb := initial_block_le M f U cutoff Y hf P k
  change relativeBlockRank M f U cutoff _ ≤ relativeBlockRank M f U cutoff _
  rcases lt_or_eq_of_le hb with hb | hb
  · exact (relativeBlockRank_strictMono M f U cutoff (Or.inr ⟨_,k,rfl⟩) hb).le
  · rw [hb]

end HarmonicArtin.ParabolicIntersections

end OAI
