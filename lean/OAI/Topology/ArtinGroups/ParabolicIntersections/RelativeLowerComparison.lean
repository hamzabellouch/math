import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeEligible

namespace OAI

/-! Strict lower-neighbor comparisons for the relative height. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativeMasks_ne_of_open_sign {P Q:Deligne M} (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1)
    (k:ℕ) (hs : relativeSign M U (pointedProfile M f P cutoff) k (.inl i) ≠ 0) :
    relativeSignMask M f U cutoff Q k ≠ relativeSignMask M f U cutoff P k := by
  intro heq
  have hP : (.inl i:S ⊕ Unit) ∈ Sum.inl '' P.val.1 := ⟨i,hi,rfl⟩
  have hQ : (.inl i:S ⊕ Unit) ∉ Sum.inl '' Q.val.1 := by
    rintro ⟨j,hj,he⟩
    exact hq (Sum.inl.inj he ▸ hj)
  have hz := congrFun heq (toLex (.inl i))
  simp only [relativeSignMask,ofLex_toLex,hP,hQ,↓reduceIte] at hz
  exact hs hz.symm

lemma relativeLower_ineligible_le {P Q:Deligne M} (h:Q<P)
    (ha:∀i∈P.val.1,i∉Q.val.1→¬RelativeEligible M f U cutoff P Q i) :
    relativeHeight M f U cutoff P ≤ relativeHeight M f U cutoff Q := by
  by_cases hsome : ∃ i ∈ P.val.1, i ∉ Q.val.1 ∧ ∃ k,
      0 < pointedProfile M f P cutoff k (.inl i) ∨
      0 < pointedProfile M f Q cutoff k (.inl i)
  · apply le_of_lt
    apply (relativeHeight_lt_iff M f U cutoff P Q).mpr
    refine ⟨relativeLowerLevel M f cutoff P Q,
      fun d hd => (relativeBlock_eq_above_lower M f U cutoff h.le hd).symm,?_⟩
    let H := relativeLowerLevel M f cutoff P Q
    by_cases hv : pointedProfile M f Q cutoff H = pointedProfile M f P cutoff H
    · have hsEq := relativeSign_eq_at_lower_tie M f U cutoff h.le hv
      have hs (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1) :
          relativeSign M U (pointedProfile M f P cutoff) H (.inl i) ≤ 0 := by
        by_cases hz : pointedProfile M f P cutoff H (.inl i) = 0
        · simp only [relativeSign,hz,↓reduceIte,le_refl]
        · have hp := lt_of_le_of_ne (pointedCosetVector_nonneg M f P (cutoff+H) (.inl i)) (Ne.symm hz)
          have he : relativePeak M f cutoff P i = H := le_antisymm
            (relativePeak_le_lowerLevel M f cutoff P Q i hi hq).1
            (relativePeak_bound M f cutoff P i H hz)
          rw [relative_ineligible_tie_sign M f U cutoff i hi hq (ha i hi hq) he hv hp]
          norm_num
      have hm := relative_mask_upper_nonpos M f U cutoff h.le H
        (fun i => (hsEq i).symm) (fun i hi hq => by rw [hsEq]; exact hs i hi hq)
      obtain ⟨i,hi,hq,he,hp⟩ := relativeLowerLevel_prescribed_at_tie M f cutoff hsome hv
      have hsign := relative_ineligible_tie_sign M f U cutoff i hi hq (ha i hi hq) he hv hp
      have hn := relativeMasks_ne_of_open_sign M f U cutoff i hi hq H (by rw [hsign]; norm_num)
      exact relativeBlock_lt_of_mask M f U cutoff hv.symm (lt_of_le_of_ne hm (Ne.symm hn))
    · exact Prod.Lex.lt_iff.mpr (Or.inl (harmonic_sum_lt_of_lt _ _
        (relativeProfile_lower_comparison M f cutoff h.le H (relative_ineligible_top_ge M f U cutoff ha))
        (Ne.symm hv)))
  · have hz : ∀ i ∈ P.val.1, i ∉ Q.val.1 → ∀ k,
        pointedProfile M f P cutoff k (.inl i) = 0 ∧ pointedProfile M f Q cutoff k (.inl i) = 0 := by
      intro i hi hq k
      constructor
      · exact le_antisymm (le_of_not_gt (fun hp => hsome ⟨i,hi,hq,k,Or.inl hp⟩))
          (pointedCosetVector_nonneg M f P _ _)
      · exact le_antisymm (le_of_not_gt (fun hp => hsome ⟨i,hi,hq,k,Or.inr hp⟩))
          (pointedCosetVector_nonneg M f Q _ _)
    exact (relativeHeight_eq_of_opened_zero M f U cutoff h.le hz).symm.le

/-- A descending lower face opens at least one eligible color. -/
theorem relativeLower_descending_has_eligible {P Q:Deligne M} (h:Q<P)
    (he:relativeHeight M f U cutoff Q < relativeHeight M f U cutoff P) :
    ∃ i, RelativeEligible M f U cutoff P Q i := by
  by_contra hn
  exact (not_lt_of_ge (relativeLower_ineligible_le M f U cutoff h
    (fun i _ _ hi => hn ⟨i,hi⟩))) he

/-- Opening only eligible colors strictly decreases height. -/
theorem relativeLower_eligible_descending {P Q:Deligne M} (h:Q<P)
    (ha:∀i∈P.val.1,i∉Q.val.1→RelativeEligible M f U cutoff P Q i) :
    relativeHeight M f U cutoff Q < relativeHeight M f U cutoff P := by
  have hsome : ∃ i ∈ P.val.1, i ∉ Q.val.1 ∧ ∃ k,
      0 < pointedProfile M f P cutoff k (.inl i) ∨
      0 < pointedProfile M f Q cutoff k (.inl i) := by
    obtain ⟨i,hi,hq⟩ := Set.exists_of_ssubset (deligne_lt_type M h)
    exact ⟨i,hi,hq,relativePeak M f cutoff P i,Or.inl (relativeEligible_positive M f U cutoff (ha i hi hq))⟩
  apply (relativeHeight_lt_iff M f U cutoff Q P).mpr
  refine ⟨relativeLowerLevel M f cutoff P Q,
    fun d hd => relativeBlock_eq_above_lower M f U cutoff h.le hd,?_⟩
  let H := relativeLowerLevel M f cutoff P Q
  by_cases hv : pointedProfile M f Q cutoff H = pointedProfile M f P cutoff H
  · have hsEq := relativeSign_eq_at_lower_tie M f U cutoff h.le hv
    have hs (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1) :
        0 ≤ relativeSign M U (pointedProfile M f P cutoff) H (.inl i) := by
      rcases eq_or_lt_of_le (relativePeak_le_lowerLevel M f cutoff P Q i hi hq).1 with he|he
      · rw [relative_eligible_tie_sign M f U cutoff i (ha i hi hq) he hv]
        norm_num
      · have hz : pointedProfile M f P cutoff H (.inl i) = 0 := relativePeak_above M f cutoff P i he
        simp only [relativeSign,hz,↓reduceIte,le_refl]
    have hm := relative_mask_upper_nonneg M f U cutoff h.le H
      (fun i => (hsEq i).symm) (fun i hi hq => by rw [hsEq]; exact hs i hi hq)
    obtain ⟨i,hi,hq,he,_⟩ := relativeLowerLevel_prescribed_at_tie M f cutoff hsome hv
    have hsign := relative_eligible_tie_sign M f U cutoff i (ha i hi hq) he hv
    have hn := relativeMasks_ne_of_open_sign M f U cutoff i hi hq H (by rw [hsign]; norm_num)
    exact relativeBlock_lt_of_mask M f U cutoff hv (lt_of_le_of_ne hm hn)
  · exact Prod.Lex.lt_iff.mpr (Or.inl (harmonic_sum_lt_of_lt _ _
      (relativeProfile_lower_comparison_rev M f cutoff h.le H (relative_eligible_top_le M f U cutoff ha)) hv))

end HarmonicArtin.ParabolicIntersections

end OAI
