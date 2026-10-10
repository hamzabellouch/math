import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeUpperSigns

namespace OAI

/-! Strict upper-neighbor comparisons for the relative height. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

lemma relativeHeight_eq_of_blocks {P R : Deligne M}
    (he : ∀ k, relativeBlock M f U cutoff P k = relativeBlock M f U cutoff R k) :
    relativeHeight M f U cutoff P = relativeHeight M f U cutoff R := by
  apply congrArg toColex
  ext k
  change relativeBlockRank M f U cutoff _ = relativeBlockRank M f U cutoff _
  rw [he]

lemma relativeHeight_eq_of_new_invisible {P R : Deligne M} (h : P ≤ R)
    (hn : ∀ i ∈ R.val.1, i ∉ P.val.1 → ∀ k,
      ¬levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i)) :
    relativeHeight M f U cutoff R = relativeHeight M f U cutoff P := by
  have hv (k : ℕ) : pointedProfile M f R cutoff k = pointedProfile M f P cutoff k := by
    apply pointedCosetVector_eq_of_upper_rows M f h (cutoff+k)
    intro i hi ht
    exact (relative_no_incidence M f U cutoff (hn i hi ht k)).2.1
  have hs (k : ℕ) (i : S ⊕ Unit) := relativeSign_congr_above M U
    (pointedProfile M f R cutoff) (pointedProfile M f P cutoff) k (fun d _ => hv d) i
  apply relativeHeight_eq_of_blocks M f U cutoff
  intro k
  have hm : relativeSignMask M f U cutoff R k = relativeSignMask M f U cutoff P k := by
    funext i
    unfold relativeSignMask
    rw [hs]
    by_cases hp : ofLex i ∈ Sum.inl '' P.val.1
    · simp only [hp, Set.image_mono h.1 hp, ↓reduceIte]
    · by_cases hr : ofLex i ∈ Sum.inl '' R.val.1
      · obtain ⟨j,hj,he⟩ := hr
        have hjp : j ∉ P.val.1 := fun hh => hp ⟨j,hh,he⟩
        have hz := (relative_no_incidence M f U cutoff (hn j hj hjp k)).2.2
        simp only [←he, hz, ite_self]
      · simp only [hp, hr, ↓reduceIte]
  unfold relativeBlock
  have hsum : pointedCosetSum M f R (cutoff+k) = pointedCosetSum M f P (cutoff+k) :=
    congrArg (fun v : S ⊕ Unit → ℝ => ∑ i, v i) (hv k)
  rw [hsum, hv, hm]

lemma relativeUpper_inactive_le {P R : Deligne M} (h : P < R)
    (ha : ∀ i ∈ R.val.1, i ∉ P.val.1 → ¬relativeColorActive M f U cutoff P i) :
    relativeHeight M f U cutoff P ≤ relativeHeight M f U cutoff R := by
  by_cases hsome : ∃ i ∈ R.val.1, i ∉ P.val.1 ∧ ∃ k,
      levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i)
  · apply le_of_lt
    apply (relativeHeight_lt_iff M f U cutoff P R).mpr
    refine ⟨relativeUpperLevel M f cutoff P R,
      fun d hd => (relativeBlock_eq_above_upper M f U cutoff h.le hd).symm, ?_⟩
    let H := relativeUpperLevel M f cutoff P R
    by_cases hv : pointedProfile M f R cutoff H = pointedProfile M f P cutoff H
    · have hr (i : S) (hi : i ∈ R.val.1) :
          (framedCartan M *ᵥ pointedProfile M f P cutoff H) (.inl i) = 0 := by
        rw [←hv]
        exact pointedCosetVector_harmonic M f R (cutoff+H) ⟨.inl i,⟨i,hi,rfl⟩⟩
      have hs (i : S) (hi : i ∈ R.val.1) (ht : i ∉ P.val.1) :
          0 ≤ relativeSign M U (pointedProfile M f P cutoff) H (.inl i) := by
        by_cases hn : levelIncident (framedCartan M) (pointedProfile M f P cutoff) H (.inl i)
        · have he : H = relativeIncidence M f cutoff P i := le_antisymm
            (levelIncident_le _ _ hn) (relativeIncidence_le_upperLevel M f cutoff P R i hi ht)
          rw [relative_inactive_sign M f U cutoff P i H (ha i hi ht) he hn (hr i hi)]
          norm_num
        · rw [(relative_no_incidence M f U cutoff hn).2.2]
      have hsEq := relative_sign_upper_tie M f U cutoff h.le hv
      have hm := relative_mask_upper_nonneg M f U cutoff h.le H hsEq hs
      have hne : relativeSignMask M f U cutoff P H ≠ relativeSignMask M f U cutoff R H := by
        intro heq
        obtain ⟨i,hi,ht,hin⟩ := relativeUpperLevel_incident M f cutoff P R hsome
        have hiP : (.inl i : S ⊕ Unit) ∉ Sum.inl '' P.val.1 := by
          rintro ⟨j,hj,he⟩
          exact ht (Sum.inl.inj he ▸ hj)
        have hiR : (.inl i : S ⊕ Unit) ∈ Sum.inl '' R.val.1 := ⟨i,hi,rfl⟩
        have he : H = relativeIncidence M f cutoff P i := le_antisymm
          (levelIncident_le _ _ hin) (relativeIncidence_le_upperLevel M f cutoff P R i hi ht)
        have hz := congrFun heq (toLex (.inl i))
        simp only [relativeSignMask, ofLex_toLex, hiP, hiR, ↓reduceIte] at hz
        have hsi : relativeSign M U (pointedProfile M f R cutoff) H (.inl i) =
            relativeSign M U (pointedProfile M f P cutoff) H (.inl i) := hsEq _
        rw [hsi, relative_inactive_sign M f U cutoff P i H (ha i hi ht) he hin (hr i hi)] at hz
        norm_num at hz
      exact relativeBlock_lt_of_mask M f U cutoff hv.symm (lt_of_le_of_ne hm hne)
    · have hle := pointedCosetVector_upper_monotone_int M f h.le (cutoff+H)
        (relative_upper_inactive_rows M f U cutoff P R ha)
      exact Prod.Lex.lt_iff.mpr (Or.inl (harmonic_sum_lt_of_lt _ _ hle (Ne.symm hv)))
  · have hn : ∀ i ∈ R.val.1, i ∉ P.val.1 → ∀ k,
        ¬levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i) := by
      intro i hi ht k hin
      exact hsome ⟨i,hi,ht,k,hin⟩
    exact (relativeHeight_eq_of_new_invisible M f U cutoff h.le hn).symm.le

/-- Every descending upper neighbor adds an active color. -/
theorem relativeUpper_descending_has_active {P R : Deligne M} (h : P < R)
    (he : relativeHeight M f U cutoff R < relativeHeight M f U cutoff P) :
    ∃ i ∈ R.val.1, i ∉ P.val.1 ∧ relativeColorActive M f U cutoff P i := by
  by_contra hn
  have hle := relativeUpper_inactive_le M f U cutoff h
    (fun i hi ht ha => hn ⟨i,hi,ht,ha⟩)
  exact (not_lt_of_ge hle) he

/-- Closing a nonempty set of active colors strictly decreases the height. -/
theorem relativeUpper_active_descending {P R : Deligne M} (h : P < R)
    (ha : ∀ i ∈ R.val.1, i ∉ P.val.1 → relativeColorActive M f U cutoff P i) :
    relativeHeight M f U cutoff R < relativeHeight M f U cutoff P := by
  apply (relativeHeight_lt_iff M f U cutoff R P).mpr
  refine ⟨relativeUpperLevel M f cutoff P R,
    fun d hd => relativeBlock_eq_above_upper M f U cutoff h.le hd, ?_⟩
  let H := relativeUpperLevel M f cutoff P R
  by_cases hv : pointedProfile M f R cutoff H = pointedProfile M f P cutoff H
  · have hr (i : S) (hi : i ∈ R.val.1) :
        (framedCartan M *ᵥ pointedProfile M f P cutoff H) (.inl i) = 0 := by
      rw [←hv]
      exact pointedCosetVector_harmonic M f R (cutoff+H) ⟨.inl i,⟨i,hi,rfl⟩⟩
    have hs (i : S) (hi : i ∈ R.val.1) (ht : i ∉ P.val.1) :
        relativeSign M U (pointedProfile M f P cutoff) H (.inl i) ≤ 0 := by
      rcases eq_or_lt_of_le (relativeIncidence_le_upperLevel M f cutoff P R i hi ht) with he | he
      · have hh := relative_active_sign M f U cutoff P i (ha i hi ht) (by rw [he]; exact hr i hi)
        rw [he] at hh
        rw [hh]
        norm_num
      · rw [(relative_no_incidence M f U cutoff (relative_above_incidence M f cutoff he)).2.2]
    have hsEq := relative_sign_upper_tie M f U cutoff h.le hv
    have hm := relative_mask_upper_nonpos M f U cutoff h.le H hsEq hs
    have hsome : ∃ i ∈ R.val.1, i ∉ P.val.1 ∧ ∃ k,
        levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i) := by
      obtain ⟨i,hi,ht⟩ := Set.exists_of_ssubset (deligne_lt_type M h)
      exact ⟨i,hi,ht,relativeIncidence M f cutoff P i,relative_active_incident M f U cutoff P i (ha i hi ht)⟩
    have hne : relativeSignMask M f U cutoff R H ≠ relativeSignMask M f U cutoff P H := by
      intro heq
      obtain ⟨i,hi,ht,hin⟩ := relativeUpperLevel_incident M f cutoff P R hsome
      have hiP : (.inl i : S ⊕ Unit) ∉ Sum.inl '' P.val.1 := by
        rintro ⟨j,hj,he⟩
        exact ht (Sum.inl.inj he ▸ hj)
      have hiR : (.inl i : S ⊕ Unit) ∈ Sum.inl '' R.val.1 := ⟨i,hi,rfl⟩
      have he : relativeIncidence M f cutoff P i = H := le_antisymm
        (relativeIncidence_le_upperLevel M f cutoff P R i hi ht) (levelIncident_le _ _ hin)
      have hsign := relative_active_sign M f U cutoff P i (ha i hi ht) (by rw [he]; exact hr i hi)
      rw [he] at hsign
      have hz := congrFun heq (toLex (.inl i))
      simp only [relativeSignMask, ofLex_toLex, hiP, hiR, ↓reduceIte] at hz
      have hsi : relativeSign M U (pointedProfile M f R cutoff) H (.inl i) =
          relativeSign M U (pointedProfile M f P cutoff) H (.inl i) := hsEq _
      rw [hsi, hsign] at hz
      norm_num at hz
    exact relativeBlock_lt_of_mask M f U cutoff hv (lt_of_le_of_ne hm hne)
  · have hle := pointedCosetVector_upper_antitone_int M f h.le (cutoff+H)
      (relative_upper_active_rows M f U cutoff P R ha)
    exact Prod.Lex.lt_iff.mpr (Or.inl (harmonic_sum_lt_of_lt _ _ hle hv))

end HarmonicArtin.ParabolicIntersections

end OAI
