import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeHeight

namespace OAI

/-! Visible and invisible sets along tied comparable vertices, §6.5 of paper 082-03. -/

namespace HarmonicArtin.ParabolicIntersections

open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

omit [LinearOrder S] in
lemma relativeSign_eq_zero_iff (p : ℕ →₀ (S ⊕ Unit → ℝ)) (k : ℕ) (i : S ⊕ Unit) :
    relativeSign M U p k i = 0 ↔ p k i = 0 := by
  unfold relativeSign
  split_ifs <;> simp_all

lemma relativeHeight_eq_profiles {P R : Deligne M}
    (he : relativeHeight M f U cutoff P = relativeHeight M f U cutoff R) (k : ℕ) :
    pointedProfile M f P cutoff k = pointedProfile M f R cutoff k := by
  have hb := relativeHeight_eq_blocks M f U cutoff he k
  have hv := congrArg (fun b : RelativeBlock S => (ofLex (ofLex b).2).1) hb
  exact congrArg ofLex hv

lemma relativeHeight_eq_masks {P R : Deligne M}
    (he : relativeHeight M f U cutoff P = relativeHeight M f U cutoff R) (k : ℕ) :
    relativeSignMask M f U cutoff P k = relativeSignMask M f U cutoff R k := by
  have hb := relativeHeight_eq_blocks M f U cutoff he k
  have hv := congrArg (fun b : RelativeBlock S => (ofLex (ofLex b).2).2) hb
  exact congrArg ofLex hv

/-- Absence of recorded incidence, restricted to the group currently acting. -/
def relativeInvisible (Y : Set S) (P : Deligne M) : Set S :=
  {i | i ∈ Y ∧ ∀ k, ¬levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i)}

def relativeVisible (Y : Set S) (P : Deligne M) : Set S :=
  P.val.1 \ relativeInvisible M f cutoff Y P

lemma relativeInvisible_eq_of_height_eq (Y : Set S) {P R : Deligne M}
    (he : relativeHeight M f U cutoff P = relativeHeight M f U cutoff R) :
    relativeInvisible M f cutoff Y P = relativeInvisible M f cutoff Y R := by
  ext i
  constructor
  · rintro ⟨hi, hh⟩
    refine ⟨hi, fun k => ?_⟩
    unfold levelIncident at *
    rw [← relativeHeight_eq_profiles M f U cutoff he k]
    exact hh k
  · rintro ⟨hi, hh⟩
    refine ⟨hi, fun k => ?_⟩
    unfold levelIncident at *
    rw [relativeHeight_eq_profiles M f U cutoff he k]
    exact hh k

/-- Each new closed color at a tied upper vertex has no recorded incidence. -/
lemma tied_new_color_invisible (Y : Set S) {P R : Deligne M}
    (hR : R.val.1 ⊆ Y)
    (he : relativeHeight M f U cutoff P = relativeHeight M f U cutoff R)
    (i : S) (hi : i ∈ R.val.1) (hn : i ∉ P.val.1) :
    i ∈ relativeInvisible M f cutoff Y R := by
  refine ⟨hR hi, ?_⟩
  intro k hinc
  have hm := congrFun (relativeHeight_eq_masks M f U cutoff he k) (toLex (.inl i))
  have hp : (.inl i : S ⊕ Unit) ∉ Sum.inl '' P.val.1 := by
    rintro ⟨j, hj, heq⟩
    exact hn (Sum.inl.inj heq ▸ hj)
  have hr : (.inl i : S ⊕ Unit) ∈ Sum.inl '' R.val.1 := ⟨i, hi, rfl⟩
  simp only [relativeSignMask, ofLex_toLex, hp, hr, ↓reduceIte] at hm
  have hz : pointedProfile M f R cutoff k (.inl i) = 0 :=
    (relativeSign_eq_zero_iff M U _ k _).mp hm.symm
  rcases hinc with hpos | ⟨j, hij, hj⟩
  · exact (ne_of_gt hpos) hz
  · have hrow : (framedCartan M *ᵥ pointedProfile M f R cutoff k) (.inl i) = 0 :=
      pointedCosetVector_harmonic M f R (cutoff + k) ⟨.inl i, hr⟩
    have hpos := harmonic_positive_neighbor_at (framedCartan M) (framedCartan_off M)
      _ (pointedCosetVector_nonneg M f R (cutoff + k)) (le_of_eq hrow.symm) hij hj
    exact (ne_of_gt hpos) hz

/-- The visible closed set is constant across a tied comparability edge. -/
lemma relativeVisible_eq_of_tie (Y : Set S) {P R : Deligne M} (hPR : P ≤ R)
    (hR : R.val.1 ⊆ Y)
    (he : relativeHeight M f U cutoff P = relativeHeight M f U cutoff R) :
    relativeVisible M f cutoff Y P = relativeVisible M f cutoff Y R := by
  have hK := relativeInvisible_eq_of_height_eq M f U cutoff Y he
  ext i
  constructor
  · rintro ⟨hi, hn⟩
    exact ⟨hPR.1 hi, by rwa [← hK]⟩
  · rintro ⟨hi, hn⟩
    have hp : i ∈ P.val.1 := by
      by_contra hp
      exact hn (tied_new_color_invisible M f U cutoff Y hR he i hi hp)
    exact ⟨hp, by rwa [hK]⟩

/-- A visible closed color is positive at some recorded level. -/
lemma relativeVisible_positive (Y : Set S) (P : Deligne M) (hP : P.val.1 ⊆ Y)
    (i : S) (hi : i ∈ relativeVisible M f cutoff Y P) :
    ∃ k, 0 < pointedProfile M f P cutoff k (.inl i) := by
  have hex : ∃ k, levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i) := by
    by_contra hh
    exact hi.2 ⟨hP hi.1, fun k hk => hh ⟨k, hk⟩⟩
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, ?_⟩
  rcases hk with hp | ⟨j, hij, hj⟩
  · exact hp
  · have hrow : (framedCartan M *ᵥ pointedProfile M f P cutoff k) (.inl i) = 0 :=
      pointedCosetVector_harmonic M f P (cutoff + k) ⟨.inl i, ⟨i, hi.1, rfl⟩⟩
    exact harmonic_positive_neighbor_at (framedCartan M) (framedCartan_off M) _
      (pointedCosetVector_nonneg M f P (cutoff + k)) (le_of_eq hrow.symm) hij hj

/-- Visible closed colors cannot be adjacent to any invisible color. -/
lemma relativeVisible_nonadjacent (Y : Set S) (P : Deligne M) (hP : P.val.1 ⊆ Y)
    (i j : S) (hi : i ∈ relativeInvisible M f cutoff Y P)
    (hj : j ∈ relativeVisible M f cutoff Y P) :
    ¬framedCartan M (.inl i) (.inl j) < 0 := by
  intro hij
  obtain ⟨k, hk⟩ := relativeVisible_positive M f cutoff Y P hP j hj
  exact hi.2 k (Or.inr ⟨.inl j, hij, hk⟩)

end HarmonicArtin.ParabolicIntersections

end OAI
