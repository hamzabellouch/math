import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeUpperBasics

namespace OAI

/-! Active-color rows and full sign masks at an upper comparison level. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

def relativeColorActive (P : Deligne M) (i : S) : Prop :=
  relativeActive (framedCartan M) U (pointedProfile M f P cutoff) (.inl i)

lemma relative_active_incident (P : Deligne M) (i : S)
    (ha : relativeColorActive M f U cutoff P i) :
    levelIncident (framedCartan M) (pointedProfile M f P cutoff)
      (relativeIncidence M f cutoff P i) (.inl i) := by
  by_contra hn
  have hz := relative_no_incidence M f U cutoff hn
  rcases ha with hp | ⟨_,hp,_⟩
  · exact (ne_of_gt hp) hz.2.1
  · exact (ne_of_gt hp) hz.1

lemma relative_active_sign (P : Deligne M) (i : S)
    (ha : relativeColorActive M f U cutoff P i)
    (hr : (framedCartan M *ᵥ pointedProfile M f P cutoff
      (relativeIncidence M f cutoff P i)) (.inl i) = 0) :
    relativeSign M U (pointedProfile M f P cutoff) (relativeIncidence M f cutoff P i) (.inl i) = -1 := by
  change 0 < (framedCartan M *ᵥ pointedProfile M f P cutoff (relativeIncidence M f cutoff P i)) (.inl i) ∨
    (framedCartan M *ᵥ pointedProfile M f P cutoff (relativeIncidence M f cutoff P i)) (.inl i) = 0 ∧
    0 < pointedProfile M f P cutoff (relativeIncidence M f cutoff P i) (.inl i) ∧
    ¬relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff)
      (relativeIncidence M f cutoff P i) (.inl i) at ha
  rcases ha with hp | ⟨_,hp,hn⟩
  · exact ((ne_of_gt hp) hr).elim
  · change 0 < pointedProfile M f P cutoff (relativeIncidence M f cutoff P i) (.inl i) at hp
    change ¬relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff)
      (relativeIncidence M f cutoff P i) (.inl i) at hn
    simp only [relativeSign, ne_of_gt hp, hn, ↓reduceIte]

lemma relative_inactive_sign (P : Deligne M) (i : S) (k : ℕ)
    (ha : ¬relativeColorActive M f U cutoff P i)
    (hk : k = relativeIncidence M f cutoff P i)
    (hi : levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i))
    (hr : (framedCartan M *ᵥ pointedProfile M f P cutoff k) (.inl i) = 0) :
    relativeSign M U (pointedProfile M f P cutoff) k (.inl i) = 1 := by
  have hp : 0 < pointedProfile M f P cutoff k (.inl i) := by
    rcases hi with hp | ⟨j,hij,hj⟩
    · exact hp
    · exact harmonic_positive_neighbor_at (framedCartan M) (framedCartan_off M) _
        (pointedCosetVector_nonneg M f P (cutoff+k)) (le_of_eq hr.symm) hij hj
  have hs : relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff) k (.inl i) := by
    by_contra hn
    apply ha
    change relativeActive (framedCartan M) U (pointedProfile M f P cutoff) (.inl i)
    change 0 < (framedCartan M *ᵥ pointedProfile M f P cutoff (relativeIncidence M f cutoff P i)) (.inl i) ∨
      (framedCartan M *ᵥ pointedProfile M f P cutoff (relativeIncidence M f cutoff P i)) (.inl i) = 0 ∧
      0 < pointedProfile M f P cutoff (relativeIncidence M f cutoff P i) (.inl i) ∧
      ¬relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff)
        (relativeIncidence M f cutoff P i) (.inl i)
    rw [←hk]
    exact Or.inr ⟨hr,hp,hn⟩
  simp only [relativeSign, ne_of_gt hp, hs, ↓reduceIte]

lemma relative_upper_inactive_rows (P R : Deligne M)
    (ha : ∀ i ∈ R.val.1, i ∉ P.val.1 → ¬relativeColorActive M f U cutoff P i)
    (i : S) (hi : i ∈ R.val.1) (ht : i ∉ P.val.1) :
    (framedCartan M *ᵥ pointedProfile M f P cutoff (relativeUpperLevel M f cutoff P R)) (.inl i) ≤ 0 := by
  rcases eq_or_lt_of_le (relativeIncidence_le_upperLevel M f cutoff P R i hi ht) with he | he
  · have hn : ¬0 < (framedCartan M *ᵥ pointedProfile M f P cutoff
        (relativeIncidence M f cutoff P i)) (.inl i) := fun hp => ha i hi ht (Or.inl hp)
    rw [←he]
    exact le_of_not_gt hn
  · rw [(relative_no_incidence M f U cutoff (relative_above_incidence M f cutoff he)).2.1]

lemma relative_upper_active_rows (P R : Deligne M)
    (ha : ∀ i ∈ R.val.1, i ∉ P.val.1 → relativeColorActive M f U cutoff P i)
    (i : S) (hi : i ∈ R.val.1) (ht : i ∉ P.val.1) :
    0 ≤ (framedCartan M *ᵥ pointedProfile M f P cutoff (relativeUpperLevel M f cutoff P R)) (.inl i) := by
  rcases eq_or_lt_of_le (relativeIncidence_le_upperLevel M f cutoff P R i hi ht) with he | he
  · have hh := ha i hi ht
    have hrow : 0 ≤ (framedCartan M *ᵥ pointedProfile M f P cutoff
        (relativeIncidence M f cutoff P i)) (.inl i) := by
      rcases hh with hp | ⟨hz, _⟩
      · exact hp.le
      · exact hz.ge
    simpa only [he] using hrow
  · rw [(relative_no_incidence M f U cutoff (relative_above_incidence M f cutoff he)).2.1]

lemma relativeUpperLevel_incident (P R : Deligne M)
    (hsome : ∃ i ∈ R.val.1, i ∉ P.val.1 ∧ ∃ k,
      levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i)) :
    ∃ i ∈ R.val.1, i ∉ P.val.1 ∧
      levelIncident (framedCartan M) (pointedProfile M f P cutoff)
        (relativeUpperLevel M f cutoff P R) (.inl i) := by
  by_cases hk : relativeUpperLevel M f cutoff P R = 0
  · obtain ⟨i,hi,ht,k,hki⟩ := hsome
    have hle := (levelIncident_le _ _ hki).trans (relativeIncidence_le_upperLevel M f cutoff P R i hi ht)
    have he : k = relativeUpperLevel M f cutoff P R := by omega
    exact ⟨i,hi,ht,he ▸ hki⟩
  · obtain ⟨i,hi,ht,k,hki⟩ := hsome
    obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup
      (R.val.1.toFinset \ P.val.1.toFinset) ⟨i,by simp [hi,ht]⟩ (relativeIncidence M f cutoff P)
    have hjR : j ∈ R.val.1 := Set.mem_toFinset.mp (Finset.mem_sdiff.mp hj).1
    have hjP : j ∉ P.val.1 := fun h => (Finset.mem_sdiff.mp hj).2 (Set.mem_toFinset.mpr h)
    refine ⟨j,hjR,hjP,?_⟩
    have hex : ∃ k, levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl j) := by
      by_contra hn
      have hempty : incidenceIndices (framedCartan M) (pointedProfile M f P cutoff) (.inl j) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro d hd
        exact hn ⟨d,(Finset.mem_filter.mp hd).2⟩
      have hz : relativeIncidence M f cutoff P j = 0 := by
        simp only [relativeIncidence, incidenceLevel, hempty, Finset.sup_empty, bot_eq_zero]
      exact hk (he.trans hz)
    rw [show relativeUpperLevel M f cutoff P R = relativeIncidence M f cutoff P j from he]
    exact incidenceLevel_incident _ _ _ hex

lemma relative_sign_upper_tie {P R : Deligne M} (h : P ≤ R)
    (hv : pointedProfile M f R cutoff (relativeUpperLevel M f cutoff P R) =
      pointedProfile M f P cutoff (relativeUpperLevel M f cutoff P R)) (i : S ⊕ Unit) :
    relativeSign M U (pointedProfile M f R cutoff) (relativeUpperLevel M f cutoff P R) i =
      relativeSign M U (pointedProfile M f P cutoff) (relativeUpperLevel M f cutoff P R) i := by
  apply relativeSign_congr_above M U
  intro d hd
  rcases eq_or_lt_of_le hd with rfl | hd
  · exact hv
  · exact relativeProfile_eq_above_upper M f cutoff h hd

lemma relative_mask_upper_nonneg {P R : Deligne M} (h : P ≤ R) (k : ℕ)
    (hs : ∀ i, relativeSign M U (pointedProfile M f R cutoff) k i =
      relativeSign M U (pointedProfile M f P cutoff) k i)
    (hn : ∀ i ∈ R.val.1, i ∉ P.val.1 →
      0 ≤ relativeSign M U (pointedProfile M f P cutoff) k (.inl i)) :
    relativeSignMask M f U cutoff P k ≤ relativeSignMask M f U cutoff R k := by
  intro i
  unfold relativeSignMask
  rw [hs]
  by_cases hp : ofLex i ∈ Sum.inl '' P.val.1
  · simp only [hp, Set.image_mono h.1 hp, ↓reduceIte, le_refl]
  · by_cases hr : ofLex i ∈ Sum.inl '' R.val.1
    · obtain ⟨j,hj,he⟩ := hr
      have hnp : j ∉ P.val.1 := fun hh => hp ⟨j,hh,he⟩
      simp only [hp, show ofLex i ∈ Sum.inl '' R.val.1 from ⟨j,hj,he⟩, ↓reduceIte]
      rw [←he]
      exact hn j hj hnp
    · simp only [hp, hr, ↓reduceIte, le_refl]

lemma relative_mask_upper_nonpos {P R : Deligne M} (h : P ≤ R) (k : ℕ)
    (hs : ∀ i, relativeSign M U (pointedProfile M f R cutoff) k i =
      relativeSign M U (pointedProfile M f P cutoff) k i)
    (hn : ∀ i ∈ R.val.1, i ∉ P.val.1 →
      relativeSign M U (pointedProfile M f P cutoff) k (.inl i) ≤ 0) :
    relativeSignMask M f U cutoff R k ≤ relativeSignMask M f U cutoff P k := by
  intro i
  unfold relativeSignMask
  rw [hs]
  by_cases hp : ofLex i ∈ Sum.inl '' P.val.1
  · simp only [hp, Set.image_mono h.1 hp, ↓reduceIte, le_refl]
  · by_cases hr : ofLex i ∈ Sum.inl '' R.val.1
    · obtain ⟨j,hj,he⟩ := hr
      have hnp : j ∉ P.val.1 := fun hh => hp ⟨j,hh,he⟩
      simp only [hp, show ofLex i ∈ Sum.inl '' R.val.1 from ⟨j,hj,he⟩, ↓reduceIte]
      rw [←he]
      exact hn j hj hnp
    · simp only [hp, hr, ↓reduceIte, le_refl]

lemma relativeBlock_lt_of_mask {P R : Deligne M} {k : ℕ}
    (hv : pointedProfile M f P cutoff k = pointedProfile M f R cutoff k)
    (hm : relativeSignMask M f U cutoff P k < relativeSignMask M f U cutoff R k) :
    relativeBlock M f U cutoff P k < relativeBlock M f U cutoff R k := by
  unfold relativeBlock
  apply Prod.Lex.lt_iff.mpr
  refine Or.inr ⟨congrArg (fun v : S ⊕ Unit → ℝ => ∑ i, v i) hv, ?_⟩
  exact Prod.Lex.lt_iff.mpr (Or.inr ⟨congrArg toLex hv, Pi.toLex_strictMono hm⟩)

end HarmonicArtin.ParabolicIntersections

end OAI
