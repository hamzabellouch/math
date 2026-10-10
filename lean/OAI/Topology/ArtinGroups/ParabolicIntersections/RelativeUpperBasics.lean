import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeActive
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedRows
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueActive

namespace OAI

/-! Highest-incidence comparisons for upper edges of the relative filtration. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

omit [LinearOrder S] in
lemma relativeSign_congr_above (p r : ℕ →₀ (S ⊕ Unit → ℝ)) (k : ℕ)
    (he : ∀ d, k ≤ d → p d = r d) (i : S ⊕ Unit) :
    relativeSign M U p k i = relativeSign M U r k i := by
  have hk := he k le_rfl
  have hs : relativePositiveSign (framedCartan M) U p k i ↔
      relativePositiveSign (framedCartan M) U r k i := by
    unfold relativePositiveSign
    simp only [hk]
    constructor
    · rintro ⟨I, hi, hU, hc, hr, hh⟩
      exact ⟨I, hi, hU, hc, hr, fun d hd j hj => by rw [←he d hd.le]; exact hh d hd j hj⟩
    · rintro ⟨I, hi, hU, hc, hr, hh⟩
      exact ⟨I, hi, hU, hc, hr, fun d hd j hj => by rw [he d hd.le]; exact hh d hd j hj⟩
  simp only [relativeSign, hk, hs]

lemma relativeHeight_lt_iff (P R : Deligne M) :
    relativeHeight M f U cutoff P < relativeHeight M f U cutoff R ↔
      ∃ k, (∀ d, k < d → relativeBlock M f U cutoff P d = relativeBlock M f U cutoff R d) ∧
        relativeBlock M f U cutoff P k < relativeBlock M f U cutoff R k := by
  rw [Finsupp.Colex.lt_iff]
  constructor
  · rintro ⟨k, hk, hlt⟩
    refine ⟨k, fun d hd => ?_, (relativeBlockRank_lt_iff M f U cutoff
      (Or.inr ⟨P,k,rfl⟩) (Or.inr ⟨R,k,rfl⟩)).mp hlt⟩
    exact (relativeBlockRank_eq_iff M f U cutoff (Or.inr ⟨P,d,rfl⟩)
      (Or.inr ⟨R,d,rfl⟩)).mp (hk d hd)
  · rintro ⟨k, hk, hlt⟩
    exact ⟨k, fun d hd => congrArg (relativeBlockRank M f U cutoff) (hk d hd),
      (relativeBlockRank_lt_iff M f U cutoff (Or.inr ⟨P,k,rfl⟩)
        (Or.inr ⟨R,k,rfl⟩)).mpr hlt⟩

noncomputable def relativeIncidence (P : Deligne M) (i : S) : ℕ :=
  incidenceLevel (framedCartan M) (pointedProfile M f P cutoff) (.inl i)

lemma relative_no_incidence {P : Deligne M} {k : ℕ} {i : S}
    (hn : ¬levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i)) :
    pointedProfile M f P cutoff k (.inl i) = 0 ∧
    (framedCartan M *ᵥ pointedProfile M f P cutoff k) (.inl i) = 0 ∧
    relativeSign M U (pointedProfile M f P cutoff) k (.inl i) = 0 := by
  have hz : pointedProfile M f P cutoff k (.inl i) = 0 := le_antisymm
    (le_of_not_gt (fun h => hn (Or.inl h))) (pointedCosetVector_nonneg M f P _ _)
  refine ⟨hz, no_incidence_row_zero (framedCartan M) (framedCartan_off M) _
    (fun k i => pointedCosetVector_nonneg M f P (cutoff+k) i) hn, ?_⟩
  simp only [relativeSign, hz, ↓reduceIte]

lemma relative_above_incidence {P : Deligne M} {k : ℕ} {i : S}
    (h : relativeIncidence M f cutoff P i < k) :
    ¬levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i) :=
  fun hi => (not_le_of_gt h) (levelIncident_le _ _ hi)

noncomputable def relativeUpperLevel (P R : Deligne M) : ℕ :=
  (R.val.1.toFinset \ P.val.1.toFinset).sup (relativeIncidence M f cutoff P)

lemma relativeIncidence_le_upperLevel (P R : Deligne M) (i : S)
    (hi : i ∈ R.val.1) (ht : i ∉ P.val.1) :
    relativeIncidence M f cutoff P i ≤ relativeUpperLevel M f cutoff P R :=
  Finset.le_sup (f := relativeIncidence M f cutoff P) (by simp [hi, ht])

lemma relativeProfile_eq_above_upper {P R : Deligne M} (h : P ≤ R) {k : ℕ}
    (hk : relativeUpperLevel M f cutoff P R < k) :
    pointedProfile M f R cutoff k = pointedProfile M f P cutoff k := by
  apply pointedCosetVector_eq_of_upper_rows M f h (cutoff+k)
  intro i hi ht
  exact (relative_no_incidence M f ∅ cutoff (relative_above_incidence M f cutoff
    ((relativeIncidence_le_upperLevel M f cutoff P R i hi ht).trans_lt hk))).2.1

lemma relativeBlock_eq_above_upper {P R : Deligne M} (h : P ≤ R) {k : ℕ}
    (hk : relativeUpperLevel M f cutoff P R < k) :
    relativeBlock M f U cutoff R k = relativeBlock M f U cutoff P k := by
  have hv := relativeProfile_eq_above_upper M f cutoff h hk
  have hs (i : S ⊕ Unit) :
      relativeSign M U (pointedProfile M f R cutoff) k i =
        relativeSign M U (pointedProfile M f P cutoff) k i :=
    relativeSign_congr_above M U _ _ k
      (fun d hd => relativeProfile_eq_above_upper M f cutoff h (hk.trans_le hd)) i
  have hm : relativeSignMask M f U cutoff R k = relativeSignMask M f U cutoff P k := by
    funext i
    unfold relativeSignMask
    by_cases hp : ofLex i ∈ Sum.inl '' P.val.1
    · have hr := Set.image_mono h.1 hp
      simp only [hp, hr, ↓reduceIte, hs]
    · by_cases hr : ofLex i ∈ Sum.inl '' R.val.1
      · obtain ⟨j, hj, he⟩ := hr
        have hjp : j ∉ P.val.1 := fun h => hp ⟨j,h,he⟩
        have hz := (relative_no_incidence M f U cutoff (relative_above_incidence M f cutoff
          ((relativeIncidence_le_upperLevel M f cutoff P R j hj hjp).trans_lt hk))).2.2
        simp only [hs, ←he, hz, ite_self]
      · simp only [hp, hr, ↓reduceIte]
  unfold relativeBlock
  have hsum : pointedCosetSum M f R (cutoff+k) = pointedCosetSum M f P (cutoff+k) :=
    congrArg (fun v : S ⊕ Unit → ℝ => ∑ i, v i) hv
  rw [hsum, hv, hm]

end HarmonicArtin.ParabolicIntersections

end OAI
