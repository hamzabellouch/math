import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativePeaks
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeUpperComparison

namespace OAI

/-! The highest changed level on a lower edge, including invisible opened colors. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativeLowerLevel_attained (P Q:Deligne M)
    (hsome : ∃ i ∈ P.val.1, i ∉ Q.val.1 ∧ ∃ k,
      0 < pointedProfile M f P cutoff k (.inl i) ∨
      0 < pointedProfile M f Q cutoff k (.inl i)) :
    ∃ i ∈ P.val.1, i ∉ Q.val.1 ∧
      (0 < pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q) (.inl i) ∨
       0 < pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q) (.inl i)) := by
  by_cases hz : relativeLowerLevel M f cutoff P Q = 0
  · obtain ⟨i,hi,hq,k,hk⟩ := hsome
    have hb := relativePeak_le_lowerLevel M f cutoff P Q i hi hq
    have hk0 : k = 0 := by
      rcases hk with hk|hk
      · exact Nat.eq_zero_of_le_zero (hz ▸ (relativePeak_bound M f cutoff P i k (ne_of_gt hk)).trans hb.1)
      · exact Nat.eq_zero_of_le_zero (hz ▸ (relativePeak_bound M f cutoff Q i k (ne_of_gt hk)).trans hb.2)
    exact ⟨i,hi,hq,by simpa only [hz,hk0] using hk⟩
  · obtain ⟨j,hj,hq,_⟩ := hsome
    have hn : (P.val.1.toFinset \ Q.val.1.toFinset).Nonempty := ⟨j,by simp [hj,hq]⟩
    obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup _ hn
      (fun i => max (relativePeak M f cutoff P i) (relativePeak M f cutoff Q i))
    have hip : i ∈ P.val.1 := Set.mem_toFinset.mp (Finset.mem_sdiff.mp hi).1
    have hiq : i ∉ Q.val.1 := fun hh => (Finset.mem_sdiff.mp hi).2 (Set.mem_toFinset.mpr hh)
    refine ⟨i,hip,hiq,?_⟩
    change relativeLowerLevel M f cutoff P Q = _ at he
    by_cases hle : relativePeak M f cutoff Q i ≤ relativePeak M f cutoff P i
    · have hh := he.trans (max_eq_left hle)
      have hp : 0 < relativePeak M f cutoff P i := Nat.pos_of_ne_zero (fun hh0 => hz (hh.trans hh0))
      rw [hh]
      exact Or.inl (lt_of_le_of_ne (pointedCosetVector_nonneg M f P _ _)
        (Ne.symm (relativePeak_nonzero_of_pos M f cutoff P i hp)))
    · have hh := he.trans (max_eq_right (lt_of_not_ge hle).le)
      have hp : 0 < relativePeak M f cutoff Q i := Nat.pos_of_ne_zero (fun hh0 => hz (hh.trans hh0))
      rw [hh]
      exact Or.inr (lt_of_le_of_ne (pointedCosetVector_nonneg M f Q _ _)
        (Ne.symm (relativePeak_nonzero_of_pos M f cutoff Q i hp)))

lemma relativeBlock_eq_above_lower {P Q:Deligne M} (h:Q≤P) {k:ℕ}
    (hk:relativeLowerLevel M f cutoff P Q<k) :
    relativeBlock M f U cutoff Q k=relativeBlock M f U cutoff P k := by
  have hv := relativeProfile_eq_above_lower M f cutoff h hk
  have hs (i:S ⊕ Unit) : relativeSign M U (pointedProfile M f Q cutoff) k i =
      relativeSign M U (pointedProfile M f P cutoff) k i :=
    relativeSign_congr_above M U _ _ k
      (fun d hd => relativeProfile_eq_above_lower M f cutoff h (hk.trans_le hd)) i
  have hm : relativeSignMask M f U cutoff Q k = relativeSignMask M f U cutoff P k := by
    funext i
    unfold relativeSignMask
    by_cases hq : ofLex i ∈ Sum.inl '' Q.val.1
    · simp only [hq,Set.image_mono h.1 hq,↓reduceIte,hs]
    · by_cases hp : ofLex i ∈ Sum.inl '' P.val.1
      · obtain ⟨j,hj,he⟩ := hp
        have hjq : j ∉ Q.val.1 := fun hh => hq ⟨j,hh,he⟩
        have hz := relativePeak_above M f cutoff P j
          ((relativePeak_le_lowerLevel M f cutoff P Q j hj hjq).1.trans_lt hk)
        have hsign : relativeSign M U (pointedProfile M f P cutoff) k (.inl j) = 0 := by
          simp only [relativeSign,hz,↓reduceIte]
        simp only [hs,←he,hsign,ite_self]
      · simp only [hq,hp,↓reduceIte]
  unfold relativeBlock
  have hsum : pointedCosetSum M f Q (cutoff+k) = pointedCosetSum M f P (cutoff+k) :=
    congrArg (fun v:S ⊕ Unit → ℝ => ∑ i,v i) hv
  rw [hsum,hv,hm]

lemma relativeHeight_eq_of_opened_zero {P Q:Deligne M} (h:Q≤P)
    (hz : ∀ i ∈ P.val.1, i ∉ Q.val.1 → ∀ k,
      pointedProfile M f P cutoff k (.inl i) = 0 ∧ pointedProfile M f Q cutoff k (.inl i) = 0) :
    relativeHeight M f U cutoff Q = relativeHeight M f U cutoff P := by
  have hv (k:ℕ) : pointedProfile M f Q cutoff k = pointedProfile M f P cutoff k :=
    relativeProfile_eq_of_lower_open M f cutoff h k (fun i hi hq => (hz i hi hq k).2.trans (hz i hi hq k).1.symm)
  apply relativeHeight_eq_of_blocks M f U cutoff
  intro k
  have hs (i:S ⊕ Unit) := relativeSign_congr_above M U _ _ k (fun d _ => hv d) i
  have hm : relativeSignMask M f U cutoff Q k = relativeSignMask M f U cutoff P k := by
    funext i
    unfold relativeSignMask
    rw [hs]
    by_cases hq : ofLex i ∈ Sum.inl '' Q.val.1
    · simp only [hq,Set.image_mono h.1 hq,↓reduceIte]
    · by_cases hp : ofLex i ∈ Sum.inl '' P.val.1
      · obtain ⟨j,hj,he⟩ := hp
        have hjq : j ∉ Q.val.1 := fun hh => hq ⟨j,hh,he⟩
        have hsign : relativeSign M U (pointedProfile M f P cutoff) k (.inl j) = 0 := by
          simp only [relativeSign,(hz j hj hjq k).1,↓reduceIte]
        simp only [←he,hsign,ite_self]
      · simp only [hq,hp,↓reduceIte]
  unfold relativeBlock
  have hsum : pointedCosetSum M f Q (cutoff+k) = pointedCosetSum M f P (cutoff+k) :=
    congrArg (fun v:S ⊕ Unit → ℝ => ∑ i,v i) (hv k)
  rw [hsum,hv,hm]

end HarmonicArtin.ParabolicIntersections

end OAI
