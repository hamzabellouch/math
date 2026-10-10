import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeLowerBasics

namespace OAI

/-! The eligible opened colors in a descending lower face. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

def RelativeEligible (P Q:Deligne M) (i:S) : Prop :=
  i∈P.val.1 ∧ i∉Q.val.1 ∧
  (∀d:ℕ,relativePeak M f cutoff P i<d→pointedProfile M f Q cutoff d (.inl i)=0) ∧
  (pointedProfile M f Q cutoff (relativePeak M f cutoff P i) (.inl i)<pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i) ∨
   pointedProfile M f Q cutoff (relativePeak M f cutoff P i) (.inl i)=pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i) ∧
     relativeSign M U (pointedProfile M f P cutoff) (relativePeak M f cutoff P i) (.inl i)=1)

lemma relative_ineligible_top_ge {P Q:Deligne M}
    (ha:∀i∈P.val.1,i∉Q.val.1→¬RelativeEligible M f U cutoff P Q i) :
    ∀i∈P.val.1,i∉Q.val.1→
      pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q) (.inl i)≤
        pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q) (.inl i) := by
  intro i hi hq
  have hb:=relativePeak_le_lowerLevel M f cutoff P Q i hi hq
  rcases eq_or_lt_of_le hb.1 with he|he
  · by_contra hn
    apply ha i hi hq
    refine ⟨hi,hq,?_,Or.inl ?_⟩
    · intro d hd
      exact relativePeak_above M f cutoff Q i (hb.2.trans_lt (he ▸ hd))
    · rw [he]
      exact lt_of_not_ge hn
  · rw [relativePeak_above M f cutoff P i he]
    exact pointedCosetVector_nonneg M f Q _ _

lemma relative_eligible_top_le {P Q:Deligne M}
    (ha:∀i∈P.val.1,i∉Q.val.1→RelativeEligible M f U cutoff P Q i) :
    ∀i∈P.val.1,i∉Q.val.1→
      pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q) (.inl i)≤
        pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q) (.inl i) := by
  intro i hi hq
  have hb:=relativePeak_le_lowerLevel M f cutoff P Q i hi hq
  have hh:=ha i hi hq
  rcases eq_or_lt_of_le hb.1 with he|he
  · rcases hh.2.2.2 with hl|⟨hl,_⟩
    · rw [he] at hl; exact hl.le
    · rw [he] at hl; exact hl.le
  · rw [relativePeak_above M f cutoff P i he,hh.2.2.1 _ he]

lemma relativeSign_eq_at_lower_tie {P Q:Deligne M} (h:Q≤P)
    (hv:pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q)=pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q))
    (i:S⊕Unit) : relativeSign M U (pointedProfile M f Q cutoff) (relativeLowerLevel M f cutoff P Q) i=
      relativeSign M U (pointedProfile M f P cutoff) (relativeLowerLevel M f cutoff P Q) i := by
  apply relativeSign_congr_above M U
  intro d hd
  rcases eq_or_lt_of_le hd with rfl|hd
  · exact hv
  · exact relativeProfile_eq_above_lower M f cutoff h hd

lemma relative_ineligible_tie_sign {P Q:Deligne M} (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1)
    (ha:¬RelativeEligible M f U cutoff P Q i)
    (he:relativePeak M f cutoff P i=relativeLowerLevel M f cutoff P Q)
    (hv:pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q)=pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q))
    (hp : 0 < pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q) (.inl i)) :
    relativeSign M U (pointedProfile M f P cutoff) (relativeLowerLevel M f cutoff P Q) (.inl i)= -1 := by
  have hn:relativeSign M U (pointedProfile M f P cutoff) (relativeLowerLevel M f cutoff P Q) (.inl i)≠1:=by
    intro hs
    apply ha
    refine ⟨hi,hq,?_,Or.inr ⟨?_,?_⟩⟩
    · intro d hd
      exact relativePeak_above M f cutoff Q i ((relativePeak_le_lowerLevel M f cutoff P Q i hi hq).2.trans_lt (he ▸ hd))
    · rw [he,hv]
    · rwa [he]
  dsimp only [relativeSign] at hn ⊢
  rw [ite_eq_right (ne_of_gt hp)] at hn ⊢
  split_ifs with hs
  · rw [ite_eq_left hs] at hn
    exact (hn rfl).elim
  · rfl

lemma relative_eligible_tie_sign {P Q:Deligne M} (i:S)
    (ha:RelativeEligible M f U cutoff P Q i) (he:relativePeak M f cutoff P i=relativeLowerLevel M f cutoff P Q)
    (hv:pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q)=pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q)) :
    relativeSign M U (pointedProfile M f P cutoff) (relativeLowerLevel M f cutoff P Q) (.inl i)=1 := by
  rcases ha.2.2.2 with hl|⟨_,hs⟩
  · rw [he,hv] at hl
    exact (lt_irrefl _ hl).elim
  · rwa [he] at hs


lemma relativeEligible_positive {P Q:Deligne M} {i:S}
    (h:RelativeEligible M f U cutoff P Q i) :
    0 < pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i) := by
  rcases h.2.2.2 with hl | ⟨_,hs⟩
  · exact lt_of_le_of_lt (pointedCosetVector_nonneg M f Q _ _) hl
  · by_contra hn
    have hz : pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i) = 0 :=
      le_antisymm (le_of_not_gt hn) (pointedCosetVector_nonneg M f P _ _)
    simp only [relativeSign,hz,↓reduceIte] at hs
    norm_num at hs

lemma relativeLowerLevel_prescribed_at_tie {P Q:Deligne M}
    (hsome : ∃ i ∈ P.val.1, i ∉ Q.val.1 ∧ ∃ k,
      0 < pointedProfile M f P cutoff k (.inl i) ∨
      0 < pointedProfile M f Q cutoff k (.inl i))
    (hv:pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q) =
        pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q)) :
    ∃ i ∈ P.val.1, i ∉ Q.val.1 ∧ relativePeak M f cutoff P i = relativeLowerLevel M f cutoff P Q ∧
      0 < pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q) (.inl i) := by
  obtain ⟨i,hi,hq,hp⟩ := relativeLowerLevel_attained M f cutoff P Q hsome
  have hn : 0 < pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q) (.inl i) := by
    rcases hp with hp|hp
    · exact hp
    · rwa [hv] at hp
  exact ⟨i,hi,hq,le_antisymm (relativePeak_le_lowerLevel M f cutoff P Q i hi hq).1
    (relativePeak_bound M f cutoff P i _ (ne_of_gt hn)),hn⟩

end HarmonicArtin.ParabolicIntersections

end OAI
