import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeLowerRetraction
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeTies
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedTypeComponent
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCosetProduct

namespace OAI

/-! Transferring an eligible opening across a tied inclusion. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativeProfiles_eq_of_tie {P Q:Deligne M}
    (he:relativeHeight M f U cutoff P=relativeHeight M f U cutoff Q) :
    pointedProfile M f P cutoff=pointedProfile M f Q cutoff :=
  Finsupp.ext (relativeHeight_eq_profiles M f U cutoff he)

lemma relativePeak_eq_of_tie {P Q:Deligne M}
    (he:relativeHeight M f U cutoff P=relativeHeight M f U cutoff Q) (i:S) :
    relativePeak M f cutoff P i=relativePeak M f cutoff Q i := by
  unfold relativePeak relativePeakSupport
  rw [relativeProfiles_eq_of_tie M f U cutoff he]

lemma relativeEligible_visible {P R:Deligne M} (Y:Set S) (_hP:P.val.1⊆Y)
    {i:S} (hi:RelativeEligible M f U cutoff P R i) :
    i∈relativeVisible M f cutoff Y P := by
  refine ⟨hi.1,?_⟩
  intro hn
  exact hn.2 (relativePeak M f cutoff P i) (Or.inl (relativeEligible_positive M f U cutoff hi))

lemma relativeVisible_commutes (Y:Set S) (P:Deligne M) (hP:P.val.1⊆Y)
    (i:S) (hi:i∈relativeVisible M f cutoff Y P) (j:S)
    (hj:j∈relativeInvisible M f cutoff Y P) : M i j=2 := by
  by_contra hn
  have hij:i≠j:=by rintro rfl;exact hi.2 hj
  have hc:=framedCartan_neg_of_label_ne_two M i j hij hn
  rw [framedCartan_symm] at hc
  exact relativeVisible_nonadjacent M f cutoff Y P hP j i hj hi hc

lemma relativeEligible_single_open (P R:Deligne M) (i:S)
    (hi:RelativeEligible M f U cutoff P R i) (z:Artin M) (hz:z∈P.val.2)
    (he:∀k:ℕ,pointedMultiplicity M f z (cutoff+k) (.inl i)=pointedProfile M f R cutoff k (.inl i)) :
    ∃ Q:Deligne M,Q<P ∧ relativeHeight M f U cutoff Q<relativeHeight M f U cutoff P := by
  let T:=P.val.1\{i}
  let Q:=sourceCoset M T (source_spherical_mono M Set.sdiff_subset P.property.1) z
  have hle:Q≤P := by
    rw [←sourceCoset_eq M P z hz]
    exact sourceCoset_le M Set.sdiff_subset z
  have hin:i∉Q.val.1:=fun hh=>hh.2 rfl
  have hlt:Q<P:=lt_of_le_of_ne hle (by
    intro h
    apply hin
    rw [h]
    exact hi.1)
  have hv (k:ℕ) : pointedProfile M f Q cutoff k (.inl i)=pointedProfile M f R cutoff k (.inl i) := by
    change pointedCosetVector M f Q (cutoff+k) (.inl i)=_
    rw [pointedCosetVector_open M f Q i hin z (rightCoset_self M T z),he]
  have hnew:RelativeEligible M f U cutoff P Q i := by
    refine ⟨hi.1,hin,?_,?_⟩
    · intro d hd
      rw [hv]
      exact hi.2.2.1 d hd
    · simpa only [hv] using hi.2.2.2
  exact ⟨Q,hlt,relativeLower_eligible_descending M f U cutoff hlt (by
    intro j hj hn
    have hji:j=i:=by
      by_contra hji
      exact hn ⟨hj,hji⟩
    subst j
    exact hnew)⟩

/-- A descending lower neighbor at the larger end of a tie yields one at
its smaller end. The invisible group factor is omitted from the representative. -/
theorem relativeTie_lower_nonempty (Y:Set S) {P Q:Deligne M} (hPQ:P≤Q) (hQ:Q.val.1⊆Y)
    (htie:relativeHeight M f U cutoff P=relativeHeight M f U cutoff Q)
    (R:Deligne M) (hR:R<Q) (hdesc:relativeHeight M f U cutoff R<relativeHeight M f U cutoff Q) :
    ∃ V:Deligne M,V<P ∧ relativeHeight M f U cutoff V<relativeHeight M f U cutoff P := by
  obtain ⟨i,hi⟩:=relativeLower_descending_has_eligible M f U cutoff hR hdesc
  let B:=relativeVisible M f cutoff Y Q
  let C:=Q.val.1∩relativeInvisible M f cutoff Y Q
  have hBC:B∪C=Q.val.1:=by
    ext j
    simp only [B,C,relativeVisible,Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff]
    tauto
  have hc:∀s∈B,∀t∈C,M s t=2:=fun s hs t ht=>
    relativeVisible_commutes M f cutoff Y Q hQ s hs t ht.2
  have hiB:i∈B:=relativeEligible_visible M f U cutoff Y hQ hi
  have hiP:i∈P.val.1:=by
    have he:=relativeVisible_eq_of_tie M f U cutoff Y hPQ hQ htie
    have hm:i∈relativeVisible M f cutoff Y P:=he ▸ hiB
    exact hm.1
  let z:=sourceCosetRepresentative M P
  let w:=sourceCosetRepresentative M R
  have hz:z∈Q.val.2:=hPQ.2 (sourceCosetRepresentative_mem M P)
  have hw:w∈Q.val.2:=hR.le.2 (sourceCosetRepresentative_mem M R)
  have hg:w*z⁻¹∈artinParabolic M (B∪C):=by
    rw [hBC]
    rw [←sourceCoset_eq M Q z hz] at hw
    exact hw
  rw [←sourceParabolicProductMap_range M B C hc] at hg
  obtain ⟨⟨b,c⟩,hbc⟩:=hg
  have hmul:(b:Artin M)*c=w*z⁻¹:=hbc
  have hew:w=(c:Artin M)*((b:Artin M)*z):=by
    rw [←_root_.mul_assoc,←(sourceParabolics_commute M B C hc b c b.property c.property).eq,hmul]
    group
  have hbP:(b:Artin M)∈artinParabolic M P.val.1:=by
    apply artinParabolic_mono M _ b.property
    intro j hj
    have he:=relativeVisible_eq_of_tie M f U cutoff Y hPQ hQ htie
    exact (show j∈relativeVisible M f cutoff Y P from he ▸ hj).1
  have hbz:(b:Artin M)*z∈P.val.2:=by
    rw [←sourceCoset_eq M P z (sourceCosetRepresentative_mem M P)]
    change ((b:Artin M)*z)*z⁻¹∈artinParabolic M P.val.1
    simpa only [_root_.mul_assoc,mul_inv_cancel,_root_.mul_one] using hbP
  have hiC:(.inl i:S⊕Unit)∉Sum.inl '' C:=by
    rintro ⟨j,hj,hji⟩
    cases Sum.inl.inj hji
    exact hiB.2 hj.2
  have heprof:=relativeProfiles_eq_of_tie M f U cutoff htie
  have hielig:RelativeEligible M f U cutoff P R i:=by
    refine ⟨hiP,hi.2.1,?_,?_⟩
    · simpa only [relativePeak_eq_of_tie M f U cutoff htie] using hi.2.2.1
    · simpa only [relativePeak_eq_of_tie M f U cutoff htie,heprof] using hi.2.2.2
  apply relativeEligible_single_open M f U cutoff P R i hielig ((b:Artin M)*z) hbz
  intro k
  have hv:=pointedCosetVector_open M f R i hi.2.1 w (sourceCosetRepresentative_mem M R) (cutoff+k)
  change _=pointedCosetVector M f R (cutoff+k) (.inl i)
  rw [hv,hew,pointedMultiplicity_exterior_ordered M f C c c.property _ _ hiC]

end HarmonicArtin.ParabolicIntersections

end OAI
