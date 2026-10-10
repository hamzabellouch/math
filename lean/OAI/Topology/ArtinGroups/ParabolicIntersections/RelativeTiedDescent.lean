import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeDescending
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeTieLower

namespace OAI

/-! Compatibility of descending neighborhoods across equal-height inclusions. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ) {Y:Set S} {x:Artin M}

lemma relativeTie_active_common {P Q:RelativeVertex M Y x} (hPQ:P≤Q)
    (he:relativeHeight M f U cutoff P.val=relativeHeight M f U cutoff Q.val)
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (i:S) (hi:i∈Y) (hn:i∉P.val.val.1) (ha:relativeColorActive M f U cutoff P.val i) :
    ∃ V:RelativeVertex M Y x, relativeAdjacent M P V ∧ relativeAdjacent M Q V ∧
      relativeHeight M f U cutoff V.val<relativeHeight M f U cutoff P.val := by
  have hp:=relativeProfiles_eq_of_tie M f U cutoff he
  have hni:i∉Q.val.val.1:=by
    intro hiQ
    have hz:=tied_new_color_invisible M f U cutoff Y Q.property.1 he i hiQ hn
    have hinc:=relative_active_incident M f U cutoff P.val i ha
    unfold levelIncident at hinc
    rw [hp] at hinc
    exact hz.2 _ hinc
  have haQ:relativeColorActive M f U cutoff Q.val i:=by
    unfold relativeColorActive at *
    rwa [←hp]
  have htop:=relative_upperTop_descending M f U cutoff Y x Q hYU ⟨i,hi,hni,haQ⟩
  exact ⟨relativeUpperTop M f U cutoff Y x Q hYU,
    Or.inl (hPQ.trans htop.1.le),Or.inl htop.1.le,htop.2.trans_eq he.symm⟩

lemma relativeTie_common_from_larger {P Q:RelativeVertex M Y x} (hPQ:P≤Q)
    (he:relativeHeight M f U cutoff P.val=relativeHeight M f U cutoff Q.val)
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (A:RelativeVertex M Y x) (hA:relativeAdjacent M Q A)
    (ha:relativeHeight M f U cutoff A.val<relativeHeight M f U cutoff Q.val) :
    ∃ V:RelativeVertex M Y x, relativeAdjacent M P V ∧ relativeAdjacent M Q V ∧
      relativeHeight M f U cutoff V.val<relativeHeight M f U cutoff P.val := by
  have hne:Q.val≠A.val:=by intro h;rw [h] at ha;exact lt_irrefl _ ha
  rcases hA with hQA|hAQ
  · obtain ⟨i,hi,hn,hact⟩:=relativeUpper_descending_has_active M f U cutoff
      (lt_of_le_of_ne hQA hne) ha
    have hp:=relativeProfiles_eq_of_tie M f U cutoff he
    have hactP:relativeColorActive M f U cutoff P.val i:=by
      unfold relativeColorActive at *
      rwa [hp]
    exact relativeTie_active_common M f U cutoff hPQ he hYU i (A.property.1 hi)
      (fun hiP=>hn (hPQ.1 hiP)) hactP
  · obtain ⟨V,hVP,hVh⟩:=relativeTie_lower_nonempty M f U cutoff Y hPQ Q.property.1 he A.val
      (lt_of_le_of_ne hAQ (Ne.symm hne)) ha
    let W:RelativeVertex M Y x:=⟨V,hVP.le.1.trans P.property.1,hVP.le.2.trans P.property.2⟩
    exact ⟨W,Or.inr hVP.le,Or.inr (hVP.le.trans hPQ),hVh⟩

lemma relativeTie_common_from_smaller {P Q:RelativeVertex M Y x} (hPQ:P≤Q)
    (he:relativeHeight M f U cutoff P.val=relativeHeight M f U cutoff Q.val)
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (A:RelativeVertex M Y x) (hA:relativeAdjacent M P A)
    (ha:relativeHeight M f U cutoff A.val<relativeHeight M f U cutoff P.val) :
    ∃ V:RelativeVertex M Y x, relativeAdjacent M P V ∧ relativeAdjacent M Q V ∧
      relativeHeight M f U cutoff V.val<relativeHeight M f U cutoff P.val := by
  have hne:P.val≠A.val:=by intro h;rw [h] at ha;exact lt_irrefl _ ha
  rcases hA with hPA|hAP
  · obtain ⟨i,hi,hn,hact⟩:=relativeUpper_descending_has_active M f U cutoff
      (lt_of_le_of_ne hPA hne) ha
    exact relativeTie_active_common M f U cutoff hPQ he hYU i (A.property.1 hi) hn hact
  · exact ⟨A,Or.inr hAP,Or.inr (hAP.trans hPQ),ha⟩

/-- The local hypotheses used by path lowering are verified for the actual
relative coset poset and the actual pointed-family height. -/
theorem relative_localDescent
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hx:x∈artinParabolic M {f}ᶜ) :
    LocalDescent (relativeAdjacent M (Y:=Y) (x:=x))
      (fun P=>relativeHeight M f U cutoff P.val) where
  symmetric := fun h=>h.elim Or.inr Or.inl
  descending := fun P A B hA ha hB hb=>
    relative_descending_connected M f U cutoff P hYU hU hf
      (relative_vertex_avoids_frame M f (fun hi=>hf (hYU f hi)) hx P) A B hA ha hB hb
  tied := by
    intro P Q hPQ he A hA ha
    rcases hPQ with hPQ|hQP
    · obtain ⟨V,hPV,hQV,hV⟩:=relativeTie_common_from_smaller M f U cutoff hPQ he hYU A hA ha
      exact ⟨V,hQV,hV.trans_eq he,
        relative_descending_connected M f U cutoff P hYU hU hf
          (relative_vertex_avoids_frame M f (fun hi=>hf (hYU f hi)) hx P) A V hA ha hPV hV⟩
    · obtain ⟨V,hQV,hPV,hV⟩:=relativeTie_common_from_larger M f U cutoff hQP he.symm hYU A hA ha
      have hVP:relativeHeight M f U cutoff V.val<relativeHeight M f U cutoff P.val:=hV.trans_eq he.symm
      exact ⟨V,hQV,hV,
        relative_descending_connected M f U cutoff P hYU hU hf
          (relative_vertex_avoids_frame M f (fun hi=>hf (hYU f hi)) hx P) A V hA ha hPV hVP⟩

theorem relative_minimum_path
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hx:x∈artinParabolic M {f}ᶜ)
    (P Q:RelativeVertex M Y x)
    (hP:∀V:RelativeVertex M Y x,relativeHeight M f U cutoff P.val≤relativeHeight M f U cutoff V.val)
    (hQ:∀V:RelativeVertex M Y x,relativeHeight M f U cutoff Q.val≤relativeHeight M f U cutoff V.val) :
    PathWithin (relativeAdjacent M)
      (fun P=>∀V:RelativeVertex M Y x,relativeHeight M f U cutoff P.val≤relativeHeight M f U cutoff V.val) P Q :=
  minimum_path _ _ (relative_localDescent M f U cutoff hYU hU hf hx) wellFounded_lt hP hQ
    (relative_poset_connected M Y x P Q)

end HarmonicArtin.ParabolicIntersections

end OAI
