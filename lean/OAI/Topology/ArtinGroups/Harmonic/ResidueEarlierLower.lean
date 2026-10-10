import Mathlib
import OAI.Topology.ArtinGroups.Realizations.NerveOrderRetractionEquiv
import OAI.Topology.ArtinGroups.Harmonic.ResidueAllowed

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceResidueAllowed_trans {strict:Bool} {P Q R:Deligne M} {q:ℤ}
    (hQ:SourceResidueAllowed M strict P Q q) (hR:SourceResidueAllowed M true Q R q) :
    SourceResidueAllowed M strict P R q := by
  refine ⟨hR.1.trans hQ.1,?_⟩
  intro i hi hn
  by_cases hq:i∈Q.val.1
  · have hr:=hR.2 i hq hn
    have hl:sourceCosetVector M R q (.inl i)<sourceCosetVector M P q (.inl i):=
      lt_of_lt_of_le (by simpa only [↓reduceIte] using hr.2) (sourceResidueAllowed_le M hQ (.inl i))
    refine ⟨hr.1,?_⟩
    cases strict with
    | false => exact hl.le
    | true => exact hl
  · have he(d:ℤ):sourceCosetVector M Q d (.inl i)=sourceCosetVector M R d (.inl i):=
      sourceCosetVector_upper_outside M hR.1.le d _ (by
        rintro ⟨j,hj,hh⟩;exact hq ((Sum.inl_injective hh) ▸ hj))
    simpa only [he] using hQ.2 i hi hq

lemma sourceResidue_strict_height_drop {P Q R:Deligne M} {q:ℤ}
    (hQ:Q≤P) (hR:SourceResidueAllowed M true Q R q) :
    sourceResidueHeight M P R q<sourceResidueHeight M P Q q := by
  apply sourceResidueHeight_lt M (sourceResidueAllowed_le M hR)
  obtain ⟨i,hi,hn⟩:=Set.exists_of_ssubset (deligne_lt_type M hR.1)
  exact ⟨i,hQ.1 hi,by simpa only [↓reduceIte] using (hR.2 i hi hn).2⟩

abbrev SourceResidueEarlierLower (strict:Bool) (P X:Deligne M) (q:ℤ) :=
  {Y:Deligne M // SourceResidueAllowed M strict P Y q ∧ Y<X ∧
    sourceResidueHeight M P Y q<sourceResidueHeight M P X q}

def sourceResidueNegative (X Y:Deligne M) (q:ℤ) : Set S :=
  {i | i∈X.val.1 ∧ i∉Y.val.1 ∧ sourceCosetVector M Y q (.inl i)<sourceCosetVector M X q (.inl i)}

lemma sourceResidueNegative_nonempty {P X Y:Deligne M} {q:ℤ} (hy:Y≤X)
    (hh:sourceResidueHeight M P Y q<sourceResidueHeight M P X q) :
    (sourceResidueNegative M X Y q).Nonempty := by
  by_contra hn
  have hc:sourceCosetVector M X q≤ sourceCosetVector M Y q:=by
    apply sourceCosetVector_lower_compare_int_rev M hy q
    intro i hi hnY
    exact le_of_not_gt (fun hl=>hn ⟨i,hi,hnY,hl⟩)
  exact (not_lt_of_ge (sourceResidueHeight_mono M hc)) hh

lemma sourceResidueNegative_shared {X Y Z:Deligne M} {q:ℤ} (h:Y≤Z) (i:S) (hi:i∉Z.val.1) :
    i∈sourceResidueNegative M X Y q ↔ i∈sourceResidueNegative M X Z q := by
  have hy:i∉Y.val.1:=fun hh=>hi (h.1 hh)
  have he:=sourceCosetVector_upper_outside M h q (.inl i) (by
    rintro ⟨j,hj,hh⟩;exact hi ((Sum.inl_injective hh) ▸ hj))
  simp only [sourceResidueNegative,Set.mem_ofPred_eq,hy,hi,not_false_eq_true,true_and,he]

noncomputable def sourceResidueClose (X Y:Deligne M) (q:ℤ) : Deligne M :=
  sourceCoset M (X.val.1 \ sourceResidueNegative M X Y q)
    (source_spherical_mono M Set.sdiff_subset X.property.1) (sourceCosetRepresentative M Y)

lemma le_sourceResidueClose {X Y:Deligne M} {q:ℤ} (h:Y≤X) : Y≤ sourceResidueClose M X Y q := by
  calc
    Y=sourceCoset M Y.val.1 Y.property.1 (sourceCosetRepresentative M Y):=
      (sourceCoset_eq M Y _ (sourceCosetRepresentative_mem M Y)).symm
    _≤ sourceResidueClose M X Y q:=sourceCoset_le M (show Y.val.1⊆X.val.1 \ sourceResidueNegative M X Y q from
      fun i hi=>⟨h.1 hi,fun hn=>hn.2.1 hi⟩) _

lemma sourceResidueClose_le {X Y:Deligne M} {q:ℤ} (h:Y≤X) : sourceResidueClose M X Y q≤X := by
  calc
    sourceResidueClose M X Y q≤ sourceCoset M X.val.1 X.property.1 (sourceCosetRepresentative M Y):=
      sourceCoset_le M Set.sdiff_subset _
    _=X:=sourceCoset_eq M X _ (h.2 (sourceCosetRepresentative_mem M Y))

lemma sourceResidueClose_strict {strict:Bool} {P X Y:Deligne M} {q:ℤ}
    (hy:SourceResidueAllowed M strict P Y q) (hx:X≤P) (hyx:Y≤X)
    (hh:sourceResidueHeight M P Y q<sourceResidueHeight M P X q) :
    SourceResidueAllowed M true X (sourceResidueClose M X Y q) q := by
  refine ⟨lt_of_le_of_ne (sourceResidueClose_le M hyx) ?_,?_⟩
  · intro he
    obtain ⟨i,hi⟩:=sourceResidueNegative_nonempty M hyx hh
    have ht:=congrArg (fun K:Deligne M=>K.val.1) he
    have hm:i∈(sourceResidueClose M X Y q).val.1:=by rw [ht]; exact hi.1
    exact hm.2 hi
  · intro i hi hn
    have hc: i∈sourceResidueNegative M X Y q:=by
      by_contra hnot
      exact hn ⟨hi,hnot⟩
    have he(d:ℤ):sourceCosetVector M (sourceResidueClose M X Y q) d (.inl i)=sourceCosetVector M Y d (.inl i):=
      sourceCosetVector_upper_outside M (le_sourceResidueClose M hyx) d _ (by
        rintro ⟨j,hj,hh⟩;exact hn ((Sum.inl_injective hh) ▸ hj))
    simp only [↓reduceIte,he]
    exact ⟨(hy.2 i (hx.1 hi) hc.2.1).1,hc.2.2⟩

lemma sourceResidueClose_monotone {X Y Z:Deligne M} {q:ℤ} (h:Y≤Z) (hz:Z≤X) :
    sourceResidueClose M X Y q≤ sourceResidueClose M X Z q := by
  have ht:X.val.1 \ sourceResidueNegative M X Y q⊆X.val.1 \ sourceResidueNegative M X Z q:=by
    intro i hi
    refine ⟨hi.1,?_⟩
    intro hh
    exact hi.2 ((sourceResidueNegative_shared M h i hh.2.1).mpr hh)
  calc
    sourceResidueClose M X Y q≤ sourceCoset M (sourceResidueClose M X Z q).val.1
      (sourceResidueClose M X Z q).property.1 (sourceCosetRepresentative M Y):=sourceCoset_le M ht _
    _=sourceResidueClose M X Z q:=sourceCoset_eq M _ _
      ((le_sourceResidueClose M hz).2 (h.2 (sourceCosetRepresentative_mem M Y)))

lemma sourceResidueClose_eq {X Y:Deligne M} {q:ℤ}
    (h:SourceResidueAllowed M true X Y q) : sourceResidueClose M X Y q=Y := by
  symm
  apply deligne_eq_of_le_type_eq M (le_sourceResidueClose M h.1.le)
  ext i
  change i∈Y.val.1 ↔ i∈X.val.1 ∧ ¬i∈sourceResidueNegative M X Y q
  constructor
  · intro hi
    exact ⟨h.1.le.1 hi,fun hn=>hn.2.1 hi⟩
  · rintro ⟨hi,hn⟩
    by_contra hy
    exact hn ⟨hi,hy,by simpa only [↓reduceIte] using (h.2 i hi hy).2⟩

noncomputable def sourceResidueLowerInclusion {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:SourceResidueAllowed M strict P X q) :
    SourceResidue M true X q →o SourceResidueEarlierLower M strict P X q where
  toFun Y:=⟨Y.val,sourceResidueAllowed_trans M hX Y.property,Y.property.1,
    sourceResidue_strict_height_drop M hX.1.le Y.property⟩
  monotone':=fun _ _ h=>h

noncomputable def sourceResidueLowerProjection {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:SourceResidueAllowed M strict P X q) :
    SourceResidueEarlierLower M strict P X q →o SourceResidue M true X q where
  toFun Y:=⟨sourceResidueClose M X Y q,sourceResidueClose_strict M Y.property.1 hX.1.le
    Y.property.2.1.le Y.property.2.2⟩
  monotone':=fun _ Z h=>sourceResidueClose_monotone M h Z.property.2.1.le

noncomputable def sourceResidueLowerEquiv {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:SourceResidueAllowed M strict P X q) :
    ContinuousMap.HomotopyEquiv |CategoryTheory.nerve (SourceResidueEarlierLower M strict P X q)|
      |CategoryTheory.nerve (SourceResidue M true X q)| :=
  nerveOrderRetractionEquiv (sourceResidueLowerProjection M hX) (sourceResidueLowerInclusion M hX)
    (by apply OrderHom.ext; funext Y; apply Subtype.ext; exact sourceResidueClose_eq M Y.property)
    (fun Y=>le_sourceResidueClose M Y.property.2.1.le)

end HarmonicArtin

end OAI
