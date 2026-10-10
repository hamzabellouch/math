import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCosetGeometry
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueAllowed
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCap
import OAI.Topology.ArtinGroups.Harmonic.ResidueEarlierLower
import Mathlib
import OAI.Topology.ArtinGroups.Realizations.NerveOrderRetractionEquiv
import OAI.Topology.ArtinGroups.Harmonic.ResidueAllowed

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedResidueAllowed_trans {strict:Bool} {P Q R:Deligne M} {q:ℤ}
    (hQ:PointedResidueAllowed M f strict P Q q) (hR:PointedResidueAllowed M f true Q R q) :
    PointedResidueAllowed M f strict P R q := by
  refine ⟨hR.1.trans hQ.1,?_⟩
  intro i hi hn
  by_cases hq:i∈Q.val.1
  · have hr:=hR.2 i hq hn
    have hl:pointedCosetVector M f R q (.inl i)<pointedCosetVector M f P q (.inl i):=
      lt_of_lt_of_le (by simpa only [↓reduceIte] using hr.2) (pointedResidueAllowed_le M f hQ (.inl i))
    refine ⟨hr.1,?_⟩
    cases strict with
    | false => exact hl.le
    | true => exact hl
  · have he(d:ℤ):pointedCosetVector M f Q d (.inl i)=pointedCosetVector M f R d (.inl i):=
      pointedCosetVector_upper_outside M f hR.1.le d _ (by
        rintro ⟨j,hj,hh⟩;exact hq ((Sum.inl_injective hh) ▸ hj))
    simpa only [he] using hQ.2 i hi hq

lemma pointedResidue_strict_height_drop {P Q R:Deligne M} {q:ℤ}
    (hQ:Q≤P) (hR:PointedResidueAllowed M f true Q R q) :
    pointedResidueHeight M f P R q<pointedResidueHeight M f P Q q := by
  apply pointedResidueHeight_lt M f (pointedResidueAllowed_le M f hR)
  obtain ⟨i,hi,hn⟩:=Set.exists_of_ssubset (deligne_lt_type M hR.1)
  exact ⟨i,hQ.1 hi,by simpa only [↓reduceIte] using (hR.2 i hi hn).2⟩

abbrev PointedResidueEarlierLower (strict:Bool) (P X:Deligne M) (q:ℤ) :=
  {Y:Deligne M // PointedResidueAllowed M f strict P Y q ∧ Y<X ∧
    pointedResidueHeight M f P Y q<pointedResidueHeight M f P X q}

def pointedResidueNegative (X Y:Deligne M) (q:ℤ) : Set S :=
  {i | i∈X.val.1 ∧ i∉Y.val.1 ∧ pointedCosetVector M f Y q (.inl i)<pointedCosetVector M f X q (.inl i)}

lemma pointedResidueNegative_nonempty {P X Y:Deligne M} {q:ℤ} (hy:Y≤X)
    (hh:pointedResidueHeight M f P Y q<pointedResidueHeight M f P X q) :
    (pointedResidueNegative M f X Y q).Nonempty := by
  by_contra hn
  have hc:pointedCosetVector M f X q≤ pointedCosetVector M f Y q:=by
    apply pointedCosetVector_lower_compare_int_rev M f hy q
    intro i hi hnY
    exact le_of_not_gt (fun hl=>hn ⟨i,hi,hnY,hl⟩)
  exact (not_lt_of_ge (pointedResidueHeight_mono M f hc)) hh

lemma pointedResidueNegative_shared {X Y Z:Deligne M} {q:ℤ} (h:Y≤Z) (i:S) (hi:i∉Z.val.1) :
    i∈pointedResidueNegative M f X Y q ↔ i∈pointedResidueNegative M f X Z q := by
  have hy:i∉Y.val.1:=fun hh=>hi (h.1 hh)
  have he:=pointedCosetVector_upper_outside M f h q (.inl i) (by
    rintro ⟨j,hj,hh⟩;exact hi ((Sum.inl_injective hh) ▸ hj))
  simp only [pointedResidueNegative,Set.mem_ofPred_eq,hy,hi,not_false_eq_true,true_and,he]

noncomputable def pointedResidueClose (X Y:Deligne M) (q:ℤ) : Deligne M :=
  sourceCoset M (X.val.1 \ pointedResidueNegative M f X Y q)
    (source_spherical_mono M Set.sdiff_subset X.property.1) (sourceCosetRepresentative M Y)

lemma le_pointedResidueClose {X Y:Deligne M} {q:ℤ} (h:Y≤X) : Y≤ pointedResidueClose M f X Y q := by
  calc
    Y=sourceCoset M Y.val.1 Y.property.1 (sourceCosetRepresentative M Y):=
      (sourceCoset_eq M Y _ (sourceCosetRepresentative_mem M Y)).symm
    _≤ pointedResidueClose M f X Y q:=sourceCoset_le M (show Y.val.1⊆X.val.1 \ pointedResidueNegative M f X Y q from
      fun i hi=>⟨h.1 hi,fun hn=>hn.2.1 hi⟩) _

lemma pointedResidueClose_le {X Y:Deligne M} {q:ℤ} (h:Y≤X) : pointedResidueClose M f X Y q≤X := by
  calc
    pointedResidueClose M f X Y q≤ sourceCoset M X.val.1 X.property.1 (sourceCosetRepresentative M Y):=
      sourceCoset_le M Set.sdiff_subset _
    _=X:=sourceCoset_eq M X _ (h.2 (sourceCosetRepresentative_mem M Y))

lemma pointedResidueClose_strict {strict:Bool} {P X Y:Deligne M} {q:ℤ}
    (hy:PointedResidueAllowed M f strict P Y q) (hx:X≤P) (hyx:Y≤X)
    (hh:pointedResidueHeight M f P Y q<pointedResidueHeight M f P X q) :
    PointedResidueAllowed M f true X (pointedResidueClose M f X Y q) q := by
  refine ⟨lt_of_le_of_ne (pointedResidueClose_le M f hyx) ?_,?_⟩
  · intro he
    obtain ⟨i,hi⟩:=pointedResidueNegative_nonempty M f hyx hh
    have ht:=congrArg (fun K:Deligne M=>K.val.1) he
    have hm:i∈(pointedResidueClose M f X Y q).val.1:=by rw [ht]; exact hi.1
    exact hm.2 hi
  · intro i hi hn
    have hc: i∈pointedResidueNegative M f X Y q:=by
      by_contra hnot
      exact hn ⟨hi,hnot⟩
    have he(d:ℤ):pointedCosetVector M f (pointedResidueClose M f X Y q) d (.inl i)=pointedCosetVector M f Y d (.inl i):=
      pointedCosetVector_upper_outside M f (le_pointedResidueClose M f hyx) d _ (by
        rintro ⟨j,hj,hh⟩;exact hn ((Sum.inl_injective hh) ▸ hj))
    simp only [↓reduceIte,he]
    exact ⟨(hy.2 i (hx.1 hi) hc.2.1).1,hc.2.2⟩

lemma pointedResidueClose_monotone {X Y Z:Deligne M} {q:ℤ} (h:Y≤Z) (hz:Z≤X) :
    pointedResidueClose M f X Y q≤ pointedResidueClose M f X Z q := by
  have ht:X.val.1 \ pointedResidueNegative M f X Y q⊆X.val.1 \ pointedResidueNegative M f X Z q:=by
    intro i hi
    refine ⟨hi.1,?_⟩
    intro hh
    exact hi.2 ((pointedResidueNegative_shared M f h i hh.2.1).mpr hh)
  calc
    pointedResidueClose M f X Y q≤ sourceCoset M (pointedResidueClose M f X Z q).val.1
      (pointedResidueClose M f X Z q).property.1 (sourceCosetRepresentative M Y):=sourceCoset_le M ht _
    _=pointedResidueClose M f X Z q:=sourceCoset_eq M _ _
      ((le_pointedResidueClose M f hz).2 (h.2 (sourceCosetRepresentative_mem M Y)))

lemma pointedResidueClose_eq {X Y:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f true X Y q) : pointedResidueClose M f X Y q=Y := by
  symm
  apply deligne_eq_of_le_type_eq M (le_pointedResidueClose M f h.1.le)
  ext i
  change i∈Y.val.1 ↔ i∈X.val.1 ∧ ¬i∈pointedResidueNegative M f X Y q
  constructor
  · intro hi
    exact ⟨h.1.le.1 hi,fun hn=>hn.2.1 hi⟩
  · rintro ⟨hi,hn⟩
    by_contra hy
    exact hn ⟨hi,hy,by simpa only [↓reduceIte] using (h.2 i hi hy).2⟩

noncomputable def pointedResidueLowerInclusion {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f strict P X q) :
    PointedResidue M f true X q →o PointedResidueEarlierLower M f strict P X q where
  toFun Y:=⟨Y.val,pointedResidueAllowed_trans M f hX Y.property,Y.property.1,
    pointedResidue_strict_height_drop M f hX.1.le Y.property⟩
  monotone':=fun _ _ h=>h

noncomputable def pointedResidueLowerProjection {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f strict P X q) :
    PointedResidueEarlierLower M f strict P X q →o PointedResidue M f true X q where
  toFun Y:=⟨pointedResidueClose M f X Y q,pointedResidueClose_strict M f Y.property.1 hX.1.le
    Y.property.2.1.le Y.property.2.2⟩
  monotone':=fun _ Z h=>pointedResidueClose_monotone M f h Z.property.2.1.le

noncomputable def pointedResidueLowerEquiv {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f strict P X q) :
    ContinuousMap.HomotopyEquiv |CategoryTheory.nerve (PointedResidueEarlierLower M f strict P X q)|
      |CategoryTheory.nerve (PointedResidue M f true X q)| :=
  nerveOrderRetractionEquiv (pointedResidueLowerProjection M f hX) (pointedResidueLowerInclusion M f hX)
    (by apply OrderHom.ext; funext Y; apply Subtype.ext; exact pointedResidueClose_eq M f Y.property)
    (fun Y=>le_pointedResidueClose M f Y.property.2.1.le)

end HarmonicArtin.ParabolicIntersections

end OAI
