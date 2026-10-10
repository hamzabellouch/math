import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCosetGeometry
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueAllowed
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCap
import OAI.Topology.ArtinGroups.Harmonic.ResidueActive
import Mathlib
import OAI.Topology.ArtinGroups.Realizations.NerveOrderMap
import OAI.Topology.ArtinGroups.Harmonic.HarmonicUpperAntitone
import OAI.Topology.ArtinGroups.Harmonic.ResidueAllowed

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedCosetVector_upper_antitone_int {X R:Deligne M} (h:X≤R) (q:ℤ)
    (hr:∀i∈R.val.1,i∉X.val.1→0≤(framedCartan M *ᵥ pointedCosetVector M f X q) (.inl i)) :
    pointedCosetVector M f R q≤ pointedCosetVector M f X q := by
  apply harmonic_upper_antitone (framedCartan M) (framedCartan_off M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (pointedCosetVector M f X q) (pointedCosetVector M f R q)
    (pointedCosetVector_upper_outside M f h q) (pointedCosetVector_harmonic M f R q)
  rintro ⟨_,⟨i,hi,rfl⟩⟩
  by_cases ht:i∈X.val.1
  · rw [pointedCosetVector_harmonic M f X q ⟨.inl i,⟨i,ht,rfl⟩⟩]
  · exact hr i hi ht

lemma pointedCosetVector_upper_monotone_int {X R:Deligne M} (h:X≤R) (q:ℤ)
    (hr:∀i∈R.val.1,i∉X.val.1→(framedCartan M *ᵥ pointedCosetVector M f X q) (.inl i)≤0) :
    pointedCosetVector M f X q≤ pointedCosetVector M f R q := by
  apply harmonic_upper_monotone (framedCartan M) (framedCartan_off M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (pointedCosetVector M f X q) (pointedCosetVector M f R q)
    (pointedCosetVector_upper_outside M f h q) (pointedCosetVector_harmonic M f R q)
  rintro ⟨_,⟨i,hi,rfl⟩⟩
  by_cases ht:i∈X.val.1
  · rw [pointedCosetVector_harmonic M f X q ⟨.inl i,⟨i,ht,rfl⟩⟩]
  · exact hr i hi ht

lemma pointedResidueHeight_lt_of_ne {P Q R:Deligne M} {q:ℤ} (hQ:Q≤P) (hR:R≤P)
    (h:pointedCosetVector M f Q q≤ pointedCosetVector M f R q)
    (hn:pointedCosetVector M f Q q≠pointedCosetVector M f R q) :
    pointedResidueHeight M f P Q q<pointedResidueHeight M f P R q := by
  apply pointedResidueHeight_lt M f h
  by_contra he
  apply hn
  funext v
  by_cases hv:v∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨i,hi,rfl⟩:=hv
    exact le_antisymm (h _) (le_of_not_gt (fun hl=>he ⟨i,hi,hl⟩))
  · exact (pointedCosetVector_upper_outside M f hQ q v hv).symm.trans
      (pointedCosetVector_upper_outside M f hR q v hv)

def pointedResidueActive (P X:Deligne M) (q:ℤ) : Set S :=
  {i | i∈P.val.1 ∧ i∉X.val.1 ∧ 0≤(framedCartan M *ᵥ pointedCosetVector M f X q) (.inl i)}

lemma pointedResidueActive_misses {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:pointedResidueHeight M f P X q<0) :
    ∃i∈P.val.1,i∉X.val.1 ∧ i∉pointedResidueActive M f P X q := by
  by_contra hn
  have hv:pointedCosetVector M f P q≤ pointedCosetVector M f X q:=by
    apply pointedCosetVector_upper_antitone_int M f hx q
    intro i hi hxi
    by_contra hr
    exact hn ⟨i,hi,hxi,fun hd=>hr hd.2.2⟩
  have hnon:0≤ pointedResidueHeight M f P X q:=
    Finset.sum_nonneg (fun i _=>sub_nonneg.mpr (hv (.inl i)))
  exact (not_lt_of_ge hnon) hh

abbrev PointedResidueEarlierUpper (P X:Deligne M) (q:ℤ) :=
  {R:Deligne M // X<R ∧ R<P ∧ pointedResidueHeight M f P R q≤ pointedResidueHeight M f P X q}

lemma pointedResidueUpper_meets {P X R:Deligne M} {q:ℤ} (hr:X<R) (hp:R≤P)
    (hh:pointedResidueHeight M f P R q≤ pointedResidueHeight M f P X q) :
    ∃i∈R.val.1,i∈pointedResidueActive M f P X q := by
  by_contra hn
  have hnrow:∀i∈R.val.1,i∉X.val.1→(framedCartan M *ᵥ pointedCosetVector M f X q) (.inl i)<0:=by
    intro i hi hxi
    exact lt_of_not_ge (fun hh=>hn ⟨i,hi,hp.1 hi,hxi,hh⟩)
  have hv:=pointedCosetVector_upper_monotone_int M f hr.le q (fun i hi hx=>(hnrow i hi hx).le)
  have hne:pointedCosetVector M f X q≠pointedCosetVector M f R q:=by
    intro he
    obtain ⟨i,hi,hxi⟩:=Set.exists_of_ssubset (deligne_lt_type M hr)
    have hh:=hnrow i hi hxi
    rw [he,pointedCosetVector_harmonic M f R q ⟨.inl i,⟨i,hi,rfl⟩⟩] at hh
    exact lt_irrefl _ hh
  exact (not_lt_of_ge hh) (pointedResidueHeight_lt_of_ne M f (hr.le.trans hp) hp hv hne)

lemma pointedResidueUpper_active {P X R:Deligne M} {q:ℤ} (hr:X≤R)
    (ha:∀i∈R.val.1,i∉X.val.1→i∈pointedResidueActive M f P X q) :
    pointedResidueHeight M f P R q≤ pointedResidueHeight M f P X q :=
  pointedResidueHeight_mono M f (pointedCosetVector_upper_antitone_int M f hr q (fun i hi hn=>(ha i hi hn).2.2))

noncomputable def pointedResidueUpperTop (P X:Deligne M) (q:ℤ) (hx:X≤P) : Deligne M :=
  sourceCoset M (X.val.1 ∪ pointedResidueActive M f P X q)
    (source_spherical_mono M (show X.val.1 ∪ pointedResidueActive M f P X q⊆P.val.1 from
      fun _ hi=>hi.elim (fun h=>hx.1 h) (fun h=>h.1)) P.property.1)
    (sourceCosetRepresentative M X)

noncomputable def pointedResidueUpperClip (P X R:Deligne M) (q:ℤ) : Deligne M :=
  sourceCoset M (R.val.1 ∩ (X.val.1 ∪ pointedResidueActive M f P X q))
    (source_spherical_mono M Set.inter_subset_left R.property.1) (sourceCosetRepresentative M X)

lemma pointedResidueUpperClip_le {P X R:Deligne M} {q:ℤ} (h:X≤R) :
    pointedResidueUpperClip M f P X R q≤R := by
  calc
    pointedResidueUpperClip M f P X R q≤ sourceCoset M R.val.1 R.property.1 (sourceCosetRepresentative M X):=
      sourceCoset_le M Set.inter_subset_left _
    _=R:=sourceCoset_eq M R _ (h.2 (sourceCosetRepresentative_mem M X))

lemma le_pointedResidueUpperClip {P X R:Deligne M} {q:ℤ} (h:X≤R) :
    X≤ pointedResidueUpperClip M f P X R q := by
  calc
    X=sourceCoset M X.val.1 X.property.1 (sourceCosetRepresentative M X):=
      (sourceCoset_eq M X _ (sourceCosetRepresentative_mem M X)).symm
    _≤ pointedResidueUpperClip M f P X R q:=sourceCoset_le M (show X.val.1⊆R.val.1 ∩ (X.val.1 ∪ pointedResidueActive M f P X q) from
      fun i hi=>⟨h.1 hi,Or.inl hi⟩) _

lemma pointedResidueUpperTop_mem {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:pointedResidueHeight M f P X q<0) (hd:(pointedResidueActive M f P X q).Nonempty) :
    X<pointedResidueUpperTop M f P X q hx ∧ pointedResidueUpperTop M f P X q hx<P ∧
      pointedResidueHeight M f P (pointedResidueUpperTop M f P X q hx) q≤ pointedResidueHeight M f P X q := by
  have hl:X≤ pointedResidueUpperTop M f P X q hx:=by
    calc
      X=sourceCoset M X.val.1 X.property.1 (sourceCosetRepresentative M X):=
        (sourceCoset_eq M X _ (sourceCosetRepresentative_mem M X)).symm
      _≤ pointedResidueUpperTop M f P X q hx:=sourceCoset_le M Set.subset_union_left _
  have hp:pointedResidueUpperTop M f P X q hx≤P:=by
    calc
      pointedResidueUpperTop M f P X q hx≤ sourceCoset M P.val.1 P.property.1 (sourceCosetRepresentative M X):=
        sourceCoset_le M (fun _ hi=>hi.elim (fun h=>hx.1 h) (fun h=>h.1)) _
      _=P:=sourceCoset_eq M P _ (hx.2 (sourceCosetRepresentative_mem M X))
  refine ⟨lt_of_le_of_ne hl ?_,lt_of_le_of_ne hp ?_,pointedResidueUpper_active M f hl (fun _ hi hn=>hi.resolve_left hn)⟩
  · intro he
    obtain ⟨i,hi⟩:=hd
    have ht:=congrArg (fun K:Deligne M=>K.val.1) he
    have hiTop:i∈(pointedResidueUpperTop M f P X q hx).val.1:=Or.inr hi
    rw [←ht] at hiTop
    exact hi.2.1 hiTop
  · intro he
    obtain ⟨i,hi,hxOut,hdOut⟩:=pointedResidueActive_misses M f hx hh
    have ht:=congrArg (fun K:Deligne M=>K.val.1) he
    have hiTop:i∈(pointedResidueUpperTop M f P X q hx).val.1:=by rw [ht];exact hi
    exact hiTop.elim hxOut hdOut

lemma pointedResidueUpperClip_mem {P X R:Deligne M} {q:ℤ}
    (h: X<R ∧ R<P ∧ pointedResidueHeight M f P R q≤ pointedResidueHeight M f P X q) :
    X<pointedResidueUpperClip M f P X R q ∧ pointedResidueUpperClip M f P X R q<P ∧
      pointedResidueHeight M f P (pointedResidueUpperClip M f P X R q) q≤ pointedResidueHeight M f P X q := by
  have hl:=le_pointedResidueUpperClip M f (P:=P) (q:=q) h.1.le
  refine ⟨lt_of_le_of_ne hl ?_,(pointedResidueUpperClip_le M f h.1.le).trans_lt h.2.1,
    pointedResidueUpper_active M f hl (fun _ hi hn=>hi.2.resolve_left hn)⟩
  intro he
  obtain ⟨i,hi,hd⟩:=pointedResidueUpper_meets M f h.1 h.2.1.le h.2.2
  have ht:=congrArg (fun K:Deligne M=>K.val.1) he
  have hm:i∈(pointedResidueUpperClip M f P X R q).val.1:=⟨hi,Or.inr hd⟩
  rw [←ht] at hm
  exact hd.2.1 hm

noncomputable def pointedResidueUpperRetraction (P X:Deligne M) (q:ℤ) :
    PointedResidueEarlierUpper M f P X q →o PointedResidueEarlierUpper M f P X q where
  toFun R:=⟨pointedResidueUpperClip M f P X R q,pointedResidueUpperClip_mem M f R.property⟩
  monotone':=by
    intro Y Z h
    change pointedResidueUpperClip M f P X Y q≤ pointedResidueUpperClip M f P X Z q
    exact sourceCoset_le M (show Y.val.val.1 ∩ (X.val.1 ∪ pointedResidueActive M f P X q)⊆
      Z.val.val.1 ∩ (X.val.1 ∪ pointedResidueActive M f P X q) from fun _ hi=>⟨h.1 hi.1,hi.2⟩) _

theorem pointedResidueEarlierUpper_contractible {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:pointedResidueHeight M f P X q<0) (h:Nonempty (PointedResidueEarlierUpper M f P X q)) :
    ContractibleSpace |CategoryTheory.nerve (PointedResidueEarlierUpper M f P X q)| := by
  let R:=Classical.choice h
  obtain ⟨i,_,hi⟩:=pointedResidueUpper_meets M f R.property.1 R.property.2.1.le R.property.2.2
  let c:PointedResidueEarlierUpper M f P X q:=⟨pointedResidueUpperTop M f P X q hx,
    pointedResidueUpperTop_mem M f hx hh ⟨i,hi⟩⟩
  exact nerve_contractible_of_order_clip (pointedResidueUpperRetraction M f P X q) c
    (by intro R; change pointedResidueUpperClip M f P X R q≤R.val
        exact pointedResidueUpperClip_le M f R.property.1.le)
    (fun R=>show pointedResidueUpperClip M f P X R q≤ pointedResidueUpperTop M f P X q hx from
      sourceCoset_le M Set.inter_subset_right _)

end HarmonicArtin.ParabolicIntersections

end OAI
