import Mathlib
import OAI.Topology.ArtinGroups.Realizations.NerveOrderMap
import OAI.Topology.ArtinGroups.Harmonic.HarmonicUpperAntitone
import OAI.Topology.ArtinGroups.Harmonic.ResidueAllowed

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceCosetVector_upper_antitone_int {X R:Deligne M} (h:X≤R) (q:ℤ)
    (hr:∀i∈R.val.1,i∉X.val.1→0≤(framedCartan M *ᵥ sourceCosetVector M X q) (.inl i)) :
    sourceCosetVector M R q≤ sourceCosetVector M X q := by
  apply harmonic_upper_antitone (framedCartan M) (framedCartan_off M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (sourceCosetVector M X q) (sourceCosetVector M R q)
    (sourceCosetVector_upper_outside M h q) (sourceCosetVector_harmonic M R q)
  rintro ⟨_,⟨i,hi,rfl⟩⟩
  by_cases ht:i∈X.val.1
  · rw [sourceCosetVector_harmonic M X q ⟨.inl i,⟨i,ht,rfl⟩⟩]
  · exact hr i hi ht

lemma sourceCosetVector_upper_monotone_int {X R:Deligne M} (h:X≤R) (q:ℤ)
    (hr:∀i∈R.val.1,i∉X.val.1→(framedCartan M *ᵥ sourceCosetVector M X q) (.inl i)≤0) :
    sourceCosetVector M X q≤ sourceCosetVector M R q := by
  apply harmonic_upper_monotone (framedCartan M) (framedCartan_off M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (sourceCosetVector M X q) (sourceCosetVector M R q)
    (sourceCosetVector_upper_outside M h q) (sourceCosetVector_harmonic M R q)
  rintro ⟨_,⟨i,hi,rfl⟩⟩
  by_cases ht:i∈X.val.1
  · rw [sourceCosetVector_harmonic M X q ⟨.inl i,⟨i,ht,rfl⟩⟩]
  · exact hr i hi ht

lemma sourceResidueHeight_lt_of_ne {P Q R:Deligne M} {q:ℤ} (hQ:Q≤P) (hR:R≤P)
    (h:sourceCosetVector M Q q≤ sourceCosetVector M R q)
    (hn:sourceCosetVector M Q q≠sourceCosetVector M R q) :
    sourceResidueHeight M P Q q<sourceResidueHeight M P R q := by
  apply sourceResidueHeight_lt M h
  by_contra he
  apply hn
  funext v
  by_cases hv:v∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨i,hi,rfl⟩:=hv
    exact le_antisymm (h _) (le_of_not_gt (fun hl=>he ⟨i,hi,hl⟩))
  · exact (sourceCosetVector_upper_outside M hQ q v hv).symm.trans
      (sourceCosetVector_upper_outside M hR q v hv)

def sourceResidueActive (P X:Deligne M) (q:ℤ) : Set S :=
  {i | i∈P.val.1 ∧ i∉X.val.1 ∧ 0≤(framedCartan M *ᵥ sourceCosetVector M X q) (.inl i)}

lemma sourceResidueActive_misses {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:sourceResidueHeight M P X q<0) :
    ∃i∈P.val.1,i∉X.val.1 ∧ i∉sourceResidueActive M P X q := by
  by_contra hn
  have hv:sourceCosetVector M P q≤ sourceCosetVector M X q:=by
    apply sourceCosetVector_upper_antitone_int M hx q
    intro i hi hxi
    by_contra hr
    exact hn ⟨i,hi,hxi,fun hd=>hr hd.2.2⟩
  have hnon:0≤ sourceResidueHeight M P X q:=
    Finset.sum_nonneg (fun i _=>sub_nonneg.mpr (hv (.inl i)))
  exact (not_lt_of_ge hnon) hh

abbrev SourceResidueEarlierUpper (P X:Deligne M) (q:ℤ) :=
  {R:Deligne M // X<R ∧ R<P ∧ sourceResidueHeight M P R q≤ sourceResidueHeight M P X q}

lemma sourceResidueUpper_meets {P X R:Deligne M} {q:ℤ} (hr:X<R) (hp:R≤P)
    (hh:sourceResidueHeight M P R q≤ sourceResidueHeight M P X q) :
    ∃i∈R.val.1,i∈sourceResidueActive M P X q := by
  by_contra hn
  have hnrow:∀i∈R.val.1,i∉X.val.1→(framedCartan M *ᵥ sourceCosetVector M X q) (.inl i)<0:=by
    intro i hi hxi
    exact lt_of_not_ge (fun hh=>hn ⟨i,hi,hp.1 hi,hxi,hh⟩)
  have hv:=sourceCosetVector_upper_monotone_int M hr.le q (fun i hi hx=>(hnrow i hi hx).le)
  have hne:sourceCosetVector M X q≠sourceCosetVector M R q:=by
    intro he
    obtain ⟨i,hi,hxi⟩:=Set.exists_of_ssubset (deligne_lt_type M hr)
    have hh:=hnrow i hi hxi
    rw [he,sourceCosetVector_harmonic M R q ⟨.inl i,⟨i,hi,rfl⟩⟩] at hh
    exact lt_irrefl _ hh
  exact (not_lt_of_ge hh) (sourceResidueHeight_lt_of_ne M (hr.le.trans hp) hp hv hne)

lemma sourceResidueUpper_active {P X R:Deligne M} {q:ℤ} (hr:X≤R)
    (ha:∀i∈R.val.1,i∉X.val.1→i∈sourceResidueActive M P X q) :
    sourceResidueHeight M P R q≤ sourceResidueHeight M P X q :=
  sourceResidueHeight_mono M (sourceCosetVector_upper_antitone_int M hr q (fun i hi hn=>(ha i hi hn).2.2))

noncomputable def sourceResidueUpperTop (P X:Deligne M) (q:ℤ) (hx:X≤P) : Deligne M :=
  sourceCoset M (X.val.1 ∪ sourceResidueActive M P X q)
    (source_spherical_mono M (show X.val.1 ∪ sourceResidueActive M P X q⊆P.val.1 from
      fun _ hi=>hi.elim (fun h=>hx.1 h) (fun h=>h.1)) P.property.1)
    (sourceCosetRepresentative M X)

noncomputable def sourceResidueUpperClip (P X R:Deligne M) (q:ℤ) : Deligne M :=
  sourceCoset M (R.val.1 ∩ (X.val.1 ∪ sourceResidueActive M P X q))
    (source_spherical_mono M Set.inter_subset_left R.property.1) (sourceCosetRepresentative M X)

lemma sourceResidueUpperClip_le {P X R:Deligne M} {q:ℤ} (h:X≤R) :
    sourceResidueUpperClip M P X R q≤R := by
  calc
    sourceResidueUpperClip M P X R q≤ sourceCoset M R.val.1 R.property.1 (sourceCosetRepresentative M X):=
      sourceCoset_le M Set.inter_subset_left _
    _=R:=sourceCoset_eq M R _ (h.2 (sourceCosetRepresentative_mem M X))

lemma le_sourceResidueUpperClip {P X R:Deligne M} {q:ℤ} (h:X≤R) :
    X≤ sourceResidueUpperClip M P X R q := by
  calc
    X=sourceCoset M X.val.1 X.property.1 (sourceCosetRepresentative M X):=
      (sourceCoset_eq M X _ (sourceCosetRepresentative_mem M X)).symm
    _≤ sourceResidueUpperClip M P X R q:=sourceCoset_le M (show X.val.1⊆R.val.1 ∩ (X.val.1 ∪ sourceResidueActive M P X q) from
      fun i hi=>⟨h.1 hi,Or.inl hi⟩) _

lemma sourceResidueUpperTop_mem {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:sourceResidueHeight M P X q<0) (hd:(sourceResidueActive M P X q).Nonempty) :
    X<sourceResidueUpperTop M P X q hx ∧ sourceResidueUpperTop M P X q hx<P ∧
      sourceResidueHeight M P (sourceResidueUpperTop M P X q hx) q≤ sourceResidueHeight M P X q := by
  have hl:X≤ sourceResidueUpperTop M P X q hx:=by
    calc
      X=sourceCoset M X.val.1 X.property.1 (sourceCosetRepresentative M X):=
        (sourceCoset_eq M X _ (sourceCosetRepresentative_mem M X)).symm
      _≤ sourceResidueUpperTop M P X q hx:=sourceCoset_le M Set.subset_union_left _
  have hp:sourceResidueUpperTop M P X q hx≤P:=by
    calc
      sourceResidueUpperTop M P X q hx≤ sourceCoset M P.val.1 P.property.1 (sourceCosetRepresentative M X):=
        sourceCoset_le M (fun _ hi=>hi.elim (fun h=>hx.1 h) (fun h=>h.1)) _
      _=P:=sourceCoset_eq M P _ (hx.2 (sourceCosetRepresentative_mem M X))
  refine ⟨lt_of_le_of_ne hl ?_,lt_of_le_of_ne hp ?_,sourceResidueUpper_active M hl (fun _ hi hn=>hi.resolve_left hn)⟩
  · intro he
    obtain ⟨i,hi⟩:=hd
    have ht:=congrArg (fun K:Deligne M=>K.val.1) he
    have hiTop:i∈(sourceResidueUpperTop M P X q hx).val.1:=Or.inr hi
    rw [←ht] at hiTop
    exact hi.2.1 hiTop
  · intro he
    obtain ⟨i,hi,hxOut,hdOut⟩:=sourceResidueActive_misses M hx hh
    have ht:=congrArg (fun K:Deligne M=>K.val.1) he
    have hiTop:i∈(sourceResidueUpperTop M P X q hx).val.1:=by rw [ht];exact hi
    exact hiTop.elim hxOut hdOut

lemma sourceResidueUpperClip_mem {P X R:Deligne M} {q:ℤ}
    (h: X<R ∧ R<P ∧ sourceResidueHeight M P R q≤ sourceResidueHeight M P X q) :
    X<sourceResidueUpperClip M P X R q ∧ sourceResidueUpperClip M P X R q<P ∧
      sourceResidueHeight M P (sourceResidueUpperClip M P X R q) q≤ sourceResidueHeight M P X q := by
  have hl:=le_sourceResidueUpperClip M (P:=P) (q:=q) h.1.le
  refine ⟨lt_of_le_of_ne hl ?_,(sourceResidueUpperClip_le M h.1.le).trans_lt h.2.1,
    sourceResidueUpper_active M hl (fun _ hi hn=>hi.2.resolve_left hn)⟩
  intro he
  obtain ⟨i,hi,hd⟩:=sourceResidueUpper_meets M h.1 h.2.1.le h.2.2
  have ht:=congrArg (fun K:Deligne M=>K.val.1) he
  have hm:i∈(sourceResidueUpperClip M P X R q).val.1:=⟨hi,Or.inr hd⟩
  rw [←ht] at hm
  exact hd.2.1 hm

noncomputable def sourceResidueUpperRetraction (P X:Deligne M) (q:ℤ) :
    SourceResidueEarlierUpper M P X q →o SourceResidueEarlierUpper M P X q where
  toFun R:=⟨sourceResidueUpperClip M P X R q,sourceResidueUpperClip_mem M R.property⟩
  monotone':=by
    intro Y Z h
    change sourceResidueUpperClip M P X Y q≤ sourceResidueUpperClip M P X Z q
    exact sourceCoset_le M (show Y.val.val.1 ∩ (X.val.1 ∪ sourceResidueActive M P X q)⊆
      Z.val.val.1 ∩ (X.val.1 ∪ sourceResidueActive M P X q) from fun _ hi=>⟨h.1 hi.1,hi.2⟩) _

theorem sourceResidueEarlierUpper_contractible {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:sourceResidueHeight M P X q<0) (h:Nonempty (SourceResidueEarlierUpper M P X q)) :
    ContractibleSpace |CategoryTheory.nerve (SourceResidueEarlierUpper M P X q)| := by
  let R:=Classical.choice h
  obtain ⟨i,_,hi⟩:=sourceResidueUpper_meets M R.property.1 R.property.2.1.le R.property.2.2
  let c:SourceResidueEarlierUpper M P X q:=⟨sourceResidueUpperTop M P X q hx,
    sourceResidueUpperTop_mem M hx hh ⟨i,hi⟩⟩
  exact nerve_contractible_of_order_clip (sourceResidueUpperRetraction M P X q) c
    (by intro R; change sourceResidueUpperClip M P X R q≤R.val
        exact sourceResidueUpperClip_le M R.property.1.le)
    (fun R=>show sourceResidueUpperClip M P X R q≤ sourceResidueUpperTop M P X q hx from
      sourceCoset_le M Set.inter_subset_right _)

end HarmonicArtin

end OAI
