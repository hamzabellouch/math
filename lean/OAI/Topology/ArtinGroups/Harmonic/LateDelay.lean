import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.EarlyDelay

namespace OAI

namespace HarmonicArtin
open scoped unitInterval
open Topology

attribute [local instance] Classical.propDecidable
universe u v
variable {A:Type u} {X:Type v} [TopologicalSpace A] [TopologicalSpace X] [T2Space X]

abbrev LateDelay (δ:C(X,I)) := {p:I×X // δ p.2≤p.1}

noncomputable def lateDelayTime (δ:C(X,I)) (hd:∀x,δ x<1) : C(LateDelay δ,I) where
  toFun p:=⟨(p.val.1.val-(δ p.val.2).val)/(1-(δ p.val.2).val),by
    have hpos:0<1-(δ p.val.2).val:=sub_pos.mpr (hd _)
    exact ⟨div_nonneg (sub_nonneg.mpr p.property) hpos.le,
      (div_le_one hpos).mpr (sub_le_sub_right p.val.1.property.2 _)⟩⟩
  continuous_toFun:=by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).sub
      (continuous_subtype_val.comp (δ.continuous.comp (continuous_snd.comp continuous_subtype_val)))).div
      (continuous_const.sub (continuous_subtype_val.comp (δ.continuous.comp (continuous_snd.comp continuous_subtype_val))))
      (fun p=>ne_of_gt (sub_pos.mpr (hd _)))

variable (i:C(A,X)) (r:C(X,A)) (hr:∀a,r (i a)=a)
  (D:ContinuousMap.HomotopyRel (ContinuousMap.id X) (i.comp r) (Set.range i))
  (δ:C(X,I)) (hd:∀x,δ x<1) (hz:∀x,δ x=0↔x∈Set.range i)
  (c:A) (H:ContinuousMap.Homotopy (ContinuousMap.id A) (ContinuousMap.const A c))

include hz in
omit [T2Space X] in
lemma extension_stationary (x:X) (hx:δ x=0) (t:I) : D (t,x)=D (0,x) := by
  rw [D.eq_fst t ((hz x).mp hx),D.apply_zero]

noncomputable def extensionEarly : C(EarlyDelay δ,X) :=
  earlyDelayContinuous δ D.toHomotopy.toContinuousMap (extension_stationary i r D δ hz)

noncomputable def extensionLate : C(LateDelay δ,X) :=
  i.comp (H.toContinuousMap.comp ((lateDelayTime δ hd).prodMk (r.comp ⟨fun p=>p.val.2,continuous_snd.comp continuous_subtype_val⟩)))

lemma extension_agree (x:X) :
    extensionEarly i r D δ hz ⟨(δ x,x),le_rfl⟩=
      extensionLate i r δ hd c H ⟨(δ x,x),le_rfl⟩ := by
  have he:earlyDelayMap δ (1,x)=⟨(δ x,x),le_rfl⟩:=by apply Subtype.ext;simp [earlyDelayMap]
  change earlyDelayValue δ D.toHomotopy.toContinuousMap _=_
  rw [←he,earlyDelayValue_map δ D.toHomotopy.toContinuousMap (extension_stationary i r D δ hz)]
  change D (1,x)=i (H (lateDelayTime δ hd ⟨(δ x,x),le_rfl⟩,r x))
  have ht:lateDelayTime δ hd ⟨(δ x,x),le_rfl⟩=0:=by apply Subtype.ext;simp [lateDelayTime]
  rw [ht,D.apply_one,H.apply_zero]
  rfl

noncomputable def extensionValue (p:I×X) : X :=
  if h:p.1≤δ p.2 then extensionEarly i r D δ hz ⟨p,h⟩
  else extensionLate i r δ hd c H ⟨p,le_of_not_ge h⟩

lemma extensionValue_early (p:EarlyDelay δ) :
    extensionValue i r D δ hd hz c H p.val=extensionEarly i r D δ hz p := by
  simp only [extensionValue,dite_eq_left p.property]

lemma extensionValue_late (p:LateDelay δ) :
    extensionValue i r D δ hd hz c H p.val=extensionLate i r δ hd c H p := by
  dsimp only [extensionValue]
  split_ifs with h
  · have he:p.val.1=δ p.val.2:=le_antisymm h p.property
    obtain ⟨⟨t,x⟩,hp⟩:=p
    change t=δ x at he
    subst t
    exact extension_agree i r D δ hd hz c H x
  · rfl

lemma extensionValue_continuous : Continuous (extensionValue i r D δ hd hz c H) := by
  let B:Bool→Set (I×X):=fun b=>if b then {p | p.1≤δ p.2} else {p | δ p.2≤p.1}
  apply (locallyFinite_of_finite B).continuous
  · apply Set.iUnion_eq_univ_iff.mpr
    intro p
    rcases le_total p.1 (δ p.2) with h|h
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩
  · intro b
    cases b
    · exact isClosed_le (δ.continuous.comp continuous_snd) continuous_fst
    · exact isClosed_le continuous_fst (δ.continuous.comp continuous_snd)
  · intro b
    rw [continuousOn_iff_continuous_domRestrict]
    cases b
    · exact (extensionLate i r δ hd c H).continuous.congr (fun p=>(extensionValue_late i r D δ hd hz c H p).symm)
    · exact (extensionEarly i r D δ hz).continuous.congr (fun p=>(extensionValue_early i r D δ hd hz c H p).symm)

noncomputable def extendContraction :
    ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X (i c)) where
  toFun:=extensionValue i r D δ hd hz c H
  continuous_toFun:=extensionValue_continuous i r D δ hd hz c H
  map_zero_left:=by
    intro x
    rw [show (0,x)=(earlyDelayMap δ (0,x)).val by simp [earlyDelayMap],extensionValue_early]
    exact (earlyDelayValue_map δ D.toHomotopy.toContinuousMap (extension_stationary i r D δ hz) (0,x)).trans (D.apply_zero x)
  map_one_left:=by
    intro x
    rw [show (1,x)=(⟨(1,x),le_of_lt (hd x)⟩:LateDelay δ).val from rfl,extensionValue_late]
    change i (H (lateDelayTime δ hd ⟨(1,x),le_of_lt (hd x)⟩,r x))=i c
    have ht:lateDelayTime δ hd ⟨(1,x),le_of_lt (hd x)⟩=1:=by
      apply Subtype.ext
      exact div_self (ne_of_gt (sub_pos.mpr (hd x)))
    rw [ht,H.apply_one]
    rfl

include hr in
lemma extendContraction_old (t:I) (a:A) :
    extendContraction i r D δ hd hz c H (t,i a)=i (H (t,a)) := by
  have he:δ (i a)=0:=(hz _).mpr ⟨a,rfl⟩
  have hlate:δ (i a)≤t:=he ▸ t.property.1
  change extensionValue i r D δ hd hz c H (t,i a)=_
  rw [show (t,i a)=(⟨(t,i a),hlate⟩:LateDelay δ).val from rfl,extensionValue_late]
  change i (H (lateDelayTime δ hd ⟨(t,i a),hlate⟩,r (i a)))=_
  have ht:lateDelayTime δ hd ⟨(t,i a),hlate⟩=t:=by
    apply Subtype.ext
    simp [lateDelayTime,he]
  rw [ht,hr]

end HarmonicArtin

end OAI
