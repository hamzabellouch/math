import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

universe u v
variable {A:Type u} {L:Type v} [TopologicalSpace A] [TopologicalSpace L]

inductive ConeAttachmentRel (f:C(L,A)) : (A ⊕ (I×L))→(A ⊕ (I×L))→Prop
  | base (x:L) : ConeAttachmentRel f (.inr (0,x)) (.inl (f x))
  | apex (x y:L) : ConeAttachmentRel f (.inr (1,x)) (.inr (1,y))

abbrev ConeAttachment (f:C(L,A)) := Quot (ConeAttachmentRel f)

noncomputable def coneAttachmentOld (f:C(L,A)) : C(A,ConeAttachment f) :=
  ⟨fun a=>Quot.mk _ (.inl a),continuous_quot_mk.comp continuous_inl⟩

noncomputable def coneAttachmentCone (f:C(L,A)) : C(I×L,ConeAttachment f) :=
  ⟨fun p=>Quot.mk _ (.inr p),continuous_quot_mk.comp continuous_inr⟩

lemma coneAttachment_base (f:C(L,A)) (x:L) :
    coneAttachmentCone f (0,x)=coneAttachmentOld f (f x) := Quot.sound (.base x)

lemma coneAttachment_apex (f:C(L,A)) (x y:L) :
    coneAttachmentCone f (1,x)=coneAttachmentCone f (1,y) := Quot.sound (.apex x y)

lemma continuous_prod_sum_elim {B X Y Z:Type*} [TopologicalSpace B]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (g:B×(X⊕Y)→Z)
    (hx:Continuous (fun p:B×X=>g (p.1,.inl p.2)))
    (hy:Continuous (fun p:B×Y=>g (p.1,.inr p.2))) : Continuous g := by
  have h:= (hx.sumElim hy).comp (Homeomorph.prodSumDistrib (X:=B) (Y:=X) (Z:=Y)).continuous
  convert h using 1
  funext p
  rcases p with ⟨b,x|y⟩ <;> rfl

section Contracting
variable (f:C(L,A)) (c:L) (H:ContinuousMap.Homotopy (ContinuousMap.id L) (ContinuousMap.const L c))

noncomputable def coneAttachmentRetract : C(ConeAttachment f,A) where
  toFun:=Quot.lift (Sum.elim id (fun p:I×L=>f (H p))) (by
    intro a b h
    cases h with
    | base x => simp only [Sum.elim_inr,Sum.elim_inl,H.apply_zero,ContinuousMap.id_apply,id_eq]
    | apex x y => simp only [Sum.elim_inr,H.apply_one,ContinuousMap.const_apply])
  continuous_toFun:=continuous_quot_lift _ (continuous_sum_dom.mpr ⟨continuous_id,f.continuous.comp H.continuous⟩)

lemma coneAttachmentRetract_old (a:A) :
    coneAttachmentRetract f c H (coneAttachmentOld f a)=a := rfl

noncomputable def coneAttachmentMiddle : C(ConeAttachment f,ConeAttachment f) where
  toFun:=Quot.lift (Sum.elim (coneAttachmentOld f) (fun p:I×L=>coneAttachmentCone f (p.1,H p))) (by
    intro a b h
    cases h with
    | base x => simpa only [Sum.elim_inr,Sum.elim_inl,H.apply_zero,ContinuousMap.id_apply] using coneAttachment_base f x
    | apex x y => exact coneAttachment_apex f _ _)
  continuous_toFun:=continuous_quot_lift _ (continuous_sum_dom.mpr
    ⟨(coneAttachmentOld f).continuous,(coneAttachmentCone f).continuous.comp (continuous_fst.prodMk H.continuous)⟩)

noncomputable def coneAttachmentFirstFun (t:I) : ConeAttachment f→ ConeAttachment f :=
  Quot.lift (Sum.elim (coneAttachmentOld f)
    (fun p:I×L=>coneAttachmentCone f (p.1,H (min t p.1,p.2)))) (by
    intro a b h
    cases h with
    | base x =>
      simpa [min_eq_right (show (0:I)≤t from t.property.1)] using coneAttachment_base f x
    | apex x y => exact coneAttachment_apex f _ _)

noncomputable def coneAttachmentFirst :
    ContinuousMap.HomotopyRel (ContinuousMap.id (ConeAttachment f)) (coneAttachmentMiddle f c H)
      (Set.range (coneAttachmentOld f)) where
  toFun p:=coneAttachmentFirstFun f c H p.1 p.2
  continuous_toFun:=by
    apply isQuotientMap_quot_mk.continuous_lift_prod_right
    apply continuous_prod_sum_elim
    · exact (coneAttachmentOld f).continuous.comp continuous_snd
    · exact (coneAttachmentCone f).continuous.comp
        (continuous_snd.fst.prodMk (H.continuous.comp
          ((continuous_fst.min continuous_snd.fst).prodMk continuous_snd.snd)))
  map_zero_left:=by
    intro p
    induction p using Quot.inductionOn with
    | h p =>
      cases p with
      | inl a => rfl
      | inr p => simp [coneAttachmentFirstFun,coneAttachmentCone]
  map_one_left:=by
    intro p
    induction p using Quot.inductionOn with
    | h p =>
      cases p with
      | inl a => rfl
      | inr p => simp [coneAttachmentFirstFun,min_eq_right (show p.1≤(1:I) from p.1.property.2),coneAttachmentMiddle]
  prop' t p hp:=by
    obtain ⟨a,rfl⟩:=hp
    rfl

noncomputable def coneAttachmentSecondFun (t:I) : ConeAttachment f→ ConeAttachment f :=
  Quot.lift (Sum.elim (coneAttachmentOld f)
    (fun p:I×L=>coneAttachmentCone f ((σ t)*p.1,H p))) (by
    intro a b h
    cases h with
    | base x =>
      simpa only [Sum.elim_inr,Sum.elim_inl,mul_zero,H.apply_zero,ContinuousMap.id_apply] using coneAttachment_base f x
    | apex x y => simp only [Sum.elim_inr,H.apply_one,ContinuousMap.const_apply])

noncomputable def coneAttachmentSecond :
    ContinuousMap.HomotopyRel (coneAttachmentMiddle f c H)
      ((coneAttachmentOld f).comp (coneAttachmentRetract f c H))
      (Set.range (coneAttachmentOld f)) where
  toFun p:=coneAttachmentSecondFun f c H p.1 p.2
  continuous_toFun:=by
    apply isQuotientMap_quot_mk.continuous_lift_prod_right
    apply continuous_prod_sum_elim
    · exact (coneAttachmentOld f).continuous.comp continuous_snd
    · exact (coneAttachmentCone f).continuous.comp
        (((unitInterval.continuous_symm.comp continuous_fst).mul continuous_snd.fst).prodMk
          (H.continuous.comp continuous_snd))
  map_zero_left:=by
    intro p
    induction p using Quot.inductionOn with
    | h p =>
      cases p with
      | inl a => rfl
      | inr p => simp only [coneAttachmentSecondFun,Sum.elim_inr,unitInterval.symm_zero,one_mul];rfl
  map_one_left:=by
    intro p
    induction p using Quot.inductionOn with
    | h p =>
      cases p with
      | inl a => rfl
      | inr p =>
        simp only [coneAttachmentSecondFun,Sum.elim_inr,unitInterval.symm_one,zero_mul]
        exact coneAttachment_base f (H p)
  prop' t p hp:=by
    obtain ⟨a,rfl⟩:=hp
    rfl

noncomputable def coneAttachmentDeformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id (ConeAttachment f))
      ((coneAttachmentOld f).comp (coneAttachmentRetract f c H))
      (Set.range (coneAttachmentOld f)) :=
  (coneAttachmentFirst f c H).trans (coneAttachmentSecond f c H)

noncomputable def coneAttachmentEquiv : ContinuousMap.HomotopyEquiv (ConeAttachment f) A where
  toFun:=coneAttachmentRetract f c H
  invFun:=coneAttachmentOld f
  left_inv:=⟨(coneAttachmentDeformation f c H).toHomotopy.symm⟩
  right_inv:=by
    have he:(coneAttachmentRetract f c H).comp (coneAttachmentOld f)=ContinuousMap.id A:=by ext a;rfl
    rw [he]

end Contracting
end HarmonicArtin

end OAI
