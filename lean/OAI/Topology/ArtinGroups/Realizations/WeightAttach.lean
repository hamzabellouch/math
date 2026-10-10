import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightLinearLinkInverse
import OAI.Topology.ArtinGroups.Harmonic.ConeAttachmentRel

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P] (v:P)

noncomputable def weightAttach : C(ConeAttachment (weightLinkMap v),OrderWeights P) where
  toFun:=Quot.lift (Sum.elim (weightOldMap v) (weightConeMap v)) (by
    intro a b h
    cases h with
    | base x => exact weightConeMap_zero v x
    | apex x y => exact (weightConeMap_one v x).trans (weightConeMap_one v y).symm)
  continuous_toFun:=continuous_quot_lift _ (continuous_sum_dom.mpr ⟨(weightOldMap v).continuous,(weightConeMap v).continuous⟩)

lemma weightAttach_old (w:OrderWeights (WeightOld v)) :
    weightAttach v (coneAttachmentOld (weightLinkMap v) w)=weightOldMap v w :=rfl
lemma weightAttach_cone (p:I×OrderWeights (WeightLink v)) :
    weightAttach v (coneAttachmentCone (weightLinkMap v) p)=weightConeMap v p :=rfl

lemma weightAttach_surjective (c:OrderWeights (WeightLink v)) : Function.Surjective (weightAttach v) := by
  intro w
  obtain ⟨p,hp⟩:=weightParts_surjective v c w
  exact ⟨Quot.mk _ p,hp⟩

lemma weightAttach_injective : Function.Injective (weightAttach v) := by
  intro a b
  induction a using Quot.inductionOn with
  | h a =>
    induction b using Quot.inductionOn with
    | h b =>
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          intro h
          have hab:a=b:=weightMap_injective (weightOldIncl v) Subtype.val_injective h
          subst b;rfl
        | inr b =>
          intro h
          have ht:b.1=0:=Subtype.ext (by
            have he:=congrArg (fun w:OrderWeights P=>w.weights v) h
            change (weightOldMap v a).weights v=(weightConeMap v b).weights v at he
            rw [weightOldMap_at,weightConeMap_at] at he
            exact he.symm)
          obtain ⟨t,b⟩:=b
          dsimp only at ht
          subst t
          change weightOldMap v a=weightConeMap v (0,b) at h
          rw [weightConeMap_zero] at h
          have ha:a=weightLinkMap v b:=weightMap_injective (weightOldIncl v) Subtype.val_injective h
          subst a
          exact (coneAttachment_base (weightLinkMap v) b).symm
      | inr a =>
        cases b with
        | inl b =>
          intro h
          have ht:a.1=0:=Subtype.ext (by
            have he:=congrArg (fun w:OrderWeights P=>w.weights v) h
            change (weightConeMap v a).weights v=(weightOldMap v b).weights v at he
            rw [weightOldMap_at,weightConeMap_at] at he
            exact he)
          obtain ⟨t,a⟩:=a
          dsimp only at ht
          subst t
          change weightConeMap v (0,a)=weightOldMap v b at h
          rw [weightConeMap_zero] at h
          have hb:weightLinkMap v a=b:=weightMap_injective (weightOldIncl v) Subtype.val_injective h
          subst b
          exact coneAttachment_base (weightLinkMap v) a
        | inr b =>
          intro h
          obtain ⟨t,a⟩:=a
          obtain ⟨s,b⟩:=b
          obtain ⟨he,hh⟩:=weightConeMap_eq_cone h
          subst s
          rcases hh with ht|hab
          · subst t
            exact coneAttachment_apex (weightLinkMap v) a b
          · subst b;rfl

noncomputable def weightAttachEquiv (c:OrderWeights (WeightLink v)) :
    ConeAttachment (weightLinkMap v) ≃ OrderWeights P :=
  Equiv.ofBijective (weightAttach v) ⟨weightAttach_injective v,weightAttach_surjective v c⟩

lemma weightAttachEquiv_symm_old (c:OrderWeights (WeightLink v)) (w:OrderWeights (WeightOld v)) :
    (weightAttachEquiv v c).symm (weightOldMap v w)=coneAttachmentOld (weightLinkMap v) w := by
  apply (weightAttachEquiv v c).symm_apply_eq.mpr
  rfl

lemma weightAttachEquiv_symm_cone (c:OrderWeights (WeightLink v)) (p:I×OrderWeights (WeightLink v)) :
    (weightAttachEquiv v c).symm (weightConeMap v p)=coneAttachmentCone (weightLinkMap v) p := by
  apply (weightAttachEquiv v c).symm_apply_eq.mpr
  rfl

noncomputable def weightAttachHomeomorph (c:OrderWeights (WeightLink v)) :
    ConeAttachment (weightLinkMap v) ≃ₜ OrderWeights P where
  toEquiv:=weightAttachEquiv v c
  continuous_toFun:=(weightAttach v).continuous
  continuous_invFun:=by
    change Continuous (weightAttachEquiv v c).symm
    apply continuous_of_weightParts v
    · have he:(weightAttachEquiv v c).symm ∘ weightOldMap v=coneAttachmentOld (weightLinkMap v):=by
        funext w;exact weightAttachEquiv_symm_old v c w
      rw [he]
      exact (coneAttachmentOld (weightLinkMap v)).continuous
    · have he:(weightAttachEquiv v c).symm ∘ weightConeMap v=coneAttachmentCone (weightLinkMap v):=by
        funext w;exact weightAttachEquiv_symm_cone v c w
      rw [he]
      exact (coneAttachmentCone (weightLinkMap v)).continuous

end HarmonicArtin

end OAI
