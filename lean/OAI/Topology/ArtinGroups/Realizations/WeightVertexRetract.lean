import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightAttach
import OAI.Topology.ArtinGroups.Harmonic.LateDelay

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

universe u
variable {P:Type u} [PartialOrder P] (v:P)
  (c:OrderWeights (WeightLink v))
  (H:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ c))

noncomputable def weightVertexRetract : C(OrderWeights P,OrderWeights (WeightOld v)) :=
  (coneAttachmentRetract (weightLinkMap v) c H).comp ⟨(weightAttachHomeomorph v c).symm,(weightAttachHomeomorph v c).symm.continuous⟩

lemma weightVertexRetract_old (w:OrderWeights (WeightOld v)) :
    weightVertexRetract v c H (weightOldMap v w)=w := by
  change coneAttachmentRetract _ c H ((weightAttachEquiv v c).symm (weightOldMap v w))=w
  rw [weightAttachEquiv_symm_old]
  rfl

noncomputable def weightVertexDeformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id (OrderWeights P))
      ((weightOldMap v).comp (weightVertexRetract v c H)) (Set.range (weightOldMap v)) where
  toFun p:=weightAttach v (coneAttachmentDeformation (weightLinkMap v) c H
    (p.1,(weightAttachHomeomorph v c).symm p.2))
  continuous_toFun:=(weightAttach v).continuous.comp
    ((coneAttachmentDeformation (weightLinkMap v) c H).continuous.comp
      (continuous_fst.prodMk ((weightAttachHomeomorph v c).symm.continuous.comp continuous_snd)))
  map_zero_left:=by
    intro w
    rw [(coneAttachmentDeformation (weightLinkMap v) c H).apply_zero]
    exact (weightAttachHomeomorph v c).apply_symm_apply w
  map_one_left:=by
    intro w
    rw [(coneAttachmentDeformation (weightLinkMap v) c H).apply_one]
    rfl
  prop' t w hw:=by
    obtain ⟨a,rfl⟩:=hw
    change weightAttach v (coneAttachmentDeformation (weightLinkMap v) c H
      (t,(weightAttachEquiv v c).symm (weightOldMap v a)))=_
    rw [weightAttachEquiv_symm_old]
    rw [(coneAttachmentDeformation (weightLinkMap v) c H).eq_fst t ⟨a,rfl⟩]
    rfl

noncomputable def weightVertexDelay (v:P) : C(OrderWeights P,I) where
  toFun w:=⟨w.weights v/2,by
    constructor
    · exact div_nonneg (w.nonneg v) (by norm_num)
    · have hh:=weight_le_one w v;linarith⟩
  continuous_toFun:=by
    apply Continuous.subtype_mk
    exact (weightEval_continuous v).div_const 2

lemma weightVertexDelay_lt (w:OrderWeights P) : weightVertexDelay v w<1 := by
  change w.weights v/2<1
  have hh:=weight_le_one w v
  linarith

lemma weightVertexDelay_zero (w:OrderWeights P) :
    weightVertexDelay v w=0↔w∈Set.range (weightOldMap v) := by
  constructor
  · intro h
    have hz:w.weights v=0:=by
      have he:=congrArg Subtype.val h
      change w.weights v/2=0 at he
      linarith
    exact weightOld_surjective_zero w hz
  · rintro ⟨w,rfl⟩
    apply Subtype.ext
    change (weightOldMap v w).weights v/2=0
    rw [weightOldMap_at,zero_div]

variable (a:OrderWeights (WeightOld v))
  (K:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ a))

noncomputable def weightExtendContraction :
    ContinuousMap.Homotopy (ContinuousMap.id (OrderWeights P))
      (ContinuousMap.const _ (weightOldMap v a)) :=
  extendContraction (weightOldMap v) (weightVertexRetract v c H)
    (weightVertexDeformation v c H) (weightVertexDelay v)
    (weightVertexDelay_lt v) (weightVertexDelay_zero v) a K

lemma weightExtendContraction_old (t:I) (w:OrderWeights (WeightOld v)) :
    weightExtendContraction v c H a K (t,weightOldMap v w)=weightOldMap v (K (t,w)) :=
  extendContraction_old (weightOldMap v) (weightVertexRetract v c H)
    (weightVertexRetract_old v c H) (weightVertexDeformation v c H)
    (weightVertexDelay v) (weightVertexDelay_lt v) (weightVertexDelay_zero v) a K t w

end HarmonicArtin

end OAI
