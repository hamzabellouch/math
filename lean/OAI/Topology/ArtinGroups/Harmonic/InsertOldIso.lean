import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightVertexRetract
import OAI.Topology.ArtinGroups.Realizations.WeightHomeomorph

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def insertOldIso (A:Set P) (v:P) (hv:v∉A) :
    A≃oWeightOld (⟨v,Set.mem_insert v A⟩:↥(insert v A)) where
  toFun x:=⟨⟨x.val,Set.mem_insert_of_mem v x.property⟩,by
    intro he
    have he':x.val=v:=congrArg Subtype.val he
    exact hv (he' ▸ x.property)⟩
  invFun x:=⟨x.val.val,(Set.mem_insert_iff.mp x.val.property).resolve_left (by
    intro he
    exact x.property (Subtype.ext he))⟩
  left_inv x:=rfl
  right_inv x:=rfl
  map_rel_iff':=by intros;rfl

abbrev WeightEarlierLink (r:P→P→Prop) (v:P) := {x:P // r x v ∧ (x≤v ∨ v≤x)}

noncomputable def insertLinkIso (r:P→P→Prop) (hirr:∀x,¬r x x)
    (A:Set P) (v:P) (heA:∀x,x∈A↔r x v) :
    WeightLink (⟨v,Set.mem_insert v A⟩:↥(insert v A))≃oWeightEarlierLink r v where
  toFun x:=⟨x.val.val,(heA _).mp ((Set.mem_insert_iff.mp x.val.property).resolve_left
    (fun he=>x.property.1 (Subtype.ext he))),x.property.2⟩
  invFun x:=⟨⟨x.val,Set.mem_insert_of_mem v ((heA _).mpr x.property.1)⟩,
    (by
      intro he
      have he':x.val=v:=congrArg Subtype.val he
      have hr : r x.val v := x.property.1
      rw [he'] at hr
      exact hirr v hr),x.property.2⟩
  left_inv x:=rfl
  right_inv x:=rfl
  map_rel_iff':=by intros;rfl

lemma insertOldIso_incl (A:Set P) (v:P) (hv:v∉A) :
    (weightOldIncl (⟨v,Set.mem_insert v A⟩:↥(insert v A))).comp (OrderHom.ofClass (insertOldIso A v hv)) =
      weightSubset A (insert v A) (Set.subset_insert v A) :=rfl

variable (A:Set P) (v:P) (hv:v∉A)
  (l:OrderWeights (WeightLink (⟨v,Set.mem_insert v A⟩:↥(insert v A))))
  (L:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ l))
  (a:OrderWeights A) (H:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ a))

noncomputable def weightInsertContraction :
    ContinuousMap.Homotopy (ContinuousMap.id (OrderWeights ↥(insert v A)))
      (ContinuousMap.const _ (weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) a)) := by
  let e:=weightHomeomorph (insertOldIso A v hv)
  let K:=transportContraction e a H
  let E:=weightExtendContraction (⟨v,Set.mem_insert v A⟩:↥(insert v A)) l L (e a) K
  refine E.cast rfl ?_
  apply ContinuousMap.ext
  intro w
  change weightMap (weightOldIncl _) (weightMap (OrderHom.ofClass (insertOldIso A v hv)) a)=_
  rw [weightMap_comp,insertOldIso_incl]
  rfl

lemma weightInsertContraction_old (t:I) (w:OrderWeights A) :
    weightInsertContraction A v hv l L a H (t,weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) w)=
      weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) (H (t,w)) := by
  let e:=weightHomeomorph (insertOldIso A v hv)
  have he:weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) w=
      weightOldMap (⟨v,Set.mem_insert v A⟩:↥(insert v A)) (e w):=by
    change _=weightMap (weightOldIncl _) (weightMap (OrderHom.ofClass (insertOldIso A v hv)) w)
    rw [weightMap_comp,insertOldIso_incl]
  rw [he]
  change weightExtendContraction _ l L (e a) (transportContraction e a H) (t,weightOldMap _ (e w))=_
  rw [weightExtendContraction_old]
  change weightMap (weightOldIncl _) (e (H (t,e.symm (e w))))=_
  rw [e.symm_apply_apply]
  change weightMap (weightOldIncl _) (weightMap (OrderHom.ofClass (insertOldIso A v hv)) (H (t,w)))=_
  rw [weightMap_comp,insertOldIso_incl]

end HarmonicArtin

end OAI
