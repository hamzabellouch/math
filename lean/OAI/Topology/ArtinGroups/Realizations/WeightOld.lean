import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver
import OAI.Topology.ArtinGroups.Realizations.WeightInclusion

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

abbrev WeightOld (v:P) := {p:P // p≠v}
abbrev WeightLink (v:P) := {p:P // p≠v ∧ (p≤v ∨ v≤p)}
noncomputable abbrev weightOldIncl (v:P) : WeightOld v→o P :=⟨Subtype.val,fun _ _ h=>h⟩
noncomputable abbrev weightLinkIncl (v:P) : WeightLink v→o P :=⟨Subtype.val,fun _ _ h=>h⟩
noncomputable abbrev weightLinkOld (v:P) : WeightLink v→o WeightOld v :=⟨fun p=>⟨p.val,p.property.1⟩,fun _ _ h=>h⟩
noncomputable def weightOldMap (v:P) : C(OrderWeights (WeightOld v),OrderWeights P) :=
  ⟨weightMap (weightOldIncl v),weightMap_continuous _⟩
noncomputable def weightLinkMap (v:P) : C(OrderWeights (WeightLink v),OrderWeights (WeightOld v)) :=
  ⟨weightMap (weightLinkOld v),weightMap_continuous _⟩
noncomputable def weightConeMap (v:P) : C(I×OrderWeights (WeightLink v),OrderWeights P) :=
  coneWeightsContinuous (weightLinkIncl v) v (fun p=>p.property.2)

lemma weightMap_zero_of_not_range {Q:Type*} [PartialOrder Q] (f:Q→oP) (w:OrderWeights Q) (p:P)
    (hp:p∉Set.range f) : (weightMap f w).weights p=0 := by
  apply Finsupp.notMem_support_iff.mp
  intro h
  obtain ⟨q,_,he⟩:=Finset.mem_image.mp (Finsupp.mapDomain_support h)
  exact hp ⟨q,he⟩

lemma weightOldMap_at (v:P) (w:OrderWeights (WeightOld v)) : (weightOldMap v w).weights v=0 := by
  apply weightMap_zero_of_not_range
  rintro ⟨p,hp⟩
  exact p.property hp

lemma weightConeMap_at (v:P) (p:I×OrderWeights (WeightLink v)) :
    (weightConeMap v p).weights v=p.1.val := by
  rw [show weightConeMap v p=coneWeights (weightLinkIncl v) v (fun p=>p.property.2) p.1 p.2 from rfl,
    coneWeights_apply]
  have hz:(weightMap (weightLinkIncl v) p.2).weights v=0:=by
    apply weightMap_zero_of_not_range
    rintro ⟨q,hq⟩
    exact q.property.1 hq
  rw [hz,ite_eq_left rfl,mul_zero,zero_add]

lemma weightConeMap_zero (v:P) (w:OrderWeights (WeightLink v)) :
    weightConeMap v (0,w)=weightOldMap v (weightLinkMap v w) := by
  rw [show weightConeMap v (0,w)=coneWeights (weightLinkIncl v) v (fun p=>p.property.2) 0 w from rfl,
    coneWeights_zero]
  exact (weightMap_comp (weightLinkOld v) (weightOldIncl v) w).symm

lemma weightConeMap_one (v:P) (w:OrderWeights (WeightLink v)) :
    weightConeMap v (1,w)=weightVertex v := coneWeights_one_vertex (weightLinkIncl v) v (fun q=>q.property.2) w

lemma weightConeMap_eq_cone {v:P} {t s:I} {w z:OrderWeights (WeightLink v)}
    (h:weightConeMap v (t,w)=weightConeMap v (s,z)) : t=s ∧ (t=1 ∨ w=z) := by
  have ht:t=s:=Subtype.ext (by simpa only [weightConeMap_at] using congrArg (fun a:OrderWeights P=>a.weights v) h)
  subst s
  refine ⟨rfl,?_⟩
  by_cases he:t=1
  · exact Or.inl he
  right
  apply OrderWeights.ext
  ext p
  have hs:=congrArg (fun a:OrderWeights P=>a.weights p.val) h
  change (coneWeights (weightLinkIncl v) v (fun q=>q.property.2) t w).weights p.val=
    (coneWeights (weightLinkIncl v) v (fun q=>q.property.2) t z).weights p.val at hs
  simp only [coneWeights_apply,ite_eq_right (Ne.symm p.property.1),add_zero] at hs
  have hw:(weightMap (weightLinkIncl v) w).weights p.val=w.weights p:=
    weightMap_apply_embedding (weightLinkIncl v) Subtype.val_injective w p
  have hz:(weightMap (weightLinkIncl v) z).weights p.val=z.weights p:=
    weightMap_apply_embedding (weightLinkIncl v) Subtype.val_injective z p
  rw [hw,hz] at hs
  exact mul_left_cancel₀ (sub_ne_zero.mpr (fun h=>he (Subtype.ext h.symm))) hs

lemma weightOld_surjective_zero {v:P} (w:OrderWeights P) (hv:w.weights v=0) :
    ∃z:OrderWeights (WeightOld v),weightOldMap v z=w := by
  have hs:∀p∈w.weights.support,p≠v:=by
    intro p hp he;subst p
    exact Finsupp.mem_support_iff.mp hp hv
  exact ⟨weightRestrict {p | p≠v} w hs,weightRestrict_map _ w hs⟩

lemma weightDelete_link {v:P} (w:OrderWeights P) (ht:w.weights v<1) (hp:0<w.weights v) :
    ∀p∈(weightDelete v w ht).weights.support,p≠v ∧ (p≤v ∨ v≤p) := by
  intro p hp'
  have h:=Finset.mem_erase.mp (weightDelete_support v w ht hp')
  exact ⟨h.1,w.chain p h.2 v (Finsupp.mem_support_iff.mpr (ne_of_gt hp))⟩

lemma weightDelete_reconstruct {v:P} (w:OrderWeights P) (ht:w.weights v<1) (hp:0<w.weights v) :
    weightConeMap v (weightTime v w,weightRestrict {p | p≠v ∧ (p≤v ∨ v≤p)}
      (weightDelete v w ht) (weightDelete_link w ht hp))=w := by
  apply OrderWeights.ext
  ext p
  change (coneWeights (weightLinkIncl v) v (fun q=>q.property.2) (weightTime v w) _).weights p=w.weights p
  rw [coneWeights_apply]
  have he:weightMap (weightLinkIncl v)
      (weightRestrict {p | p≠v ∧ (p≤v ∨ v≤p)} (weightDelete v w ht) (weightDelete_link w ht hp))=
      weightDelete v w ht:=weightRestrict_map _ _ _
  rw [he,weightDelete_apply]
  change (1-w.weights v)*((1-w.weights v)⁻¹*(if p=v then 0 else w.weights p))+
    (if v=p then w.weights v else 0)=w.weights p
  by_cases he:p=v
  · subst p;simp
  · rw [ite_eq_right he,ite_eq_right (Ne.symm he),←mul_assoc,mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr ht)),one_mul,add_zero]

lemma weightParts_surjective (v:P) (c:OrderWeights (WeightLink v)) :
    Function.Surjective (Sum.elim (weightOldMap v) (weightConeMap v)) := by
  intro w
  by_cases hz:w.weights v=0
  · obtain ⟨z,rfl⟩:=weightOld_surjective_zero w hz
    exact ⟨.inl z,rfl⟩
  by_cases ho:w.weights v=1
  · exact ⟨.inr (1,c),(weightConeMap_one v c).trans (weight_eq_vertex_of_one w v ho).symm⟩
  have ht:w.weights v<1:=lt_of_le_of_ne (weight_le_one w v) ho
  have hp:0<w.weights v:=lt_of_le_of_ne (w.nonneg v) (Ne.symm hz)
  exact ⟨.inr (weightTime v w,weightRestrict _ (weightDelete v w ht) (weightDelete_link w ht hp)),
    weightDelete_reconstruct w ht hp⟩

end HarmonicArtin

end OAI
