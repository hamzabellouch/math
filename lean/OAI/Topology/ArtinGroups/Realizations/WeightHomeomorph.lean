import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightInclusion

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

universe u v
variable {P:Type u} {Q:Type v} [PartialOrder P] [PartialOrder Q]

noncomputable def weightHomeomorph (e:P≃oQ) : OrderWeights P≃ₜOrderWeights Q where
  toFun:=weightMap (e : P→oQ)
  invFun:=weightMap (e.symm : Q→oP)
  left_inv w:=by
    rw [weightMap_comp]
    have he:(e.symm : Q→oP).comp (e : P→oQ)=OrderHom.id:=by ext p;exact e.symm_apply_apply p
    rw [he,weightMap_id]
  right_inv w:=by
    rw [weightMap_comp]
    have he:(e : P→oQ).comp (e.symm : Q→oP)=OrderHom.id:=by ext p;exact e.apply_symm_apply p
    rw [he,weightMap_id]
  continuous_toFun:=weightMap_continuous _
  continuous_invFun:=weightMap_continuous _

lemma weightMap_vertex (f:P→oQ) (p:P) : weightMap f (weightVertex p)=weightVertex (f p) := by
  apply OrderWeights.ext
  exact Finsupp.mapDomain_single

noncomputable def weightSubset (A B:Set P) (h:A⊆B) : A→oB :=
  ⟨fun p=>⟨p.val,h p.property⟩,fun _ _ he=>he⟩

lemma weightSubset_comp (A B C:Set P) (h:A⊆B) (k:B⊆C) :
    (weightSubset B C k).comp (weightSubset A B h)=weightSubset A C (h.trans k) :=rfl
lemma weightSubset_incl (A B:Set P) (h:A⊆B) :
    (weightInclusion B).comp (weightSubset A B h)=weightInclusion A :=rfl

lemma weightSubset_self (A:Set P) (h:A⊆A) : weightSubset A A h=OrderHom.id :=by ext p;rfl

noncomputable def transportContraction {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e:X≃ₜY) (c:X) (H:ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X c)) :
    ContinuousMap.Homotopy (ContinuousMap.id Y) (ContinuousMap.const Y (e c)) where
  toFun p:=e (H (p.1,e.symm p.2))
  continuous_toFun:=e.continuous.comp (H.continuous.comp
    (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
  map_zero_left x:=by rw [H.apply_zero];exact e.apply_symm_apply x
  map_one_left x:=by rw [H.apply_one];rfl

variable (r:P→P→Prop) (c:P)

structure WeightContractionPiece where
  carrier:Set P
  root_mem:c∈carrier
  down:∀{x y},x∈carrier → r y x → y∈carrier
  hom:ContinuousMap.Homotopy (ContinuousMap.id (OrderWeights carrier))
    (ContinuousMap.const _ (weightVertex ⟨c,root_mem⟩))

namespace WeightContractionPiece
variable {r c}
noncomputable def inclusion (a:WeightContractionPiece r c) :=weightInclusion a.carrier

def Extends (a b:WeightContractionPiece r c) : Prop :=
  ∃h:a.carrier⊆b.carrier,∀t:I,∀w:OrderWeights a.carrier,
    weightMap a.inclusion (a.hom (t,w))=
      weightMap b.inclusion (b.hom (t,weightMap (weightSubset _ _ h) w))

lemma extends_refl (a:WeightContractionPiece r c) : a.Extends a := by
  refine ⟨Set.Subset.rfl,?_⟩
  intro t w
  rw [weightSubset_self,weightMap_id]

lemma extends_trans {a b d:WeightContractionPiece r c} (h:a.Extends b) (k:b.Extends d) : a.Extends d := by
  obtain ⟨h,hh⟩:=h
  obtain ⟨k,hk⟩:=k
  refine ⟨h.trans k,?_⟩
  intro t w
  rw [hh,hk,weightMap_comp]
  rfl

lemma extends_compare {a b:WeightContractionPiece r c} (h:a.Extends b)
    (w:OrderWeights a.carrier) (z:OrderWeights b.carrier)
    (he:weightMap a.inclusion w=weightMap b.inclusion z) (t:I) :
    weightMap a.inclusion (a.hom (t,w))=weightMap b.inclusion (b.hom (t,z)) := by
  obtain ⟨h,hh⟩:=h
  rw [hh]
  have hz:weightMap (weightSubset _ _ h) w=z:=by
    apply weightMap_injective b.inclusion Subtype.val_injective
    rw [weightMap_comp]
    exact he
  rw [hz]

end WeightContractionPiece
end HarmonicArtin

end OAI
