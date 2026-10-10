import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightHomeomorph
import OAI.Topology.ArtinGroups.Realizations.WeightMapCover

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P] (r:P→P→Prop) (A:Set P)

structure WeightRetractionPiece where
  carrier:Set P
  base:A⊆carrier
  down:∀{x y},x∈carrier → r y x → y∈carrier
  map:C(OrderWeights carrier,OrderWeights A)
  retract:∀w:OrderWeights A,map (weightMap (weightSubset A carrier base) w)=w

namespace WeightRetractionPiece
variable {r A}

def Extends (a b:WeightRetractionPiece r A) : Prop :=
  ∃h:a.carrier⊆b.carrier,∀w:OrderWeights a.carrier,
    b.map (weightMap (weightSubset _ _ h) w)=a.map w

lemma extends_refl (a:WeightRetractionPiece r A) : a.Extends a := by
  refine ⟨Set.Subset.rfl,?_⟩
  intro w
  rw [weightSubset_self,weightMap_id]

lemma extends_trans {a b c:WeightRetractionPiece r A} (h:a.Extends b) (k:b.Extends c) : a.Extends c := by
  obtain ⟨h,hh⟩:=h
  obtain ⟨k,hk⟩:=k
  refine ⟨h.trans k,?_⟩
  intro w
  rw [← weightSubset_comp _ _ _ h k,← weightMap_comp,hk,hh]

instance : Std.Refl (@Extends P _ r A):=⟨extends_refl⟩

lemma extends_compare {a b:WeightRetractionPiece r A} (h:a.Extends b)
    (w:OrderWeights a.carrier) (z:OrderWeights b.carrier)
    (he:weightMap (weightInclusion a.carrier) w=weightMap (weightInclusion b.carrier) z) :
    a.map w=b.map z := by
  obtain ⟨h,hh⟩:=h
  have hz:weightMap (weightSubset _ _ h) w=z:=by
    apply weightMap_injective (weightInclusion b.carrier) Subtype.val_injective
    rw [weightMap_comp]
    exact he
  rw [←hh,hz]

variable (C:Set (WeightRetractionPiece r A)) (hc:IsChain Extends C) (hne:C.Nonempty)

def unionCarrier : Set P :={x | ∃a∈C,x∈a.carrier}
lemma subset_union {a:WeightRetractionPiece r A} (ha:a∈C) : a.carrier⊆unionCarrier C :=
  fun _ hx=>⟨a,ha,hx⟩

include hc hne in
lemma union_finset_cover (s:Finset P) (hs:∀x∈s,x∈unionCarrier C) :
    ∃a∈C,∀x∈s,x∈a.carrier := by
  induction s using Finset.induction_on with
  | empty=>obtain ⟨a,ha⟩:=hne;exact ⟨a,ha,by simp⟩
  | @insert x s hx ih=>
    obtain ⟨a,ha,hac⟩:=ih (fun y hy=>hs y (Finset.mem_insert_of_mem hy))
    obtain ⟨b,hb,hxb⟩:=hs x (Finset.mem_insert_self x s)
    rcases hc.total ha hb with hab|hba
    · refine ⟨b,hb,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl|hy
      · exact hxb
      · exact hab.choose (hac y hy)
    · refine ⟨a,ha,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl|hy
      · exact hba.choose hxb
      · exact hac y hy

noncomputable def unionIncl (a:C) : a.val.carrier→o unionCarrier C :=
  weightSubset _ _ (subset_union C a.property)

include hc hne in
lemma union_map_cover : WeightMapCover (unionIncl C) := by
  intro n a
  obtain ⟨b,hb,hcover⟩:=union_finset_cover C hc hne
    (Finset.univ.image (fun i=> (a i).val)) (by
      intro x hx
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
      exact (a i).property)
  let d:Fin (n+1)→o b.carrier:=⟨fun i=>⟨(a i).val,hcover _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩,
    fun _ _ h=>a.monotone h⟩
  exact ⟨⟨b,hb⟩,d,by ext i;rfl⟩

noncomputable def unionLocal (a:C) : C(Unit×OrderWeights a.val.carrier,OrderWeights A) :=
  a.val.map.comp ContinuousMap.snd

include hc in
lemma union_compatible : WeightMapCompatible (unionIncl C) (unionLocal C) := by
  intro a b w z he t
  have hW:weightMap (weightInclusion a.val.carrier) w=weightMap (weightInclusion b.val.carrier) z:=by
    have hh:=congrArg (weightMap (weightInclusion (unionCarrier C))) he
    rw [weightMap_comp,weightMap_comp] at hh
    exact hh
  rcases hc.total a.property b.property with hab|hba
  · exact extends_compare hab w z hW
  · exact (extends_compare hba z w hW.symm).symm

noncomputable def unionMap : C(OrderWeights (unionCarrier C),OrderWeights A) :=
  (weightMapGlue (unionIncl C) (unionLocal C) (union_map_cover C hc hne) (union_compatible C hc)).comp
    ⟨fun w=>((),w),continuous_const.prodMk continuous_id⟩

lemma unionMap_on (a:C) (w:OrderWeights a.val.carrier) :
    unionMap C hc hne (weightMap (unionIncl C a) w)=a.val.map w :=
  weightMapGlueValue_on (unionIncl C) (unionLocal C) (union_map_cover C hc hne) (union_compatible C hc) a ((),w)

noncomputable def union : WeightRetractionPiece r A where
  carrier:=unionCarrier C
  base:=by
    obtain ⟨a,ha⟩:=hne
    exact fun x hx=>⟨a,ha,a.base hx⟩
  down:=by
    intro x y hx h
    obtain ⟨a,ha,hx⟩:=hx
    exact ⟨a,ha,a.down hx h⟩
  map:=unionMap C hc hne
  retract:=by
    intro w
    obtain ⟨a,ha⟩:=hne
    have he:weightSubset A (unionCarrier C) (fun x hx=>⟨a,ha,a.base hx⟩)=
        (unionIncl C ⟨a,ha⟩).comp (weightSubset A a.carrier a.base):=rfl
    rw [he,← weightMap_comp]
    exact (unionMap_on C hc (show C.Nonempty from ⟨a,ha⟩) ⟨a,ha⟩ _).trans (a.retract w)

lemma extends_union {a:WeightRetractionPiece r A} (ha:a∈C) : a.Extends (union C hc hne) :=
  ⟨subset_union C ha,fun w=>unionMap_on C hc hne ⟨a,ha⟩ w⟩

end WeightRetractionPiece
end HarmonicArtin

end OAI
