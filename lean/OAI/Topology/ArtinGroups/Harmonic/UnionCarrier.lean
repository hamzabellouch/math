import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightHomeomorph
import OAI.Topology.ArtinGroups.Realizations.WeightMapCover

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P] {r:P→P→Prop} {c:P}
namespace WeightContractionPiece

instance : Std.Refl (@Extends P _ r c) :=⟨extends_refl⟩

variable (C:Set (WeightContractionPiece r c)) (hc:IsChain Extends C) (hne:C.Nonempty)

def unionCarrier : Set P :={x | ∃a∈C,x∈a.carrier}
lemma subset_union {a:WeightContractionPiece r c} (ha:a∈C) : a.carrier⊆unionCarrier C :=
  fun _ hx=>⟨a,ha,hx⟩

include hc hne in
lemma union_finset_cover (s:Finset P) (hs:∀x∈s,x∈unionCarrier C) :
    ∃a∈C,∀x∈s,x∈a.carrier := by
  induction s using Finset.induction_on with
  | empty => obtain ⟨a,ha⟩:=hne;exact ⟨a,ha,by simp⟩
  | @insert x s hx ih =>
    obtain ⟨a,ha,haC⟩:=ih (fun y hy=>hs y (Finset.mem_insert_of_mem hy))
    obtain ⟨b,hb,hxb⟩:=hs x (Finset.mem_insert_self x s)
    rcases hc.total ha hb with hab|hba
    · refine ⟨b,hb,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl|hy
      · exact hxb
      · exact hab.choose (haC y hy)
    · refine ⟨a,ha,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl|hy
      · exact hba.choose hxb
      · exact haC y hy

noncomputable def unionIncl (a:C) : a.val.carrier→o unionCarrier C :=
  weightSubset _ _ (subset_union C a.property)

lemma unionIncl_ambient (a:C) : (weightInclusion (unionCarrier C)).comp (unionIncl C a)=a.val.inclusion :=rfl

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

noncomputable def unionLocal (a:C) : C(I×OrderWeights a.val.carrier,OrderWeights (unionCarrier C)) :=
  (weightMapContinuous (unionIncl C a)).comp a.val.hom.toContinuousMap

include hc in
lemma union_compatible : WeightMapCompatible (unionIncl C) (unionLocal C) := by
  intro a b w z he t
  apply weightMap_injective (weightInclusion (unionCarrier C)) Subtype.val_injective
  change weightMap (weightInclusion _) (weightMap (unionIncl C a) (a.val.hom (t,w)))=
    weightMap (weightInclusion _) (weightMap (unionIncl C b) (b.val.hom (t,z)))
  simp only [weightMap_comp,unionIncl_ambient]
  have hW:weightMap a.val.inclusion w=weightMap b.val.inclusion z:=by
    have hh:=congrArg (weightMap (weightInclusion (unionCarrier C))) he
    simpa only [weightMap_comp,unionIncl_ambient] using hh
  rcases hc.total a.property b.property with hab|hba
  · exact extends_compare hab w z hW t
  · exact (extends_compare hba z w hW.symm t).symm

noncomputable def unionMap : C(I×OrderWeights (unionCarrier C),OrderWeights (unionCarrier C)) :=
  weightMapGlue (unionIncl C) (unionLocal C) (union_map_cover C hc hne) (union_compatible C hc)

lemma unionMap_on (a:C) (t:I) (w:OrderWeights a.val.carrier) :
    unionMap C hc hne (t,weightMap (unionIncl C a) w)=weightMap (unionIncl C a) (a.val.hom (t,w)) :=
  weightMapGlueValue_on (unionIncl C) (unionLocal C) (union_map_cover C hc hne) (union_compatible C hc) a (t,w)

noncomputable def union : WeightContractionPiece r c where
  carrier:=unionCarrier C
  root_mem:=by obtain ⟨a,ha⟩:=hne;exact ⟨a,ha,a.root_mem⟩
  down:=by
    intro x y hx h
    obtain ⟨a,ha,hx⟩:=hx
    exact ⟨a,ha,a.down hx h⟩
  hom:={
    toContinuousMap:=unionMap C hc hne
    map_zero_left:=by
      intro w
      obtain ⟨a,z,rfl⟩:=weightMapCover_rep (unionIncl C) (union_map_cover C hc hne) w
      change unionMap C hc hne (0,weightMap (unionIncl C a) z)=_
      rw [unionMap_on,a.val.hom.apply_zero]
      rfl
    map_one_left:=by
      intro w
      obtain ⟨a,z,rfl⟩:=weightMapCover_rep (unionIncl C) (union_map_cover C hc hne) w
      change unionMap C hc hne (1,weightMap (unionIncl C a) z)=_
      rw [unionMap_on,a.val.hom.apply_one]
      exact weightMap_vertex _ _ }

lemma extends_union {a:WeightContractionPiece r c} (ha:a∈C) : a.Extends (union C hc hne) := by
  refine ⟨subset_union C ha,?_⟩
  intro t w
  change weightMap a.inclusion (a.hom (t,w))=
    weightMap (weightInclusion (unionCarrier C)) (unionMap C hc hne (t,weightMap (unionIncl C ⟨a,ha⟩) w))
  rw [unionMap_on,weightMap_comp]
  rfl

end WeightContractionPiece
end HarmonicArtin

end OAI
