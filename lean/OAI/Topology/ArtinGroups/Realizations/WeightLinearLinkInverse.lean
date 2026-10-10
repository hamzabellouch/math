import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightOld

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v

lemma weightMap_cone {P Q R:Type*} [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    (f:Q→oP) (g:P→oR) (v:P) (hv:∀q,f q≤v ∨ v≤f q) (t:I) (w:OrderWeights Q) :
    weightMap g (coneWeights f v hv t w)=
      coneWeights (g.comp f) (g v) (fun q=>(hv q).imp (fun h=>g.monotone h) (fun h=>g.monotone h)) t w := by
  apply OrderWeights.ext
  change Finsupp.mapDomain g ((σ t).val • (weightMap f w).weights+Finsupp.single v t.val)=_
  rw [Finsupp.mapDomain_add,Finsupp.mapDomain_smul,Finsupp.mapDomain_single]
  congr 1
  exact congrArg (fun z:OrderWeights R=>(σ t).val • z.weights) (weightMap_comp f g w)

lemma weight_support_singleton {P:Type*} [PartialOrder P] (w:OrderWeights P) (v:P)
    (hs:w.weights.support⊆{v}) : w=weightVertex v := by
  have he:=Finsupp.support_subset_singleton.mp hs
  have ht:=w.total
  rw [he,Finsupp.sum_single_index (by rfl)] at ht
  apply weight_eq_vertex_of_one w v ht

noncomputable def weightLinearLinkInverse {P:Type*} [LinearOrder P] (v:P) : WeightOld v→o WeightLink v :=
  ⟨fun p=>⟨p.val,p.property,le_total p.val v⟩,fun _ _ h=>h⟩

lemma weightLinearLinkMap_surjective {P:Type*} [LinearOrder P] (v:P) :
    Function.Surjective (weightLinkMap v) := by
  intro w
  refine ⟨weightMap (weightLinearLinkInverse v) w,?_⟩
  change weightMap (weightLinkOld v) (weightMap (weightLinearLinkInverse v) w)=w
  rw [weightMap_comp]
  exact weightMap_id w

lemma weightLinearCone_surjective {P:Type*} [LinearOrder P] (v:P) (c:OrderWeights (WeightLink v)) :
    Function.Surjective (weightConeMap v) := by
  intro w
  obtain ⟨z,hz⟩:=weightParts_surjective v c w
  rcases z with z|z
  · obtain ⟨l,hl⟩:=weightLinearLinkMap_surjective v z
    refine ⟨(0,l),?_⟩
    rw [weightConeMap_zero,hl]
    exact hz
  · exact ⟨z,hz⟩

lemma weightLinearCone_quotient {P:Type*} [LinearOrder P] [Fintype P]
    (v:P) (c:OrderWeights (WeightLink v)) : Topology.IsQuotientMap (weightConeMap v) :=
  Topology.IsQuotientMap.of_surjective_continuous (weightLinearCone_surjective v c) (weightConeMap v).continuous

noncomputable def weightLinkEmbedding {P Q:Type*} [PartialOrder P] [PartialOrder Q]
    (j:Q↪oP) (v:Q) : WeightLink v→o WeightLink (j v) where
  toFun p:=⟨j p.val,fun h=>p.property.1 (j.injective h),
    p.property.2.imp (fun h=>j.monotone h) (fun h=>j.monotone h)⟩
  monotone':=fun _ _ h=>j.monotone h

lemma weightCone_embedding {P Q:Type*} [PartialOrder P] [PartialOrder Q]
    (j:Q↪oP) (v:Q) (p:I×OrderWeights (WeightLink v)) :
    weightMap ⟨j,j.monotone⟩ (weightConeMap v p)=
      weightConeMap (j v) (p.1,weightMap (weightLinkEmbedding j v) p.2) := by
  let jo:Q→oP:=⟨j,j.monotone⟩
  change weightMap jo (coneWeights (weightLinkIncl v) v (fun q=>q.property.2) p.1 p.2)=
    coneWeights (weightLinkIncl (j v)) (j v) (fun q=>q.property.2) p.1 (weightMap (weightLinkEmbedding j v) p.2)
  rw [weightMap_cone]
  apply OrderWeights.ext
  change (σ p.1).val • (weightMap (jo.comp (weightLinkIncl v)) p.2).weights+_= _
  have he:weightMap (jo.comp (weightLinkIncl v)) p.2=
      weightMap (weightLinkIncl (j v)) (weightMap (weightLinkEmbedding j v) p.2):=
    (weightMap_comp (weightLinkEmbedding j v) (weightLinkIncl (j v)) p.2).symm
  rw [he]
  rfl

lemma continuous_comp_weightEmbedding {P Q Y:Type*} [PartialOrder P] [LinearOrder Q]
    [Fintype Q] [TopologicalSpace Y] (j:Q↪oP) (v:Q) (c:OrderWeights (WeightLink v))
    (f:OrderWeights P→Y) (hCone:Continuous (f ∘ weightConeMap (j v))) :
    Continuous (f ∘ weightMap ⟨j,j.monotone⟩) := by
  apply (weightLinearCone_quotient v c).continuous_iff.mpr
  have hp:Continuous (fun p:I×OrderWeights (WeightLink v)=>
      (p.1,weightMap (weightLinkEmbedding j v) p.2)):=
    continuous_fst.prodMk ((weightMap_continuous (weightLinkEmbedding j v)).comp continuous_snd)
  exact (hCone.comp hp).congr (fun p=>congrArg f (weightCone_embedding j v p).symm)

theorem continuous_of_weightParts {P:Type u} [PartialOrder P] {Y:Type v} [TopologicalSpace Y]
    (v:P) (f:OrderWeights P→Y)
    (hOld:Continuous (f ∘ weightOldMap v))
    (hCone:Continuous (f ∘ weightConeMap v)) : Continuous f := by
  rw [orderWeights_continuous_iff]
  intro n x
  let a:Fin (n.len+1)→o P:=nerveChain x
  let C:Finset P:=Finset.univ.image a
  have hC:IsChain (·<·) (↑C:Set P):=by
    intro p hp q hq hne
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hp
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hq
    exact (le_total i j).imp (fun hle=>lt_of_le_of_ne (a.monotone hle) hne)
      (fun hle=>lt_of_le_of_ne (a.monotone hle) hne.symm)
  have ha (i:Fin (n.len+1)):a i∈C:=Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  by_cases hv:v∈C
  · by_cases hn:(C.erase v).Nonempty
    · let _ := IsChain.linearOrder hC
      let rv:C:=⟨v,hv⟩
      let j:C→oP:=⟨Subtype.val,fun _ _ h=>h⟩
      let aC:Fin (n.len+1)→o C:=⟨fun i=>⟨a i,ha i⟩,fun _ _ h=>a.monotone h⟩
      obtain ⟨b,hb⟩:=hn
      let c:WeightLink rv:=⟨⟨b,(Finset.mem_erase.mp hb).2⟩,
        (by intro h;exact (Finset.mem_erase.mp hb).1 (congrArg Subtype.val h)),le_total _ _⟩
      let je:C↪oP:=OrderEmbedding.subtype (·∈C)
      have hf:Continuous (f ∘ weightMap j):=
        continuous_comp_weightEmbedding je rv (weightVertex c) f hCone
      have hh:=hf.comp (chainWeightsChart_continuous aC)
      change Continuous (fun z=>f (weightMap j (orderWeightsOfChain aC z))) at hh
      simp_rw [weightMap_chain] at hh
      have hj:j.comp aC=nerveChain x:=by ext i;rfl
      rw [hj] at hh
      exact hh
    · have hs:C⊆{v}:=by
        intro p hp
        by_contra hh
        have hpv:p≠v:=by simpa only [Finset.mem_singleton] using hh
        exact hn ⟨p,Finset.mem_erase.mpr ⟨hpv,hp⟩⟩
      have he (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) : orderWeightsOfChain a z=weightVertex v:=
        weight_support_singleton _ _ ((chainWeights_support a z).trans hs)
      simp_rw [show nerveChain x=a from rfl,he]
      exact continuous_const
  · let aO:Fin (n.len+1)→o WeightOld v:=
      ⟨fun i=>⟨a i,(by intro h;exact hv (h ▸ ha i))⟩,fun _ _ h=>a.monotone h⟩
    have hh:=hOld.comp (chainWeightsChart_continuous aO)
    change Continuous (fun z=>f (weightMap (weightOldIncl v) (orderWeightsOfChain aO z))) at hh
    simp_rw [weightMap_chain] at hh
    have hj:(weightOldIncl v).comp aO=nerveChain x:=by ext i;rfl
    rw [hj] at hh
    exact hh

end HarmonicArtin

end OAI
