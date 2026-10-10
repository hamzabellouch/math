import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightInclusion

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v w z
variable {P:Type u} [PartialOrder P] {J:Type v} (A:J→Set P)
  {Z:Type w} [TopologicalSpace Z] [LocallyCompactSpace Z]
  {Y:Type z} [TopologicalSpace Y]

def WeightChainCover : Prop :=
  ∀(n:ℕ) (a:Fin (n+1)→oP),∃i:J,∀q,a q∈A i

lemma weightChainCover_rep (hA:WeightChainCover A) (w:OrderWeights P) :
    ∃i:J,∃z:OrderWeights (A i),weightMap (weightInclusion (A i)) z=w := by
  obtain ⟨i,hi⟩:=hA (weightDim w) (weightChain w)
  have hs:∀p∈w.weights.support,p∈A i:=by
    intro p hp
    let q:Fin (weightDim w+1):=(weightEnum w).symm ⟨p,hp⟩
    have he:weightChain w q=p:=congrArg Subtype.val ((weightEnum w).apply_symm_apply ⟨p,hp⟩)
    exact he ▸ hi q
  exact ⟨i,weightRestrict (A i) w hs,weightRestrict_map _ w hs⟩

noncomputable def weightGlueIndex (hA:WeightChainCover A) (w:OrderWeights P) : J :=
  (weightChainCover_rep A hA w).choose
noncomputable def weightGlueRep (hA:WeightChainCover A) (w:OrderWeights P) : OrderWeights (A (weightGlueIndex A hA w)) :=
  (weightChainCover_rep A hA w).choose_spec.choose
lemma weightGlueRep_map (hA:WeightChainCover A) (w:OrderWeights P) :
    weightMap (weightInclusion _) (weightGlueRep A hA w)=w :=
  (weightChainCover_rep A hA w).choose_spec.choose_spec

variable (F:∀i:J,C(Z×OrderWeights (A i),Y))

def WeightCompatible : Prop :=
  ∀(i j:J) (wi:OrderWeights (A i)) (wj:OrderWeights (A j)),
    weightMap (weightInclusion (A i)) wi=weightMap (weightInclusion (A j)) wj →
    ∀t:Z,F i (t,wi)=F j (t,wj)

noncomputable def weightGlueValue (hA:WeightChainCover A) (p:Z×OrderWeights P) : Y :=
  F (weightGlueIndex A hA p.2) (p.1,weightGlueRep A hA p.2)

omit [LocallyCompactSpace Z] in
lemma weightGlueValue_on (hA:WeightChainCover A) (hF:WeightCompatible A F)
    (i:J) (p:Z×OrderWeights (A i)) :
    weightGlueValue A F hA (p.1,weightMap (weightInclusion (A i)) p.2)=F i p := by
  exact hF _ _ _ _ (weightGlueRep_map A hA _) _

lemma weightGlueValue_continuous (hA:WeightChainCover A) (hF:WeightCompatible A F) :
    Continuous (weightGlueValue A F hA) := by
  apply orderWeights_prod_continuous
  intro n x
  obtain ⟨i,hi⟩:=hA n.len (nerveChain x)
  let a:Fin (n.len+1)→o A i:=⟨fun q=>⟨nerveChain x q,hi q⟩,fun _ _ h=>(nerveChain x).monotone h⟩
  have he (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) :
      weightMap (weightInclusion (A i)) (orderWeightsOfChain a z)=orderWeightsOfChain (nerveChain x) z := by
    rw [weightMap_chain]
    rfl
  have hc:Continuous (fun p:Z×Convexity.StdSimplex ℝ (Fin (n.len+1))=>F i (p.1,orderWeightsOfChain a p.2)):=
    (F i).continuous.comp (continuous_fst.prodMk ((chainWeightsChart_continuous a).comp continuous_snd))
  apply hc.congr
  intro p
  rw [←he]
  exact (weightGlueValue_on A F hA hF i (p.1,orderWeightsOfChain a p.2)).symm

noncomputable def weightGlue (hA:WeightChainCover A) (hF:WeightCompatible A F) : C(Z×OrderWeights P,Y) :=
  ⟨weightGlueValue A F hA,weightGlueValue_continuous A F hA hF⟩

end HarmonicArtin

end OAI
