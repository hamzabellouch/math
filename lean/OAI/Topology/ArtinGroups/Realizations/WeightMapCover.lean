import Mathlib
import OAI.Topology.ArtinGroups.Realizations.ConeWeights

namespace OAI

namespace HarmonicArtin
open scoped unitInterval
open Simplicial

universe u v w z
variable {P:Type u} [PartialOrder P] {J:Type v} {Q:J→Type u} [∀j,PartialOrder (Q j)]
  (f:∀j,Q j→oP) {Z:Type w} [TopologicalSpace Z] [LocallyCompactSpace Z]
  {Y:Type z} [TopologicalSpace Y]

def WeightMapCover : Prop :=
  ∀(n:ℕ) (a:Fin (n+1)→oP),∃i:J,∃b:Fin (n+1)→o Q i,(f i).comp b=a

lemma weightMapCover_rep (hf:WeightMapCover f) (w:OrderWeights P) :
    ∃i:J,∃z:OrderWeights (Q i),weightMap (f i) z=w := by
  obtain ⟨i,b,hb⟩:=hf (weightDim w) (weightChain w)
  refine ⟨i,orderWeightsOfChain b (weightSimplex w),?_⟩
  rw [weightMap_chain,hb]
  exact orderWeightsOfChain_canonical w

noncomputable def weightMapGlueIndex (hf:WeightMapCover f) (w:OrderWeights P) : J :=
  (weightMapCover_rep f hf w).choose
noncomputable def weightMapGlueRep (hf:WeightMapCover f) (w:OrderWeights P) : OrderWeights (Q (weightMapGlueIndex f hf w)) :=
  (weightMapCover_rep f hf w).choose_spec.choose
lemma weightMapGlueRep_map (hf:WeightMapCover f) (w:OrderWeights P) :
    weightMap (f _) (weightMapGlueRep f hf w)=w :=
  (weightMapCover_rep f hf w).choose_spec.choose_spec

variable (F:∀i:J,C(Z×OrderWeights (Q i),Y))

def WeightMapCompatible : Prop :=
  ∀(i j:J) (wi:OrderWeights (Q i)) (wj:OrderWeights (Q j)),
    weightMap (f i) wi=weightMap (f j) wj → ∀t:Z,F i (t,wi)=F j (t,wj)

noncomputable def weightMapGlueValue (hf:WeightMapCover f) (p:Z×OrderWeights P) : Y :=
  F (weightMapGlueIndex f hf p.2) (p.1,weightMapGlueRep f hf p.2)

omit [LocallyCompactSpace Z] in
lemma weightMapGlueValue_on (hf:WeightMapCover f) (hF:WeightMapCompatible f F)
    (i:J) (p:Z×OrderWeights (Q i)) :
    weightMapGlueValue f F hf (p.1,weightMap (f i) p.2)=F i p := by
  exact hF _ _ _ _ (weightMapGlueRep_map f hf _) _

lemma weightMapGlueValue_continuous (hf:WeightMapCover f) (hF:WeightMapCompatible f F) :
    Continuous (weightMapGlueValue f F hf) := by
  apply orderWeights_prod_continuous
  intro n x
  obtain ⟨i,b,hb⟩:=hf n.len (nerveChain x)
  have he (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) :
      weightMap (f i) (orderWeightsOfChain b z)=orderWeightsOfChain (nerveChain x) z := by
    rw [weightMap_chain,hb]
  have hc:Continuous (fun p:Z×Convexity.StdSimplex ℝ (Fin (n.len+1))=>F i (p.1,orderWeightsOfChain b p.2)):=
    (F i).continuous.comp (continuous_fst.prodMk ((chainWeightsChart_continuous b).comp continuous_snd))
  apply hc.congr
  intro p
  rw [←he]
  exact (weightMapGlueValue_on f F hf hF i (p.1,orderWeightsOfChain b p.2)).symm

noncomputable def weightMapGlue (hf:WeightMapCover f) (hF:WeightMapCompatible f F) : C(Z×OrderWeights P,Y) :=
  ⟨weightMapGlueValue f F hf,weightMapGlueValue_continuous f F hf hF⟩

end HarmonicArtin

end OAI
