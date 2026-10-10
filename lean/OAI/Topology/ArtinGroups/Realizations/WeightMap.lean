import Mathlib
import OAI.Topology.ArtinGroups.Realizations.NerveChain

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {P:Type u} {Q:Type v} [PartialOrder P] [PartialOrder Q]

noncomputable def weightMap (f:P→oQ) (w:OrderWeights P) : OrderWeights Q where
  weights:=w.weights.mapDomain f
  nonneg q:=by
    unfold Finsupp.mapDomain
    rw [Finsupp.sum_apply]
    exact Finset.sum_nonneg (fun p _=>by
      simp only [Finsupp.single_apply]
      split_ifs; exacts [w.nonneg p,le_rfl])
  total:=by
    rw [Finsupp.sum_mapDomain_index (by intros;rfl) (by intros;rfl)]
    exact w.total
  chain:=by
    intro p hp q hq
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp (Finsupp.mapDomain_support hp)
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp (Finsupp.mapDomain_support hq)
    exact (w.chain a ha b hb).imp (fun h=>f.monotone h) (fun h=>f.monotone h)

lemma weightMap_chain {n:ℕ} (f:P→oQ) (x:Fin (n+1)→o P)
    (z:Convexity.StdSimplex ℝ (Fin (n+1))) :
    weightMap f (orderWeightsOfChain x z)=orderWeightsOfChain (f.comp x) z := by
  apply OrderWeights.ext
  change Finsupp.mapDomain f (chainWeights x z)=chainWeights (f.comp x) z
  simp only [chainWeights,Finsupp.mapDomain_finsetSum,Finsupp.mapDomain_single]
  rfl

lemma chainWeightsChart_continuous {n:ℕ} (x:Fin (n+1)→oP) :
    Continuous (orderWeightsOfChain x) :=
  orderWeightsChart_continuous (nerveOfChain x)

lemma weightMap_continuous (f:P→o Q) : Continuous (weightMap f) := by
  rw [orderWeights_continuous_iff]
  intro n x
  simp_rw [weightMap_chain]
  exact chainWeightsChart_continuous _

noncomputable def weightMapContinuous (f:P→oQ) : C(OrderWeights P,OrderWeights Q) :=
  ⟨weightMap f,weightMap_continuous f⟩

lemma weightMap_id (w:OrderWeights P) : weightMap OrderHom.id w=w := by
  apply OrderWeights.ext
  exact Finsupp.mapDomain_id

lemma weightMap_comp {R:Type*} [PartialOrder R] (f:P→oQ) (g:Q→oR) (w:OrderWeights P) :
    weightMap g (weightMap f w)=weightMap (g.comp f) w := by
  apply OrderWeights.ext
  exact Finsupp.mapDomain_comp.symm

lemma weightMap_injective (f:P→oQ) (hf:Function.Injective f) : Function.Injective (weightMap f) := by
  intro x y h
  apply OrderWeights.ext
  have he:=congrArg OrderWeights.weights h
  change x.weights.mapDomain f=y.weights.mapDomain f at he
  exact Finsupp.mapDomain_injective hf he

lemma weightMap_apply_embedding (f:P→oQ) (hf:Function.Injective f) (w:OrderWeights P) (p:P) :
    (weightMap f w).weights (f p)=w.weights p := by
  change (w.weights.mapDomain f) (f p)=_
  exact Finsupp.mapDomain_apply_of_injective hf _ _

lemma weightMap_support_embedding (f:P→oQ) (hf:Function.Injective f) (w:OrderWeights P) :
    (weightMap f w).weights.support=w.weights.support.image f :=
  Finsupp.mapDomain_support_of_injective hf w.weights

end HarmonicArtin

end OAI
