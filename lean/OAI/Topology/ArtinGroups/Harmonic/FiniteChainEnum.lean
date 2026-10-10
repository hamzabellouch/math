import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightMap

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def finiteChainEnum (C:Finset P) (hC:IsChain (·≤·) (↑C:Set P)) (hne:C.Nonempty) :
    Fin (C.card-1+1) ≃o {p // p∈C} := by
  letI := IsChain.linearOrder hC.lt_of_le
  exact Fintype.orderIsoFinOfCardEq _ (by rw [Fintype.card_coe];have:=hne.card_pos;omega)

noncomputable def finiteChainOrder (C:Finset P) (hC:IsChain (·≤·) (↑C:Set P)) (hne:C.Nonempty) :
    Fin (C.card-1+1) →o P where
  toFun:=fun i=>(finiteChainEnum C hC hne i).val
  monotone':=fun _ _ h=>(finiteChainEnum C hC hne).monotone h

lemma finiteChainOrder_injective (C:Finset P) (hC:IsChain (·≤·) (↑C:Set P)) (hne:C.Nonempty) :
    Function.Injective (finiteChainOrder C hC hne) :=
  Subtype.val_injective.comp (finiteChainEnum C hC hne).injective

noncomputable def carrierSimplex (C:Finset P) (hC:IsChain (·≤·) (↑C:Set P)) (hne:C.Nonempty)
    (w:OrderWeights P) (hw:w.weights.support⊆C) : Convexity.StdSimplex ℝ (Fin (C.card-1+1)) :=
  ⟨Finsupp.equivFunOnFinite.symm (fun index=>w.weights (finiteChainOrder C hC hne index)),
    fun index=>w.nonneg _,by
    have he:=Equiv.sum_comp (finiteChainEnum C hC hne).toEquiv (fun p=>w.weights p.val)
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑i,w.weights (finiteChainOrder C hC hne i))=1
    rw [show (∑i,w.weights (finiteChainOrder C hC hne i))=∑p:C,w.weights p.val from he,
      Finset.sum_coe_sort]
    rw [← w.total]
    symm
    apply Finset.sum_subset hw
    intro p _ hp
    exact Finsupp.notMem_support_iff.mp hp⟩

lemma carrierSimplex_reconstruct (C:Finset P) (hC:IsChain (·≤·) (↑C:Set P)) (hne:C.Nonempty)
    (w:OrderWeights P) (hw:w.weights.support⊆C) :
    orderWeightsOfChain (finiteChainOrder C hC hne) (carrierSimplex C hC hne w hw)=w := by
  apply OrderWeights.ext
  ext p
  by_cases hp:p∈C
  · let i:=(finiteChainEnum C hC hne).symm ⟨p,hp⟩
    have hi:finiteChainOrder C hC hne i=p:=
      congrArg Subtype.val ((finiteChainEnum C hC hne).apply_symm_apply ⟨p,hp⟩)
    change chainWeights _ _ p=w.weights p
    rw [← hi,chainWeights_injective_apply _ (finiteChainOrder_injective _ _ _)]
    rfl
  · have hpw:p∉w.weights.support:=fun h=>hp (hw h)
    have hpz:p∉(chainWeights (finiteChainOrder C hC hne) (carrierSimplex C hC hne w hw)).support:=by
      intro ht
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (chainWeights_support _ _ ht)
      exact hp (hi ▸ (finiteChainEnum C hC hne i).property)
    exact (Finsupp.notMem_support_iff.mp hpz).trans (Finsupp.notMem_support_iff.mp hpw).symm

lemma continuous_of_finite_chain_carrier {Z:Type*} [TopologicalSpace Z]
    (f:Z→OrderWeights P) (C:Finset P) (hC:IsChain (·≤·) (↑C:Set P)) (hne:C.Nonempty)
    (hf:∀z,(f z).weights.support⊆C) (hc:∀p,Continuous (fun z=>(f z).weights p)) :
    Continuous f := by
  have hs:Continuous (fun z=>carrierSimplex C hC hne (f z) (hf z)):=by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (C.card-1+1))).continuous_iff]
    change Continuous (fun z index=>(f z).weights (finiteChainOrder C hC hne index))
    exact continuous_pi (fun i=>hc _)
  have he:(fun z=>orderWeightsOfChain (finiteChainOrder C hC hne) (carrierSimplex C hC hne (f z) (hf z)))=f:=by
    funext z
    exact carrierSimplex_reconstruct C hC hne (f z) (hf z)
  rw [←he]
  exact (chainWeightsChart_continuous _).comp hs

noncomputable instance finiteLinearWeightsCompact (R:Type*) [LinearOrder R] [Fintype R] :
    CompactSpace (OrderWeights R) := by
  classical
  by_cases h:Nonempty R
  · let := h
    let C:Finset R:=Finset.univ
    have hc:IsChain (·≤·) (↑C:Set R):=fun a _ b _ _=>le_total a b
    have hn:C.Nonempty:=Finset.univ_nonempty
    have hs:Function.Surjective (orderWeightsOfChain (finiteChainOrder C hc hn)):=by
      intro w
      exact ⟨carrierSimplex C hc hn w (Finset.subset_univ _),carrierSimplex_reconstruct C hc hn w _⟩
    exact isCompact_univ_iff.mp (by
      rw [←Set.range_eq_univ.mpr hs]
      exact isCompact_range (chainWeightsChart_continuous _))
  · have : IsEmpty R := not_nonempty_iff.mp h
    have : IsEmpty (OrderWeights R) := ⟨fun weights=>by
      obtain ⟨point,_⟩:=weights.support_nonempty
      exact isEmptyElim point⟩
    infer_instance

end HarmonicArtin

end OAI
