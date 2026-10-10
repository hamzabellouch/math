import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightCarrier
import OAI.Topology.ArtinGroups.Harmonic.FiniteChainEnum

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {P:Type u} {Q:Type v} [PartialOrder P] [PartialOrder Q]

lemma orderWeights_prod_continuous {Z Y:Type*} [TopologicalSpace Z] [LocallyCompactSpace Z]
    [TopologicalSpace Y] (f:Z×OrderWeights P→Y)
    (hc:∀(n:SimplexCategory) (x:(nerve P).obj (op n)),
      Continuous (fun p:Z×Convexity.StdSimplex ℝ (Fin (n.len+1))=>f (p.1,orderWeightsOfChain (nerveChain x) p.2))) :
    Continuous f := by
  have ht (w:OrderWeights P):Continuous (fun t=>f (t,w)):=by
    have h:Continuous (fun t=>f (t,orderWeightsOfChain (weightChain w) (weightSimplex w))):=
      (hc ⦋weightDim w⦌ (nerveOfChain (weightChain w))).comp (continuous_id.prodMk continuous_const)
    simpa only [orderWeightsOfChain_canonical] using h
  let F:OrderWeights P→C(Z,Y):=fun w=>⟨fun t=>f (t,w),ht w⟩
  have hF:Continuous F:=by
    rw [orderWeights_continuous_iff]
    intro n x
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (hc n x).comp continuous_swap
  exact (ContinuousMap.continuous_uncurry_of_continuous ⟨F,hF⟩).comp continuous_swap

noncomputable def coneWeights (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q)
    (t:I) (w:OrderWeights Q) : OrderWeights P where
  weights:=(σ t).val • (weightMap f w).weights + Finsupp.single v t.val
  nonneg p:=by
    change 0≤ (σ t).val * (weightMap f w).weights p + (Finsupp.single v t.val) p
    apply add_nonneg (mul_nonneg (σ t).property.1 ((weightMap f w).nonneg p))
    simp only [Finsupp.single_apply]
    split_ifs; exacts [t.property.1,le_rfl]
  total:=by
    rw [Finsupp.sum_add_index (by intros;rfl) (by intros;rfl),
      Finsupp.sum_single_index (by rfl),Finsupp.sum_smul_index (by intros;rfl)]
    change (∑p∈(weightMap f w).weights.support,(σ t).val * (weightMap f w).weights p)+t.val=1
    rw [←Finset.mul_sum]
    change (σ t).val * ((weightMap f w).weights.sum (fun _ a=>a))+t.val=1
    rw [(weightMap f w).total]
    change (1-t.val)*1+t.val=1
    ring
  chain:=by
    intro a ha b hb
    have hl {p:P} (h:p∈((σ t).val • (weightMap f w).weights + Finsupp.single v t.val).support) :
        p∈(weightMap f w).weights.support ∨ p=v:=by
      rcases Finset.mem_union.mp (Finsupp.support_add h) with h|h
      · exact Or.inl (Finsupp.support_smul h)
      · exact Or.inr (Finset.mem_singleton.mp (Finsupp.support_single_subset h))
    rcases hl ha with hpa|hpa
    · rcases hl hb with hpb|hpb
      · exact (weightMap f w).chain _ hpa _ hpb
      · subst b
        obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp (Finsupp.mapDomain_support hpa)
        exact hv q
    · subst a
      rcases hl hb with hpb|hpb
      · obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp (Finsupp.mapDomain_support hpb)
        exact (hv q).symm
      · subst b
        exact Or.inl le_rfl

lemma coneWeights_apply (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q)
    (t:I) (w:OrderWeights Q) (p:P) :
    (coneWeights f v hv t w).weights p=(1-t.val)*(weightMap f w).weights p+if v=p then t.val else 0 := by
  simp [coneWeights,Finsupp.single_apply,unitInterval.symm]

lemma coneWeights_zero (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q) (w:OrderWeights Q) :
    coneWeights f v hv 0 w=weightMap f w := by
  apply OrderWeights.ext
  change (σ (0:I)).val • (weightMap f w).weights+Finsupp.single v (0:ℝ)=_
  simp

lemma coneWeights_one (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q) (w w':OrderWeights Q) :
    coneWeights f v hv 1 w=coneWeights f v hv 1 w' := by
  apply OrderWeights.ext
  change (σ (1:I)).val • (weightMap f w).weights+Finsupp.single v (1:ℝ)=_
  simp [coneWeights]

lemma coneWeights_support (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q) (t:I) (w:OrderWeights Q) :
    (coneWeights f v hv t w).weights.support⊆insert v (w.weights.support.image f) := by
  intro p hp
  rcases Finset.mem_union.mp (Finsupp.support_add hp) with h|h
  · exact Finset.mem_insert_of_mem (Finsupp.mapDomain_support (Finsupp.support_smul h))
  · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h)))

lemma coneWeights_continuous (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q) :
    Continuous (fun p:I×OrderWeights Q=>coneWeights f v hv p.1 p.2) := by
  apply orderWeights_prod_continuous
  intro n x
  let C:Finset P:=insert v (Finset.univ.image (f.comp (nerveChain x)))
  have hC:IsChain (·≤·) (↑C:Set P):=by
    intro a ha b hb _
    change a∈insert v (Finset.univ.image (f.comp (nerveChain x))) at ha
    change b∈insert v (Finset.univ.image (f.comp (nerveChain x))) at hb
    rcases Finset.mem_insert.mp ha with hpa|hpa
    · subst a
      rcases Finset.mem_insert.mp hb with hpb|hpb
      · subst b;exact Or.inl le_rfl
      · obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hpb
        exact (hv (nerveChain x j)).symm
    · rcases Finset.mem_insert.mp hb with hpb|hpb
      · subst b
        obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hpa
        exact hv (nerveChain x i)
      · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hpa
        obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hpb
        exact (le_total i j).imp (fun h=>(f.comp (nerveChain x)).monotone h) (fun h=>(f.comp (nerveChain x)).monotone h)

  apply continuous_of_finite_chain_carrier _ C hC (Finset.insert_nonempty _ _)
  · intro p a ha
    have hs:=coneWeights_support f v hv p.1 (orderWeightsOfChain (nerveChain x) p.2) ha
    rcases Finset.mem_insert.mp hs with rfl|hs
    · exact Finset.mem_insert_self _ _
    · obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hs
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp (chainWeights_support _ _ hq)
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  · intro q
    simp_rw [coneWeights_apply,weightMap_chain]
    apply Continuous.add
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        ((weightEval_continuous q).comp ((chainWeightsChart_continuous _).comp continuous_snd))
    · split_ifs
      · exact continuous_subtype_val.comp continuous_fst
      · exact continuous_const

noncomputable def coneWeightsContinuous (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q) :
    C(I×OrderWeights Q,OrderWeights P) :=⟨_,coneWeights_continuous f v hv⟩

end HarmonicArtin

end OAI
