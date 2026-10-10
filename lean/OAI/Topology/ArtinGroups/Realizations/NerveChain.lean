import Mathlib
import OAI.Topology.ArtinGroups.Realizations.RealizeSimplex
import OAI.Topology.ArtinGroups.Realizations.WeightDim
import OAI.Topology.ArtinGroups.Harmonic.SimplexSupport

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite Convexity

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def nerveOfChain {n:ℕ} (x:Fin (n+1) →o P) : (nerve P).obj (op ⦋n⦌) := x.toFunctor

noncomputable def nerveWeightsSimplex {n:SimplexCategory} (x:(nerve P).obj (op n)) :
    C(StdSimplex ℝ (Fin (n.len+1)),OrderWeights P) :=
  ⟨fun z=>orderWeightsOfChain (nerveChain x) z,orderWeightsChart_continuous x⟩

noncomputable def nerveWeightsMap : nerve P⟶TopCat.toSSet.obj (TopCat.of (OrderWeights P)) where
  app n:=↾fun x=>(TopCat.toSSetObjEquiv _ n).symm (nerveWeightsSimplex x)
  naturality {n m} a:=by
    apply ConcreteCategory.hom_ext
    intro x
    apply (TopCat.toSSetObjEquiv _ m).injective
    ext z : 1
    apply OrderWeights.ext
    exact chainWeights_natural (nerveChain x) a.unop.toOrderHom z

noncomputable def nerveToWeights : C(|nerve P|,OrderWeights P) :=
  ((sSetTopAdj.homEquiv _ _).symm nerveWeightsMap).hom

lemma nerveToWeights_simplex {n:SimplexCategory} (x:(nerve P).obj (op n))
    (z:StdSimplex ℝ (Fin (n.len+1))) :
    nerveToWeights (realizeSimplex (nerve P) x z)=orderWeightsOfChain (nerveChain x) z := by
  have he:(sSetTopAdj.homEquiv _ _) (TopCat.ofHom (nerveToWeights (P:=P)))=nerveWeightsMap:=
    (sSetTopAdj.homEquiv _ _).apply_symm_apply _
  rw [Adjunction.homEquiv_unit] at he
  have hh:=ConcreteCategory.congr_hom (congrArg (fun f:nerve P ⟶ TopCat.toSSet.obj (TopCat.of (OrderWeights P))=>f.app (op n)) he) x
  have ht:=congrArg (fun f=>(TopCat.toSSetObjEquiv _ (op n)) f z) hh
  exact ht

noncomputable def weightsToNerve (w:OrderWeights P) : |nerve P| :=
  realizeSimplex (nerve P) (n:=⦋weightDim w⦌) (nerveOfChain (weightChain w)) (weightSimplex w)

lemma nerveToWeights_weightsToNerve (w:OrderWeights P) :
    nerveToWeights (weightsToNerve w)=w := by
  unfold weightsToNerve
  rw [nerveToWeights_simplex (n:=⦋weightDim w⦌)]
  exact orderWeightsOfChain_canonical w

noncomputable def supportedWeightMap {n:ℕ} (x:Fin (n+1)→o P)
    (z:StdSimplex ℝ (Fin (n+1))) :
    Fin (simplexSupportDim z+1) →o Fin (weightDim (orderWeightsOfChain x z)+1) :=
  { toFun:=fun i=>(weightEnum (orderWeightsOfChain x z)).symm
      ⟨x (simplexSupportInclusion z i),chainWeights_support_positive x z (simplexSupportEnum z i).property⟩
    monotone':=fun _ _ h=>(weightEnum (orderWeightsOfChain x z)).symm.monotone
      (x.monotone ((simplexSupportInclusion z).monotone h)) }

lemma supportedWeightMap_chain {n:ℕ} (x:Fin (n+1)→o P)
    (z:StdSimplex ℝ (Fin (n+1))) :
    (weightChain (orderWeightsOfChain x z)).comp (supportedWeightMap x z)=
      x.comp (simplexSupportInclusion z) := by
  apply DFunLike.ext
  intro i
  change ((weightEnum (orderWeightsOfChain x z)) ((weightEnum (orderWeightsOfChain x z)).symm _)).val=_
  exact congrArg Subtype.val ((weightEnum (orderWeightsOfChain x z)).apply_symm_apply _)

lemma supportedWeightMap_simplex {n:ℕ} (x:Fin (n+1)→o P)
    (z:StdSimplex ℝ (Fin (n+1))) :
    StdSimplex.map (supportedWeightMap x z) (simplexSupported z)=
      weightSimplex (orderWeightsOfChain x z) := by
  apply chainWeights_coordinates_injective _ (weightChain_injective _)
  rw [← chainWeights_natural,supportedWeightMap_chain,chainWeights_natural,simplexSupported_map]
  exact congrArg OrderWeights.weights (orderWeightsOfChain_canonical (orderWeightsOfChain x z)).symm

lemma weightsToNerve_simplex {n:SimplexCategory} (x:(nerve P).obj (op n))
    (z:StdSimplex ℝ (Fin (n.len+1))) :
    weightsToNerve (orderWeightsOfChain (nerveChain x) z)=realizeSimplex (nerve P) x z := by
  let a:⦋simplexSupportDim z⦌⟶n:=SimplexCategory.mkHom (simplexSupportInclusion z)
  let b:⦋simplexSupportDim z⦌⟶⦋weightDim (orderWeightsOfChain (nerveChain x) z)⦌:=
    SimplexCategory.mkHom (supportedWeightMap (nerveChain x) z)
  have he:(nerve P).map b.op (nerveOfChain (weightChain (orderWeightsOfChain (nerveChain x) z)))=
      (nerve P).map a.op x:=by
    apply nerve.ext_of_isThin
    funext i
    exact DFunLike.congr_fun (supportedWeightMap_chain (nerveChain x) z) i
  have h₁:=realizeSimplex_natural (nerve P) b
    (nerveOfChain (weightChain (orderWeightsOfChain (nerveChain x) z))) (simplexSupported z)
  have h₂:=realizeSimplex_natural (nerve P) a x (simplexSupported z)
  change _=realizeSimplex (nerve P) x (StdSimplex.map (simplexSupportInclusion z) (simplexSupported z)) at h₂
  rw [simplexSupported_map] at h₂
  have hb:StdSimplex.map b.toOrderHom (simplexSupported z)=weightSimplex (orderWeightsOfChain (nerveChain x) z):=
    supportedWeightMap_simplex (nerveChain x) z
  rw [he,hb] at h₁
  exact h₁.symm.trans h₂

lemma weightsToNerve_continuous : Continuous (weightsToNerve (P:=P)) := by
  rw [orderWeights_continuous_iff]
  intro n x
  simp_rw [weightsToNerve_simplex]
  exact (realizeSimplex (nerve P) x).continuous

noncomputable def nerveWeightsHomeomorph : |nerve P| ≃ₜ OrderWeights P := by
  have he:ContinuousMap.comp ⟨weightsToNerve,weightsToNerve_continuous⟩ nerveToWeights=ContinuousMap.id |nerve P|:=by
    have ht:TopCat.ofHom (ContinuousMap.comp ⟨weightsToNerve,weightsToNerve_continuous⟩ nerveToWeights)=𝟙 |nerve P|:=by
      apply (sSetTopAdj.homEquiv _ _).injective
      rw [Adjunction.homEquiv_unit,Adjunction.homEquiv_unit]
      ext n x
      apply (TopCat.toSSetObjEquiv _ n).injective
      ext z
      change weightsToNerve (nerveToWeights (realizeSimplex (nerve P) x z))=realizeSimplex (nerve P) x z
      rw [nerveToWeights_simplex,weightsToNerve_simplex]
    exact congrArg TopCat.Hom.hom ht
  exact {
    toFun:=nerveToWeights
    invFun:=weightsToNerve
    left_inv:=fun x=>ContinuousMap.congr_fun he x
    right_inv:=nerveToWeights_weightsToNerve
    continuous_toFun:=nerveToWeights.continuous
    continuous_invFun:=weightsToNerve_continuous }

end HarmonicArtin

end OAI
