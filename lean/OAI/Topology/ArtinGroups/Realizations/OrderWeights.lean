import Mathlib

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory Opposite Convexity
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

structure OrderWeights (P:Type u) [PartialOrder P] where
  weights:P→₀ℝ
  nonneg:∀p,0≤weights p
  total:weights.sum (fun _ a=>a)=1
  chain:∀p∈weights.support,∀q∈weights.support,p≤q ∨ q≤p

@[ext] lemma OrderWeights.ext {x y:OrderWeights P} (h:x.weights=y.weights) : x=y := by
  cases x;cases y;cases h;rfl

lemma OrderWeights.support_nonempty (x:OrderWeights P) : x.weights.support.Nonempty := by
  by_contra hn
  have he:x.weights=0:=Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hn)
  have ht:=x.total
  rw [he,Finsupp.sum_zero_index] at ht
  norm_num at ht

noncomputable def chainWeights {n:ℕ} (x:Fin (n+1)→o P) (z:StdSimplex ℝ (Fin (n+1))) : P→₀ℝ :=
  ∑i,Finsupp.single (x i) (z.weights i)

lemma chainWeights_apply {n:ℕ} (x:Fin (n+1)→o P) (z:StdSimplex ℝ (Fin (n+1))) (p:P) :
    chainWeights x z p=∑i,if x i=p then z.weights i else 0 := by
  simp only [chainWeights,Finsupp.finsetSum_apply,Finsupp.single_apply]

lemma chainWeights_nonneg {n:ℕ} (x:Fin (n+1)→o P) (z:StdSimplex ℝ (Fin (n+1))) (p:P) :
    0≤chainWeights x z p := by
  rw [chainWeights_apply]
  exact Finset.sum_nonneg (fun i _=>by split_ifs; exacts [z.nonneg i,le_rfl])

lemma chainWeights_total {n:ℕ} (x:Fin (n+1)→o P) (z:StdSimplex ℝ (Fin (n+1))) :
    (chainWeights x z).sum (fun _ a=>a)=1 := by
  rw [chainWeights,← Finsupp.sum_finsetSum_index (by intros;rfl) (by intros;rfl)]
  simpa only [Finsupp.sum_single_index (h:=fun (_:P) (a:ℝ)=>a) (by rfl)] using z.total_of_fintype

lemma chainWeights_support {n:ℕ} (x:Fin (n+1)→o P) (z:StdSimplex ℝ (Fin (n+1))) :
    (chainWeights x z).support⊆Finset.univ.image x := by
  apply Finset.Subset.trans Finsupp.support_finsetSum
  intro p hp
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hp
  have he:p=x i:=Finset.mem_singleton.mp (Finsupp.support_single_subset hi)
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩

noncomputable def orderWeightsOfChain {n:ℕ} (x:Fin (n+1)→o P) (z:StdSimplex ℝ (Fin (n+1))) : OrderWeights P where
  weights:=chainWeights x z
  nonneg:=chainWeights_nonneg x z
  total:=chainWeights_total x z
  chain:=by
    intro p hp q hq
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp (chainWeights_support x z hp)
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp (chainWeights_support x z hq)
    exact (le_total i j).imp (fun h=>x.monotone h) (fun h=>x.monotone h)

noncomputable def nerveChain {n:SimplexCategory} (x:(nerve P).obj (op n)) : Fin (n.len+1)→o P where
  toFun:=x.obj
  monotone':=by intro i j h;exact leOfHom (x.map (homOfLE h))

noncomputable def orderWeightsChart : (Σn:SimplexCategory,((nerve P).obj (op n)) × StdSimplex ℝ (Fin (n.len+1)))→OrderWeights P :=
  fun p=>orderWeightsOfChain (nerveChain p.2.1) p.2.2

noncomputable instance : TopologicalSpace (OrderWeights P) := by
  letI (n:SimplexCategory):TopologicalSpace ((nerve P).obj (op n)):=⊥
  exact TopologicalSpace.coinduced orderWeightsChart inferInstance

lemma orderWeightsChart_continuous {n:SimplexCategory} (x:(nerve P).obj (op n)) :
    Continuous (fun z:StdSimplex ℝ (Fin (n.len+1))=>orderWeightsOfChain (nerveChain x) z) := by
  let (n:SimplexCategory):TopologicalSpace ((nerve P).obj (op n)):=⊥
  have hc : Continuous (orderWeightsChart (P:=P)) := continuous_coinduced_rng
  exact hc.comp ((continuous_sigmaMk (i:=n)).comp (continuous_const.prodMk continuous_id))

lemma orderWeights_continuous_iff {Y:Type*} [TopologicalSpace Y] (f:OrderWeights P→Y) :
    Continuous f ↔ ∀(n:SimplexCategory) (x:(nerve P).obj (op n)),
      Continuous (fun z:StdSimplex ℝ (Fin (n.len+1))=>f (orderWeightsOfChain (nerveChain x) z)) := by
  let (n:SimplexCategory):TopologicalSpace ((nerve P).obj (op n)):=⊥
  let (n:SimplexCategory):DiscreteTopology ((nerve P).obj (op n)):=⟨rfl⟩
  rw [continuous_coinduced_dom,continuous_sigma_iff]
  constructor
  · intro h n x
    exact (h n).comp (continuous_const.prodMk continuous_id)
  · intro h n
    exact continuous_prod_of_discrete_left.mpr (h n)

lemma chainWeights_natural {n m:ℕ} (x:Fin (m+1)→o P) (a:Fin (n+1)→o Fin (m+1))
    (z:StdSimplex ℝ (Fin (n+1))) :
    chainWeights (x.comp a) z=chainWeights x (StdSimplex.map a z) := by
  have chainWeights_eq {dimension : ℕ} (chain : Fin (dimension+1) →o P)
      (simplex : StdSimplex ℝ (Fin (dimension+1))) :
      chainWeights chain simplex = simplex.weights.mapDomain chain := by
    simp [chainWeights, Finsupp.mapDomain, Finsupp.sum_fintype]
  rw [chainWeights_eq, chainWeights_eq]
  exact Finsupp.mapDomain_comp (v := z.weights) (f := a) (g := x)

end HarmonicArtin

end OAI
