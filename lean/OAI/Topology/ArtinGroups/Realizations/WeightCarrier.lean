import Mathlib
import OAI.Topology.ArtinGroups.Realizations.OrderWeights

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite Convexity

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

lemma weightEval_continuous (p:P) : Continuous (fun w:OrderWeights P=>w.weights p) := by
  rw [orderWeights_continuous_iff]
  intro n x
  change Continuous (fun z:StdSimplex ℝ (Fin (n.len+1))=>chainWeights (nerveChain x) z p)
  simp_rw [chainWeights_apply]
  apply continuous_finsetSum
  intro i _
  by_cases h:nerveChain x i=p
  · simp only [h,ite_eq_left]
    exact StdSimplex.continuous_weights_apply ℝ i
  · simp only [h]
    exact continuous_const

noncomputable instance : T2Space (OrderWeights P) :=
  T2Space.of_injective_continuous
    (f:=fun w:OrderWeights P=>fun p=>w.weights p)
    (by intro x y h;apply OrderWeights.ext;exact DFunLike.ext' h)
    (continuous_pi weightEval_continuous)

lemma isClosed_prod_discrete_left {X Y:Type*} [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace Y] {A:Set (X×Y)} (h:∀x,IsClosed {y | (x,y)∈A}) : IsClosed A := by
  have he:Aᶜ=⋃x:X,({x}:Set X) ×ˢ {y | (x,y)∉A}:=by
    ext ⟨x,y⟩
    simp
  rw [← isOpen_compl_iff,he]
  exact isOpen_iUnion (fun x=>(isOpen_discrete _).prod (h x).isOpen_compl)

lemma orderWeights_isClosed_iff (A:Set (OrderWeights P)) :
    IsClosed A ↔ ∀(n:SimplexCategory) (x:(nerve P).obj (op n)),
      IsClosed ((fun z:StdSimplex ℝ (Fin (n.len+1))=>orderWeightsOfChain (nerveChain x) z) ⁻¹' A) := by
  let (n:SimplexCategory):TopologicalSpace ((nerve P).obj (op n)):=⊥
  let (n:SimplexCategory):DiscreteTopology ((nerve P).obj (op n)):=⟨rfl⟩
  change @IsClosed _ (TopologicalSpace.coinduced orderWeightsChart inferInstance) A ↔ _
  rw [isClosed_coinduced,isClosed_sigma_iff]
  constructor
  · intro h n x
    exact (h n).preimage (continuous_const.prodMk continuous_id)
  · intro h n
    exact isClosed_prod_discrete_left (h n)

def weightCarrier (K:Set (OrderWeights P)) : Set P :=
  {p | ∃w∈K,p∈w.weights.support}

lemma weightCarrier_finite_of_finite {K:Set (OrderWeights P)} (hK:K.Finite) :
    (weightCarrier K).Finite := by
  have he:weightCarrier K=⋃w∈K,(↑w.weights.support:Set P):=by ext p;simp [weightCarrier]
  rw [he]
  exact hK.biUnion (fun w _=>w.weights.support.finite_toSet)

theorem weightCarrier_finite_of_isCompact {K:Set (OrderWeights P)} (hK:IsCompact K) :
    (weightCarrier K).Finite := by
  by_contra hn
  let U:=weightCarrier K
  have hi:U.Infinite:=hn
  choose f hf using (fun p:U=>p.property)
  let E:Set (OrderWeights P):=Set.range f
  have hEK:E⊆K:=by rintro w ⟨p,rfl⟩;exact (hf p).1
  have hEf:∀(n:SimplexCategory) (x:(nerve P).obj (op n)),
      (E∩Set.range (fun z:StdSimplex ℝ (Fin (n.len+1))=>orderWeightsOfChain (nerveChain x) z)).Finite:=by
    intro n x
    let B:Finset P:=Finset.univ.image (nerveChain x)
    have hB:(Subtype.val ⁻¹' (↑B : Set P) : Set U).Finite:=
      B.finite_toSet.preimage Subtype.val_injective.injOn
    apply (hB.image f).subset
    rintro w ⟨⟨p,rfl⟩,⟨z,hz⟩⟩
    refine ⟨p,?_,rfl⟩
    have hp:p.val∈(chainWeights (nerveChain x) z).support:=by
      change p.val∈(orderWeightsOfChain (nerveChain x) z).weights.support
      have he : orderWeightsOfChain (nerveChain x) z = f p := hz
      rw [he]
      exact (hf p).2
    exact chainWeights_support _ _ hp
  have hclosed:∀A:Set (OrderWeights P),A⊆E→IsClosed A:=by
    intro A hAE
    rw [orderWeights_isClosed_iff]
    intro n x
    let g:=fun z:StdSimplex ℝ (Fin (n.len+1))=>orderWeightsOfChain (nerveChain x) z
    have hfin:(A∩Set.range g).Finite:=(hEf n x).subset (fun _ h=>⟨hAE h.1,h.2⟩)
    have he:g⁻¹'A=g⁻¹'(A∩Set.range g):=by ext z;simp
    rw [he]
    exact hfin.isClosed.preimage (orderWeightsChart_continuous x)
  have hEc:IsCompact E:=hK.of_isClosed_subset (hclosed E (fun _ h=>h)) hEK
  have hdis:DiscreteTopology E:=by
    rw [discreteTopology_iff_forall_isClosed]
    intro A
    have ha:IsClosed (Subtype.val '' A):=hclosed _ (by rintro w ⟨p,_,rfl⟩;exact p.property)
    have he:A=Subtype.val ⁻¹' (Subtype.val '' A):=by
      exact (Set.preimage_image_eq A Subtype.val_injective).symm
    rw [he]
    exact ha.preimage continuous_subtype_val
  have :DiscreteTopology E:=hdis
  have :CompactSpace E:=isCompact_iff_compactSpace.mp hEc
  have :Finite E:=finite_of_compact_of_discrete
  have hE:E.Finite:=Set.toFinite E
  apply hi
  apply (weightCarrier_finite_of_finite hE).subset
  intro p hp
  exact ⟨f ⟨p,hp⟩,⟨⟨p,hp⟩,rfl⟩,(hf ⟨p,hp⟩).2⟩

end HarmonicArtin

end OAI
