import Mathlib
import OAI.Topology.ArtinGroups.Realizations.OrderWeights

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite Convexity

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable instance orderWeightSupportLinearOrder (w:OrderWeights P) :
    LinearOrder {p // p∈w.weights.support} :=
  IsChain.linearOrder (show IsChain (·<·) (↑w.weights.support:Set P) from
    fun left hleft right hright hne => (w.chain left hleft right hright).imp
      (fun hle => lt_of_le_of_ne hle hne) (fun hle => lt_of_le_of_ne hle hne.symm))

noncomputable def weightDim (w:OrderWeights P) : ℕ := w.weights.support.card-1

lemma weightDim_succ (w:OrderWeights P) : weightDim w+1=w.weights.support.card := by
  have :=w.support_nonempty.card_pos
  unfold weightDim
  omega

noncomputable def weightEnum (w:OrderWeights P) :
    Fin (weightDim w+1) ≃o {p // p∈w.weights.support} :=
  Fintype.orderIsoFinOfCardEq _ (by rw [Fintype.card_coe,weightDim_succ])

noncomputable def weightChain (w:OrderWeights P) : Fin (weightDim w+1) →o P where
  toFun:=fun i=>(weightEnum w i).val
  monotone':=fun _ _ h=>(weightEnum w).monotone h

lemma weightChain_injective (w:OrderWeights P) : Function.Injective (weightChain w) :=
  Subtype.val_injective.comp (weightEnum w).injective

noncomputable def weightSimplex (w:OrderWeights P) : StdSimplex ℝ (Fin (weightDim w+1)) :=
  ⟨Finsupp.equivFunOnFinite.symm (fun coordinate=>w.weights (weightChain w coordinate)),
    fun coordinate=>w.nonneg _,by
    have he:=Equiv.sum_comp (weightEnum w).toEquiv (fun p=>w.weights p.val)
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑i,w.weights (weightChain w i))=1
    rw [show (∑i,w.weights (weightChain w i))=∑p:w.weights.support,w.weights p.val from he]
    rw [Finset.sum_coe_sort]
    exact w.total⟩

lemma chainWeights_injective_apply {n:ℕ} (x:Fin (n+1)→o P)
    (hx:Function.Injective x) (z:StdSimplex ℝ (Fin (n+1))) (i:Fin (n+1)) :
    chainWeights x z (x i)=z.weights i := by
  rw [chainWeights_apply,Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hx.ne hj]
  · simp

lemma orderWeightsOfChain_canonical (w:OrderWeights P) :
    orderWeightsOfChain (weightChain w) (weightSimplex w)=w := by
  apply OrderWeights.ext
  ext p
  by_cases hp:p∈w.weights.support
  · obtain ⟨i,hi⟩:∃i,weightChain w i=p:=by
      exact ⟨(weightEnum w).symm ⟨p,hp⟩,congrArg Subtype.val ((weightEnum w).apply_symm_apply _)⟩
    rw [← hi]
    exact chainWeights_injective_apply _ (weightChain_injective w) _ i
  · change chainWeights _ _ p=w.weights p
    rw [Finsupp.notMem_support_iff.mp hp,chainWeights_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hn:weightChain w i≠p:=by
      intro he
      exact hp (he ▸ (weightEnum w i).property)
    simp [hn]

lemma chainWeights_coordinates_injective {n:ℕ} (x:Fin (n+1)→o P)
    (hx:Function.Injective x) {z z':StdSimplex ℝ (Fin (n+1))}
    (h:chainWeights x z=chainWeights x z') : z=z' := by
  apply StdSimplex.ext
  ext coordinate
  have he:=congrArg (fun weights:P→₀ℝ=>weights (x coordinate)) h
  simpa only [chainWeights_injective_apply x hx] using he

end HarmonicArtin

end OAI
