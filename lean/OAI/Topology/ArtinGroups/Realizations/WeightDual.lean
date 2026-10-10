import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightCarrier
import OAI.Topology.ArtinGroups.Harmonic.FiniteChainEnum

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def weightDual (w:OrderWeights P) : OrderWeights Pᵒᵈ where
  weights:=w.weights
  nonneg:=w.nonneg
  total:=w.total
  chain:=by
    intro a ha b hb
    exact (w.chain a ha b hb).symm

lemma weightDual_continuous : Continuous (weightDual (P:=P)) := by
  rw [orderWeights_continuous_iff]
  intro n x
  let c:=nerveChain x
  let C:Finset Pᵒᵈ:=Finset.univ.image c
  have hc:IsChain (·≤·) (↑C:Set Pᵒᵈ):=by
    rintro a ha b hb hn
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hb
    exact (le_total i j).symm.imp (fun h=>c.monotone h) (fun h=>c.monotone h)
  have hne:C.Nonempty:=Finset.Nonempty.image Finset.univ_nonempty _
  apply continuous_of_finite_chain_carrier _ C hc hne
  · intro z
    exact chainWeights_support c z
  · intro p
    exact (weightEval_continuous (P:=P) p).comp (chainWeightsChart_continuous c)

noncomputable def weightDualHomeomorph : OrderWeights P≃ₜOrderWeights Pᵒᵈ where
  toFun:=weightDual
  invFun:=weightDual
  left_inv _:=rfl
  right_inv _:=rfl
  continuous_toFun:=weightDual_continuous
  continuous_invFun:=weightDual_continuous

end HarmonicArtin

end OAI
