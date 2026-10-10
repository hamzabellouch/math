import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightEarlierLower

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

theorem orderWeights_contractible_of_lower_fibers (A:Set P) (k:P→ℕ) (N:ℕ)
    (hk:∀x,k x≤N) (hm:StrictMono k) (hA:ContractibleSpace (OrderWeights A))
    (hf:∀v,v∉A → ContractibleSpace (OrderWeights {x:P // x∈A ∧ x<v})) :
    ContractibleSpace (OrderWeights P) := by
  let d:P→ℕ:=fun x=>N-k x
  let r:=WeightJoinEarlier A d
  have hw:=weightJoinEarlier_wf A d
  apply orderWeights_contractible_of_initial r hw (weightJoinEarlier_total A d) A
    (weightJoinEarlier_initial A d) hA
  intro v hv
  have he:∀x,x<v → (r x v ↔ x∈A):=by
    intro x hx
    constructor
    · intro hr
      by_contra hn
      change WeightJoinEarlier A d x v at hr
      rw [weightJoinEarlier_iff] at hr
      have hlt:=hm hx
      have hb:=hk v
      simp [weightJoinKey,hn,hv,d] at hr
      omega
    · intro ha
      exact weightJoinEarlier_old A d ha hv
  let e:WeightEarlierLower r v ≃o {x:P // x∈A ∧ x<v}:={
    toFun:=fun x=>⟨x.val,(he x.val x.property.2).mp x.property.1,x.property.2⟩
    invFun:=fun x=>⟨x.val,(he x.val x.property.2).mpr x.property.1,x.property.2⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl
    map_rel_iff':=by intros;rfl }
  exact weightLink_contractible_of_lower r (fun x=>hw.irrefl.irrefl x) v k N hk hm
    ((weightHomeomorph e).contractibleSpace_iff.mpr (hf v hv))

end HarmonicArtin

end OAI
