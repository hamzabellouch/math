import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightEarlierLower

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

theorem orderWeights_contractible_unique_source (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x)
    (k:P→ℕ) (N:ℕ) (hk:∀x,k x≤N) (hmono:StrictMono k)
    (hl:∀v,Nonempty (WeightEarlierLower r v) →
      ContractibleSpace (OrderWeights (WeightEarlierLower r v)))
    (hu:∀v,Nonempty (WeightEarlierUpper r v) →
      ContractibleSpace (OrderWeights (WeightEarlierUpper r v)))
    (hs:∀x y,¬Nonempty (WeightEarlierLink r x) →
      ¬Nonempty (WeightEarlierLink r y) → x=y)
    (hne:Nonempty P) : ContractibleSpace (OrderWeights P) := by
  obtain ⟨c,_,hc⟩:=wf.has_min Set.univ (by obtain ⟨x⟩:=hne;exact ⟨x,Set.mem_univ _⟩)
  have hc':∀x,¬r x c:=fun x=>hc x (Set.mem_univ x)
  have hcL:¬Nonempty (WeightEarlierLink r c):=by
    rintro ⟨x,hx,_⟩
    exact hc' x hx
  apply orderWeights_contractible_of_earlier_links r wf htotal c hc'
  intro v hv
  have hn:Nonempty (WeightEarlierLink r v):=by
    by_contra hn
    exact hv (hs v c hn hcL)
  rcases weightLink_nonempty_parts r (fun x=>wf.irrefl.irrefl x) v hn with h|h
  · exact weightLink_contractible_of_lower r (fun x=>wf.irrefl.irrefl x) v k N hk hmono (hl v h)
  · exact weightLink_contractible_of_upper r (fun x=>wf.irrefl.irrefl x) v k N hk hmono (hu v h)

end HarmonicArtin

end OAI
