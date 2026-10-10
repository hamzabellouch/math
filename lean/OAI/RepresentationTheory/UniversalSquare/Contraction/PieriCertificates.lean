import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Pieri Certificates. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowSquare_pieri {p rs ss : List ℕ} {cs : List (List ℕ)}
    (plan : PackingPlan) (q δ : ℕ)
    (hp : GoodRows p) (hq : 0 < q) (hδ : δ = 1 ∨ δ = 2)
    (hv : plan.Valid p.length) (hb : BandsValid ((q,pairUpper q δ)::plan.bands))
    (hk : q ∉ plan.marks) (hd : q+δ ≤ p.length)
    (hc : ([q+δ,q]++plan.columns).Perm (transposeRows p))
    (hr : GoodRows rs) (hrl : rs.length ≤ 4) (hrs : rs.sum = 2*q+δ)
    (ho : δ = 2 → ∃ j ∈ List.range (rs.sum+1),
      (rs.countP (fun x => decide (j < x))) % 2 = 1)
    (hchain : ChainValid rs cs ss) (hs : plan.parts.Perm (stripSizes rs cs))
    (hn : ss.sum = p.sum) : RowSquare p ss := by
  let a := canonicalTableau (rowDiagram p) (rowDiagram_card p)
  let t := canonicalTableau (rowDiagram ss) ((rowDiagram_card ss).trans hn)
  refine ⟨p.sum,a,t,?_⟩
  apply pieriPlan_pos plan hq hδ hv hb hk (rowDiagram_height hp) hd
  · rwa [← transposeRows_eq hp]
  · exact hr
  · exact hrl
  · exact hrs
  · exact ho
  · exact hchain
  · exact hs

end UniversalTensorSquare
end
end

end OAI
