import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyGraphs

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def relationImageEqualityFormula {n} (output domain codomain graph : Fin n) : BoundedFormula n :=
  .conj (.allMem output (.conj (.mem 0 codomain.succ)
    (imageMemberFormula 0 domain.succ graph.succ)))
    (.allMem codomain (imp (imageMemberFormula 0 domain.succ graph.succ) (.mem 0 output.succ)))

theorem truth_relationImageEqualityFormula {n} (output domain codomain graph : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (relationImageEqualityFormula output domain codomain graph) env ↔
      env output = relationImage (env domain) (env codomain) (env graph) := by
  simp only [relationImageEqualityFormula, Truth, truth_imageMemberFormula, truth_imp]
  change ((∀ y ∈ env output, y ∈ env codomain ∧ ∃ x ∈ env domain,
      ZFSet.pair x y ∈ env graph) ∧
    (∀ y ∈ env codomain, (∃ x ∈ env domain, ZFSet.pair x y ∈ env graph) → y ∈ env output)) ↔ _
  constructor
  · rintro ⟨forward, backward⟩
    apply ZFSet.ext
    intro y
    rw [mem_relationImage]
    exact ⟨forward y, fun h => backward y h.1 h.2⟩
  · intro equal
    constructor
    · intro y hy
      exact (mem_relationImage _ _ _ y).1 (equal ▸ hy)
    · intro y hy member
      exact equal ▸ (mem_relationImage _ _ _ y).2 ⟨hy, member⟩

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
