import OAI.SetTheory.PartitionPrinciple.Definability.PresentedRowAssignmentGraphs

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {G R : Type u} [Group G] [PartialOrder R]
variable (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
variable (Q J B : ZFSet.{u})

theorem presentedRowAssignmentGraph_totalValue {V : ZFSet.{u}}
    (shape : Q ⊆ ZFSet.prod c.carrier V)
    (function : ZFSet.IsFunc (ZFSet.prod t.carrier Q) Q
      (rawRowAssignmentActionGraph t.carrier Q c.carrier Q.sUnion.sUnion J (a.actionGraph c t) B))
    (g : G) (r : R) (A : ZFSet.{u}) (member : ZFSet.pair (c.encode r) A ∈ Q) :
    ZFSet.pair (c.encode (a.iso g r)) (relationImage A J (rawActionSection (t.encode g) B J)) ∈ Q ∧
    ZFSet.pair (ZFSet.pair (t.encode g) (ZFSet.pair (c.encode r) A))
      (ZFSet.pair (c.encode (a.iso g r)) (relationImage A J (rawActionSection (t.encode g) B J))) ∈
        rawRowAssignmentActionGraph t.carrier Q c.carrier Q.sUnion.sUnion J (a.actionGraph c t) B := by
  obtain ⟨y, edge, _unique⟩ := function.2 (ZFSet.pair (t.encode g) (ZFSet.pair (c.encode r) A))
    (ZFSet.pair_mem_prod.2 ⟨t.encode_mem g, member⟩)
  have hy := (ZFSet.pair_mem_prod.1 (function.1 edge)).2
  obtain ⟨q, D, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hy
  obtain ⟨_, _, row, data⟩ := (presentedRowAssignmentGraph_entry a c t Q J B g r q A D).1 edge
  rw [← row, data] at hy edge
  exact ⟨hy, edge⟩

end PartitionPilot.Forcing

end

end OAI
