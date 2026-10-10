import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageOneOrder

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem rowAssignmentOrder_partialOrder {Q C B r : ZFSet.{u}}
    (shape : Q ⊆ ZFSet.prod C B) (rows : PartialOrderCode C r) :
    PartialOrderCode Q (rowAssignmentOrder Q C B r) := by
  refine ⟨fun z member => (mem_rowAssignmentOrder Q C B r z).1 member |>.1, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, hq, A, hA, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
    exact (pair_mem_rowAssignmentOrder Q C B r q A q A).2
      ⟨hz, hz, hq, hA, hq, hA, rows.refl q hq, fun _ h => h⟩
  · intro x hx y hy xy yx
    obtain ⟨q, hq, A, hA, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
    obtain ⟨p, hp, D, hD, rfl⟩ := ZFSet.mem_prod.1 (shape hy)
    have first := (pair_mem_rowAssignmentOrder Q C B r q A p D).1 xy
    have second := (pair_mem_rowAssignmentOrder Q C B r p D q A).1 yx
    have rowEq := rows.antisymm q hq p hp first.2.2.2.2.2.2.1 second.2.2.2.2.2.2.1
    have dataEq : A = D := ZFSet.ext (fun z =>
      ⟨fun h => second.2.2.2.2.2.2.2 h, fun h => first.2.2.2.2.2.2.2 h⟩)
    rw [rowEq, dataEq]
  · intro x hx y hy z hz xy yz
    obtain ⟨q, hq, A, hA, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
    obtain ⟨p, hp, D, hD, rfl⟩ := ZFSet.mem_prod.1 (shape hy)
    obtain ⟨s, hs, E, hE, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
    have first := (pair_mem_rowAssignmentOrder Q C B r q A p D).1 xy
    have second := (pair_mem_rowAssignmentOrder Q C B r p D s E).1 yz
    exact (pair_mem_rowAssignmentOrder Q C B r q A s E).2
      ⟨hx, hz, hq, hA, hs, hE,
        rows.trans q hq p hp s hs first.2.2.2.2.2.2.1 second.2.2.2.2.2.2.1,
        fun _ h => first.2.2.2.2.2.2.2 (second.2.2.2.2.2.2.2 h)⟩

theorem rowAssignmentOrder_top {Q C B r top : ZFSet.{u}}
    (shape : Q ⊆ ZFSet.prod C B)
    (rowTop : ∀ q ∈ C, ZFSet.pair q top ∈ r)
    (member : ZFSet.pair top ∅ ∈ Q) :
    ∀ z ∈ Q, ZFSet.pair z (ZFSet.pair top ∅) ∈ rowAssignmentOrder Q C B r := by
  have topShape := ZFSet.pair_mem_prod.1 (shape member)
  intro z hz
  obtain ⟨q, hq, A, hA, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
  exact (pair_mem_rowAssignmentOrder Q C B r q A top ∅).2
    ⟨hz, member, hq, hA, topShape.1, topShape.2, rowTop q hq,
      fun x impossible => False.elim (ZFSet.notMem_empty x impossible)⟩

end PartitionPilot.Forcing

end

end OAI
