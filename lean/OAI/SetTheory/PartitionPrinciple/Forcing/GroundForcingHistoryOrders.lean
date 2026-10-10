import OAI.SetTheory.PartitionPrinciple.Geometry.RowAssignmentOrderLaws
import OAI.SetTheory.PartitionPrinciple.Transfinite.RefinementBirthEnumerationFairness

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def refinementHistoryOrder (rows rowOrder T stages history : ZFSet.{u}) : ZFSet.{u} :=
  rowAssignmentOrder (M.refinementHistoryForcing rows T stages history) rows
    (M.groundSmallSubsets (stageOneAssignments (refinementDataHistoryIndices stages history) T) ZFSet.omega)
    rowOrder

theorem refinementHistoryForcing_shape (rows T stages history : ZFSet.{u}) :
    M.refinementHistoryForcing rows T stages history ⊆
      ZFSet.prod rows (M.groundSmallSubsets
        (stageOneAssignments (refinementDataHistoryIndices stages history) T) ZFSet.omega) :=
  fun z member => (M.mem_refinementHistoryForcing rows T stages history z).1 member |>.1

theorem refinementHistoryOrder_partialOrder {rows rowOrder : ZFSet.{u}}
    (order : PartialOrderCode rows rowOrder) (T stages history : ZFSet.{u}) :
    PartialOrderCode (M.refinementHistoryForcing rows T stages history)
      (M.refinementHistoryOrder rows rowOrder T stages history) :=
  rowAssignmentOrder_partialOrder (M.refinementHistoryForcing_shape rows T stages history) order

theorem pair_mem_refinementHistoryOrder (rows rowOrder T stages history q A p D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈ M.refinementHistoryOrder rows rowOrder T stages history ↔
      ZFSet.pair q A ∈ M.refinementHistoryForcing rows T stages history ∧
        ZFSet.pair p D ∈ M.refinementHistoryForcing rows T stages history ∧
        ZFSet.pair q p ∈ rowOrder ∧ D ⊆ A := by
  rw [refinementHistoryOrder, pair_mem_rowAssignmentOrder]
  constructor
  · rintro ⟨hq, hp, _, _, _, _, below, data⟩
    exact ⟨hq, hp, below, data⟩
  · rintro ⟨hq, hp, below, data⟩
    have qShape := ZFSet.pair_mem_prod.1 (M.refinementHistoryForcing_shape rows T stages history hq)
    have pShape := ZFSet.pair_mem_prod.1 (M.refinementHistoryForcing_shape rows T stages history hp)
    exact ⟨hq, hp, qShape.1, qShape.2, pShape.1, pShape.2, below, data⟩

theorem refinementHistoryOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {rows rowOrder T stages history : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hOrder : rowOrder ∈ M.sets) (hT : T ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.refinementHistoryOrder rows rowOrder T stages history ∈ M.sets :=
  M.rowAssignmentOrder_mem pairing unions powers separation
    (M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hStages hHistory omega)
    hRows (M.groundSmallSubsets_mem powers separation
      (M.stageOneAssignments_mem pairing unions powers separation
        (M.refinementDataHistoryIndices_mem pairing unions powers separation hStages hHistory) hT) omega) hOrder

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
