import OAI.SetTheory.PartitionPrinciple.Forcing.GroundForcingHistoryOrders

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

noncomputable def rawRowAssignmentOrder (Q rowOrder : ZFSet.{u}) : ZFSet.{u} :=
  rowAssignmentOrder Q Q.sUnion.sUnion Q.sUnion.sUnion rowOrder

theorem pair_mem_rawRowAssignmentOrder (Q rowOrder q A p D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈ rawRowAssignmentOrder Q rowOrder ↔
      ZFSet.pair q A ∈ Q ∧ ZFSet.pair p D ∈ Q ∧ ZFSet.pair q p ∈ rowOrder ∧ D ⊆ A := by
  rw [rawRowAssignmentOrder, pair_mem_rowAssignmentOrder]
  constructor
  · rintro ⟨hq, hp, _, _, _, _, below, data⟩
    exact ⟨hq, hp, below, data⟩
  · rintro ⟨hq, hp, below, data⟩
    exact ⟨hq, hp, pair_first_mem_doubleUnion hq, pair_second_mem_doubleUnion hq,
      pair_first_mem_doubleUnion hp, pair_second_mem_doubleUnion hp, below, data⟩

theorem rawRowAssignmentOrder_eq {Q C B rowOrder : ZFSet.{u}} (shape : Q ⊆ ZFSet.prod C B) :
    rawRowAssignmentOrder Q rowOrder = rowAssignmentOrder Q C B rowOrder := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ((mem_rowAssignmentOrder _ _ _ _ z).1 member).1
    obtain ⟨q, hq, A, hA, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
    obtain ⟨p, hp, D, hD, rfl⟩ := ZFSet.mem_prod.1 (shape hy)
    obtain ⟨_, _, below, data⟩ := (pair_mem_rawRowAssignmentOrder _ _ _ _ _ _).1 member
    exact (pair_mem_rowAssignmentOrder _ _ _ _ _ _ _ _).2 ⟨hx, hy, hq, hA, hp, hD, below, data⟩
  · intro member
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ((mem_rowAssignmentOrder _ _ _ _ z).1 member).1
    obtain ⟨q, _, A, _, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
    obtain ⟨p, _, D, _, rfl⟩ := ZFSet.mem_prod.1 (shape hy)
    obtain ⟨_, _, _, _, _, _, below, data⟩ := (pair_mem_rowAssignmentOrder _ _ _ _ _ _ _ _).1 member
    exact (pair_mem_rawRowAssignmentOrder _ _ _ _ _ _).2 ⟨hx, hy, below, data⟩

theorem TransitiveGround.refinementHistoryOrder_raw (M : TransitiveGround.{u})
    (rows rowOrder T stages history : ZFSet.{u}) :
    M.refinementHistoryOrder rows rowOrder T stages history =
      rawRowAssignmentOrder (M.refinementHistoryForcing rows T stages history) rowOrder :=
  (rawRowAssignmentOrder_eq (M.refinementHistoryForcing_shape rows T stages history)).symm

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_rowAssignmentOrder :
    GroundDefinableFunction M (fun env : Fin 4 → ZFSet.{u} =>
      rowAssignmentOrder (env 0) (env 1) (env 2) (env 3)) := by
  let v := GroundSetTerm.var M (n := 4)
  let bound := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 0, v 0]
  let formula : SetFormula 4 := (BoundedFormula.rowAssignmentOrderFormula 0 1 2 3).toFormula
  let term := GroundSetTerm.app (M.definable_separation separation formula) ![bound, v 1, v 2, v 3]
  refine { formula := term.definition.formula
           closed := fun env members => M.rowAssignmentOrder_mem pairing unions powers separation
             (members 0) (members 1) (members 2) (members 3)
           correct := ?_ }
  intro env members z hz
  rw [term.definition.correct env members z hz]
  have args : (fun j : Fin 3 => (![bound, v 1, v 2, v 3] j.succ).eval env) =
      ![env 1, env 2, env 3] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j
  have equal : term.eval env = rowAssignmentOrder (env 0) (env 1) (env 2) (env 3) := by
    change ZFSet.sep (fun w => Realize M.sets formula (extend w _)) (bound.eval env) = _
    rw [args]
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_sep, mem_rowAssignmentOrder]
    apply and_congr_right
    intro hw
    change Realize M.sets (BoundedFormula.rowAssignmentOrderFormula 0 1 2 3).toFormula
      (extend w ![env 1, env 2, env 3]) ↔ _
    rw [BoundedFormula.realize_toFormula M _ (extend w ![env 1, env 2, env 3])
      (Fin.cases (M.transitive (bound.ground env members) hw)
        (Fin.cases (members 1) (Fin.cases (members 2) (Fin.cases (members 3) (fun j => Fin.elim0 j))))),
      BoundedFormula.truth_rowAssignmentOrderFormula]
    rfl
  rw [equal]

noncomputable def definable_rawRowAssignmentOrder :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => rawRowAssignmentOrder (env 0) (env 1)) := by
  let v := GroundSetTerm.var M (n := 2)
  let fields := GroundSetTerm.app (M.definable_doubleUnion unions) ![v 0]
  exact (GroundSetTerm.app (M.definable_rowAssignmentOrder pairing unions powers separation)
    ![v 0, fields, fields, v 1]).definition

noncomputable def rawRowAssignmentOrderOutputFormula {n : Nat}
    (output Q rowOrder : Fin n) : SetFormula n :=
  reindex (extend output ![Q, rowOrder])
    (M.definable_rawRowAssignmentOrder pairing unions powers separation).formula

theorem realize_rawRowAssignmentOrderOutputFormula {n : Nat}
    (output Q rowOrder : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.rawRowAssignmentOrderOutputFormula pairing unions powers separation output Q rowOrder) env ↔
      env output = rawRowAssignmentOrder (env Q) (env rowOrder) := by
  unfold rawRowAssignmentOrderOutputFormula
  rw [realize_reindex, map_extend]
  exact (M.definable_rawRowAssignmentOrder pairing unions powers separation).correct
    (fun j => env (![Q, rowOrder] j)) (fun j => members _) (env output) (members output)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
