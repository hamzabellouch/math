import OAI.SetTheory.PartitionPrinciple.Geometry.GroundDefinableRowAssignmentOrders
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundDefinableRefinementHistories

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

noncomputable def refinementHistoryForcingOutputFormula {n : Nat}
    (output rows T stages history N : Fin n) : SetFormula n :=
  let old := suffixIndex n 2
  let v := prefixIndex n 2
  exBlock 2 (.conj (refinementDataHistoryIndicesSetFormula (v 0) (old stages) (old history))
    (.conj (refinementDataHistoryLevelsSetFormula (v 1) (old stages) (old history) (old T))
      (forcingHistoryConditionsOutputFormula (old output) (old rows) (v 0) (old T)
        (old stages) (old history) (v 1) (old N))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_refinementHistoryForcingOutputFormula {n : Nat}
    (output rows T stages history N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (naturals : env N = ZFSet.omega) :
    Realize M.sets (refinementHistoryForcingOutputFormula output rows T stages history N) env ↔
      env output = M.refinementHistoryForcing (env rows) (env T) (env stages) (env history) := by
  rw [refinementHistoryForcingOutputFormula, realize_exBlock]
  have actual (fields : Fin 2 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets (.conj
        (refinementDataHistoryIndicesSetFormula (prefixIndex n 2 0)
          (suffixIndex n 2 stages) (suffixIndex n 2 history))
        (.conj (refinementDataHistoryLevelsSetFormula (prefixIndex n 2 1)
          (suffixIndex n 2 stages) (suffixIndex n 2 history) (suffixIndex n 2 T))
          (forcingHistoryConditionsOutputFormula (suffixIndex n 2 output) (suffixIndex n 2 rows)
            (prefixIndex n 2 0) (suffixIndex n 2 T) (suffixIndex n 2 stages)
            (suffixIndex n 2 history) (prefixIndex n 2 1) (suffixIndex n 2 N))))
        (extendMany 2 fields env) ↔
      fields 0 = refinementDataHistoryIndices (env stages) (env history) ∧
        fields 1 = refinementDataHistoryLevels (env stages) (env history) (env T) ∧
        env output = M.forcingHistoryConditions (env rows) (fields 0) (env T)
          (env stages) (env history) (fields 1) := by
    have bounds := extendMany_members 2 fields env ground members
    apply and_congr
    · simpa only [extendMany_prefix, extendMany_suffix] using
        M.realize_refinementDataHistoryIndicesSetFormula pairing unions powers separation
          (prefixIndex n 2 0) (suffixIndex n 2 stages) (suffixIndex n 2 history)
          (extendMany 2 fields env) bounds
    apply and_congr
    · simpa only [extendMany_prefix, extendMany_suffix] using
        M.realize_refinementDataHistoryLevelsSetFormula pairing unions powers separation
          (prefixIndex n 2 1) (suffixIndex n 2 stages) (suffixIndex n 2 history) (suffixIndex n 2 T)
          (extendMany 2 fields env) bounds
    · simpa only [extendMany_prefix, extendMany_suffix] using
        M.realize_forcingHistoryConditionsOutputFormula pairing separation
          (suffixIndex n 2 output) (suffixIndex n 2 rows) (prefixIndex n 2 0)
          (suffixIndex n 2 T) (suffixIndex n 2 stages) (suffixIndex n 2 history)
          (prefixIndex n 2 1) (suffixIndex n 2 N) (extendMany 2 fields env) bounds
          (by simpa only [extendMany_suffix] using naturals)
  constructor
  · rintro ⟨fields, ground, body⟩
    obtain ⟨indices, levels, outputEq⟩ := (actual fields ground).1 body
    rw [indices, levels] at outputEq
    exact outputEq
  · intro equal
    let fields : Fin 2 → ZFSet.{u} :=
      ![refinementDataHistoryIndices (env stages) (env history),
        refinementDataHistoryLevels (env stages) (env history) (env T)]
    have ground : ∀ j, fields j ∈ M.sets :=
      Fin.cases (M.refinementDataHistoryIndices_mem pairing unions powers separation
        (members stages) (members history))
        (Fin.cases (M.refinementDataHistoryLevels_mem pairing unions powers separation
          (members stages) (members history) (members T)) (fun j => Fin.elim0 j))
    exact ⟨fields, ground, (actual fields ground).2 ⟨rfl, rfl, equal⟩⟩

theorem exists_unique_refinementHistoryForcingOutput
    {rows T stages history : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hT : T ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    ∃ output ∈ M.sets,
      Realize M.sets (refinementHistoryForcingOutputFormula 0 1 2 3 4 5)
        ![output, rows, T, stages, history, ZFSet.omega] ∧
      ∀ other ∈ M.sets,
        Realize M.sets (refinementHistoryForcingOutputFormula 0 1 2 3 4 5)
          ![other, rows, T, stages, history, ZFSet.omega] → other = output := by
  have ground := M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hStages hHistory omega
  have meaning (output : ZFSet.{u}) (hOutput : output ∈ M.sets) :
      Realize M.sets (refinementHistoryForcingOutputFormula 0 1 2 3 4 5)
        ![output, rows, T, stages, history, ZFSet.omega] ↔
      output = M.refinementHistoryForcing rows T stages history :=
    M.realize_refinementHistoryForcingOutputFormula pairing unions powers separation 0 1 2 3 4 5 _
      (Fin.cases hOutput (Fin.cases hRows (Fin.cases hT (Fin.cases hStages
        (Fin.cases hHistory (Fin.cases omega (fun j => Fin.elim0 j))))))) rfl
  exact ⟨_, ground, (meaning _ ground).2 rfl, fun other member valid => (meaning other member).1 valid⟩

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def refinementHistoryOrderOutputFormula {n : Nat}
    (output rows rowOrder T stages history N : Fin n) : SetFormula n :=
  .ex (.conj (refinementHistoryForcingOutputFormula 0 rows.succ T.succ stages.succ history.succ N.succ)
    (M.rawRowAssignmentOrderOutputFormula pairing unions powers separation output.succ 0 rowOrder.succ))

theorem realize_refinementHistoryOrderOutputFormula {n : Nat}
    (output rows rowOrder T stages history N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) (naturals : env N = ZFSet.omega) :
    Realize M.sets (M.refinementHistoryOrderOutputFormula pairing unions powers separation
      output rows rowOrder T stages history N) env ↔
      env output = M.refinementHistoryOrder (env rows) (env rowOrder) (env T) (env stages) (env history) := by
  unfold refinementHistoryOrderOutputFormula
  rw [realize_ex]
  have meaning (Q : ZFSet.{u}) (hQ : Q ∈ M.sets) :
      Realize M.sets (.conj
        (refinementHistoryForcingOutputFormula 0 rows.succ T.succ stages.succ history.succ N.succ)
        (M.rawRowAssignmentOrderOutputFormula pairing unions powers separation output.succ 0 rowOrder.succ))
        (extend Q env) ↔
      Q = M.refinementHistoryForcing (env rows) (env T) (env stages) (env history) ∧
        env output = rawRowAssignmentOrder Q (env rowOrder) :=
    and_congr (M.realize_refinementHistoryForcingOutputFormula pairing unions powers separation
      0 rows.succ T.succ stages.succ history.succ N.succ (extend Q env) (Fin.cases hQ members) naturals)
      (M.realize_rawRowAssignmentOrderOutputFormula pairing unions powers separation
        output.succ 0 rowOrder.succ (extend Q env) (Fin.cases hQ members))
  constructor
  · rintro ⟨Q, hQ, recognized⟩
    obtain ⟨rfl, equal⟩ := (meaning Q hQ).1 recognized
    rw [M.refinementHistoryOrder_raw]
    exact equal
  · intro equal
    have ground := M.refinementHistoryForcing_mem pairing unions powers separation
      (members rows) (members T) (members stages) (members history) (naturals ▸ members N)
    refine ⟨_, ground, (meaning _ ground).2 ⟨rfl, ?_⟩⟩
    rw [M.refinementHistoryOrder_raw] at equal
    exact equal

theorem exists_unique_refinementHistoryOrderOutput
    {rows rowOrder T stages history : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hOrder : rowOrder ∈ M.sets) (hT : T ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    ∃ output ∈ M.sets,
      Realize M.sets (M.refinementHistoryOrderOutputFormula pairing unions powers separation 0 1 2 3 4 5 6)
        ![output, rows, rowOrder, T, stages, history, ZFSet.omega] ∧
      ∀ other ∈ M.sets,
        Realize M.sets (M.refinementHistoryOrderOutputFormula pairing unions powers separation 0 1 2 3 4 5 6)
          ![other, rows, rowOrder, T, stages, history, ZFSet.omega] → other = output := by
  have ground := M.refinementHistoryOrder_mem pairing unions powers separation hRows hOrder hT hStages hHistory omega
  have meaning (output : ZFSet.{u}) (hOutput : output ∈ M.sets) :
      Realize M.sets (M.refinementHistoryOrderOutputFormula pairing unions powers separation 0 1 2 3 4 5 6)
        ![output, rows, rowOrder, T, stages, history, ZFSet.omega] ↔
      output = M.refinementHistoryOrder rows rowOrder T stages history :=
    M.realize_refinementHistoryOrderOutputFormula pairing unions powers separation 0 1 2 3 4 5 6 _
      (Fin.cases hOutput (Fin.cases hRows (Fin.cases hOrder (Fin.cases hT (Fin.cases hStages
        (Fin.cases hHistory (Fin.cases omega (fun j => Fin.elim0 j)))))))) rfl
  exact ⟨_, ground, (meaning _ ground).2 rfl, fun other member valid => (meaning other member).1 valid⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
