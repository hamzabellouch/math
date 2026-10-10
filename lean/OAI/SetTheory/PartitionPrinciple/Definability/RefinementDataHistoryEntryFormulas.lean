import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStructuralHistoryTestUnions

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem mem_refinementDataHistoryIndices (stages history x : ZFSet.{u}) :
    x ∈ refinementDataHistoryIndices stages history ↔
      ∃ alpha ∈ stages, ∃ d : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history ∧ x ∈ d 0 := by
  rw [refinementDataHistoryIndices, mem_refinementHistoryIndices]
  constructor
  · rintro ⟨alpha, halpha, I, entry, member⟩
    obtain ⟨_, d, stored, rfl⟩ := (pair_mem_refinementDataHistoryField _ _ _ _ _).1 entry
    exact ⟨alpha, halpha, d, stored, member⟩
  · rintro ⟨alpha, halpha, d, entry, member⟩
    exact ⟨alpha, halpha, d 0,
      (pair_mem_refinementDataHistoryField _ _ _ _ _).2 ⟨halpha, d, entry, rfl⟩, member⟩

theorem pair_mem_refinementDataHistoryLevels (stages history T assignment xi : ZFSet.{u}) :
    ZFSet.pair assignment xi ∈ refinementDataHistoryLevels stages history T ↔
      ∃ i ∈ refinementDataHistoryIndices stages history, ∃ u ∈ T, ∃ w ∈ T,
        assignment = stageOneAssignment i u w ∧ xi ∈ stages ∧
          ∃ fields : Fin 6 → ZFSet.{u}, i = nonemptyTupleCode 5 fields ∧ xi = fields 0 := by
  change ZFSet.pair assignment xi ∈ assignmentIndexLevels
    (refinementDataHistoryIndices stages history) T stages
    (refinementIndexFieldGraph (refinementDataHistoryIndices stages history) stages 0) ↔ _
  rw [pair_mem_assignmentIndexLevels]
  constructor
  · rintro ⟨i, hi, u, hu, w, hw, equal, hxi, entry⟩
    exact ⟨i, hi, u, hu, w, hw, equal, hxi,
      ((pair_mem_refinementIndexFieldGraph _ _ _ _ _).1 entry).2.2⟩
  · rintro ⟨i, hi, u, hu, w, hw, equal, hxi, fields⟩
    exact ⟨i, hi, u, hu, w, hw, equal, hxi,
      (pair_mem_refinementIndexFieldGraph _ _ _ _ _).2 ⟨hi, hxi, fields⟩⟩

namespace BoundedFormula
noncomputable def refinementDataHistoryIndicesEntryFormula {n : Nat}
    (stages history x : Fin n) : BoundedFormula n :=
  exGraphFields history (.conj (.mem 1 stages.succ.succ)
    (exPairFields 0 (.conj (tupleShapeFormula 13 0) (.mem x.succ.succ.succ.succ 1))))

theorem truth_refinementDataHistoryIndicesEntryFormula {n : Nat}
    (stages history x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (refinementDataHistoryIndicesEntryFormula stages history x) env ↔
      env x ∈ refinementDataHistoryIndices (env stages) (env history) := by
  rw [mem_refinementDataHistoryIndices]
  simp only [refinementDataHistoryIndicesEntryFormula, truth_exGraphFields, Truth,
    truth_exPairFields, truth_tupleShapeFormula]
  change (∃ alpha data, ZFSet.pair alpha data ∈ env history ∧ alpha ∈ env stages ∧
    ∃ I tail, data = ZFSet.pair I tail ∧ (∃ fields : Fin 14 → ZFSet.{u},
      tail = nonemptyTupleCode 13 fields) ∧ env x ∈ I) ↔ _
  constructor
  · rintro ⟨alpha, data, entry, halpha, I, tail, pair, ⟨fields, tuple⟩, member⟩
    let d : Fin 15 → ZFSet.{u} := Fin.cases I fields
    refine ⟨alpha, halpha, d, ?_, member⟩
    have equal : data = refinementFormulaDataCode d := pair.trans (congrArg (ZFSet.pair I) tuple)
    exact equal ▸ entry
  · rintro ⟨alpha, halpha, d, entry, member⟩
    exact ⟨alpha, refinementFormulaDataCode d, entry, halpha, d 0,
      nonemptyTupleCode 13 (fun i => d i.succ), rfl,
      ⟨fun i => d i.succ, rfl⟩, member⟩

noncomputable def refinementDataHistoryLevelsEntryFormula {n : Nat}
    (stages history T z : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  exPairFields z (exPairFields 1 (exPairFields 0
    (.conj (refinementDataHistoryIndicesEntryFormula (lift stages) (lift history) 3)
      (.conj (.mem 1 (lift T)) (.conj (.mem 0 (lift T))
        (.conj (.mem 4 (lift stages)) (tupleFieldFormula 5 3 4 0)))))))

theorem truth_refinementDataHistoryLevelsEntryFormula {n : Nat}
    (stages history T z : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (refinementDataHistoryLevelsEntryFormula stages history T z) env ↔
      env z ∈ refinementDataHistoryLevels (env stages) (env history) (env T) := by
  simp only [refinementDataHistoryLevelsEntryFormula, truth_exPairFields, Truth,
    truth_refinementDataHistoryIndicesEntryFormula, truth_tupleFieldFormula]
  change (∃ assignment xi, env z = ZFSet.pair assignment xi ∧
    ∃ i tail, assignment = ZFSet.pair i tail ∧ ∃ u w, tail = ZFSet.pair u w ∧
      i ∈ refinementDataHistoryIndices (env stages) (env history) ∧ u ∈ env T ∧ w ∈ env T ∧
        xi ∈ env stages ∧ ∃ fields : Fin 6 → ZFSet.{u},
          i = nonemptyTupleCode 5 fields ∧ xi = fields 0) ↔ _
  constructor
  · rintro ⟨assignment, xi, equal, i, tail, pair, u, w, tailEq, hi, hu, hw, hxi, fields⟩
    rw [equal]
    apply (pair_mem_refinementDataHistoryLevels _ _ _ _ _).2
    exact ⟨i, hi, u, hu, w, hw, pair.trans (congrArg (ZFSet.pair i) tailEq), hxi, fields⟩
  · intro member
    have raw := member
    unfold refinementDataHistoryLevels refinementHistoryAssignmentLevels assignmentIndexLevels relationCompose at raw
    have shape := (ZFSet.mem_sep.1 raw).1
    obtain ⟨assignment, _, xi, _, equal⟩ := ZFSet.mem_prod.1 shape
    rw [equal] at member
    obtain ⟨i, hi, u, hu, w, hw, pair, hxi, fields⟩ :=
      (pair_mem_refinementDataHistoryLevels _ _ _ _ _).1 member
    exact ⟨assignment, xi, equal, i, ZFSet.pair u w, pair, u, w, rfl, hi, hu, hw, hxi, fields⟩

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
