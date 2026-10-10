import OAI.SetTheory.PartitionPrinciple.Definability.FlatLimitConditionFormulas

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def flatLimitConditions (rows I T stages history levels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (FlatLimitConditionCode stages history levels) (M.stageOneCandidateBound rows I T)

theorem mem_flatLimitConditions (rows I T stages history levels z : ZFSet.{u}) :
    z ∈ M.flatLimitConditions rows I T stages history levels ↔
      z ∈ M.stageOneCandidateBound rows I T ∧ FlatLimitConditionCode stages history levels z :=
  ZFSet.mem_sep

theorem pair_mem_flatLimitConditions (rows I T stages history levels row A : ZFSet.{u}) :
    ZFSet.pair row A ∈ M.flatLimitConditions rows I T stages history levels ↔
      row ∈ rows ∧ A ∈ M.sets ∧ A ⊆ stageOneAssignments I T ∧
        M.groundEmbeddable A ZFSet.omega ∧ FlatHistoryCuts stages history levels row A := by
  rw [M.mem_flatLimitConditions, M.pair_mem_stageOneCandidateBound, flatLimitConditionCode_pair]
  constructor
  · rintro ⟨⟨hr, hA, subset, small⟩, valid⟩
    exact ⟨hr, hA, subset, small, valid⟩
  · rintro ⟨hr, hA, subset, small, valid⟩
    exact ⟨⟨hr, hA, subset, small⟩, valid⟩

theorem flatLimitConditions_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {rows I T stages history levels : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hLevels : levels ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.flatLimitConditions rows I T stages history levels ∈ M.sets := by
  have bound := M.stageOneCandidateBound_mem pairing unions powers separation hRows hI hT omega
  let params : Fin 3 → ZFSet.{u} := ![stages, history, levels]
  have ground : ∀ j, params j ∈ M.sets :=
    Fin.cases hStages (Fin.cases hHistory (Fin.cases hLevels (fun j => Fin.elim0 j)))
  let phi : SetFormula 4 := flatLimitConditionFormula 1 2 3 0
  have selected := M.separation_mem separation phi params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets phi (extend z params))
      (M.stageOneCandidateBound rows I T) = M.flatLimitConditions rows I T stages history levels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_flatLimitConditions]
    apply and_congr_right
    intro member
    exact M.realize_flatLimitConditionFormula 1 2 3 0 (extend z params)
      (Fin.cases (M.transitive bound member) ground)
  exact equal ▸ selected

theorem flatLimitConditions_empty {rows I T stages history levels row : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hrow : row ∈ rows)
    (lower : ∀ beta ∈ stages, ∃ Q, ZFSet.pair beta Q ∈ history ∧ ZFSet.pair row ∅ ∈ Q) :
    ZFSet.pair row ∅ ∈ M.flatLimitConditions rows I T stages history levels := by
  apply (M.mem_flatLimitConditions rows I T stages history levels _).2
  refine ⟨M.stageOneCandidateBound_empty hRows hrow, row, ∅, rfl, ?_⟩
  intro beta hbeta
  obtain ⟨Q, entry, member⟩ := lower beta hbeta
  have empty : assignmentCut levels beta ∅ = ∅ := by
    apply ZFSet.ext
    intro z
    simp only [mem_assignmentCut, ZFSet.notMem_empty, false_and]
  exact ⟨Q, entry, empty.symm ▸ member⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
