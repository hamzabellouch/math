import OAI.SetTheory.PartitionPrinciple.Definability.RefinementDataHistoryEntryFormulas
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStructuralRefinementHistories

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

noncomputable def structuralAssignments (G nodes nodeOrder basis T T2 stages history : ZFSet.{u}) : ZFSet.{u} :=
  stageOneAssignments (refinementDataHistoryIndices stages
    (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history)) T

theorem rawStageRefinementAssignmentActionGraph_bound
    (g G nodes nodeOrder nodeAction basis T T2 stages history level P order top action : ZFSet.{u})
    (hl : level ∈ stages) (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history) :
    M.rawStageRefinementAssignmentActionGraph g P order top action G nodes nodeOrder nodeAction basis T T2 level ⊆
      ZFSet.prod (M.structuralAssignments G nodes nodeOrder basis T T2 stages history)
        (M.structuralAssignments G nodes nodeOrder basis T T2 stages history) := by
  let data := M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level
  have packed : ZFSet.pair level (refinementFormulaDataCode data) ∈
      M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history :=
    (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
      ⟨hl, P, order, top, action, stored, rfl⟩
  have includeIndex : data 0 ⊆ refinementDataHistoryIndices stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
    intro i hi
    exact (mem_refinementDataHistoryIndices _ _ _).2 ⟨level, hl, data, packed, hi⟩
  have includeAssignments : stageOneAssignments (data 0) T ⊆
      M.structuralAssignments G nodes nodeOrder basis T T2 stages history := by
    intro x hx
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments _ _ _).1 hx
    exact (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨includeIndex hi, hu, hw⟩
  intro z hz
  unfold rawStageRefinementAssignmentActionGraph rawRefinementAssignmentActionGraph relationProduct at hz
  have bound : z ∈ ZFSet.prod (stageOneAssignments (data 0) T) (stageOneAssignments (data 0) T) :=
    (ZFSet.mem_sep.1 hz).1
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 bound
  exact ZFSet.pair_mem_prod.2 ⟨includeAssignments hx, includeAssignments hy⟩

noncomputable def structuralAssignmentActionGraph
    (G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u}) : ZFSet.{u} :=
  let J := M.structuralAssignments G nodes nodeOrder basis T T2 stages history
  ZFSet.sep (fun z => ∃ g ∈ G, ∃ x y, z = ZFSet.pair (ZFSet.pair g x) y ∧
    ∃ level ∈ stages, ∃ P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
      ZFSet.pair x y ∈ M.rawStageRefinementAssignmentActionGraph g P order top action
        G nodes nodeOrder nodeAction basis T T2 level)
    (ZFSet.prod (ZFSet.prod G J) J)

theorem mem_structuralAssignmentActionGraph
    (G nodes nodeOrder nodeAction basis T T2 stages history z : ZFSet.{u}) :
    z ∈ M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history ↔
      ∃ g ∈ G, ∃ x y, z = ZFSet.pair (ZFSet.pair g x) y ∧
        ∃ level ∈ stages, ∃ P order top action,
          ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
          ZFSet.pair x y ∈ M.rawStageRefinementAssignmentActionGraph g P order top action
            G nodes nodeOrder nodeAction basis T T2 level := by
  rw [structuralAssignmentActionGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨g, hg, x, y, rfl, level, hl, P, order, top, action, stored, edge⟩
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_bound g G nodes nodeOrder nodeAction basis T T2
        stages history level P order top action hl stored edge)
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, bounds.1⟩, bounds.2⟩,
      g, hg, x, y, rfl, level, hl, P, order, top, action, stored, edge⟩

theorem pair_mem_structuralAssignmentActionGraph
    (G nodes nodeOrder nodeAction basis T T2 stages history g x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g x) y ∈
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history ↔
      g ∈ G ∧ ∃ level ∈ stages, ∃ P order top action,
        ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
        ZFSet.pair x y ∈ M.rawStageRefinementAssignmentActionGraph g P order top action
          G nodes nodeOrder nodeAction basis T T2 level := by
  rw [M.mem_structuralAssignmentActionGraph]
  constructor
  · rintro ⟨g', hg, x', y', equal, rest⟩
    obtain ⟨first, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
    exact ⟨hg, rest⟩
  · rintro ⟨hg, rest⟩
    exact ⟨g, hg, x, y, rfl, rest⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
