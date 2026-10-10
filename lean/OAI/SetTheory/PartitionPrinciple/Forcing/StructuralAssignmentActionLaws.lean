import OAI.SetTheory.PartitionPrinciple.Geometry.StructuralPreparationSourceImages

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {H : Type u} [Group H]

theorem structuralAssignment_relationLaws (t : Presentation H)
    (nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u})
    (function : FunctionGraphOn stages history)
    (branches : ∀ level ∈ stages, ∀ P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      RelationActionLaws H
        (stageOneAssignments (M.rawRefinementFormulaData P order top action
          t.carrier nodes nodeOrder basis T T2 level 0) T)
        (fun g => M.rawStageRefinementAssignmentActionGraph (t.encode g) P order top action
          t.carrier nodes nodeOrder nodeAction basis T T2 level)) :
    RelationActionLaws H
      (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)
      (fun g => rawActionSection (t.encode g)
        (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history)
        (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)) := by
  let ι := {v : Fin 5 → ZFSet.{u} // v 0 ∈ stages ∧
    ZFSet.pair (v 0) (forcingStageCode (v 1) (v 2) (v 3) (v 4)) ∈ history}
  let X (i : ι) := stageOneAssignments (M.rawRefinementFormulaData (i.val 1) (i.val 2)
    (i.val 3) (i.val 4) t.carrier nodes nodeOrder basis T T2 (i.val 0) 0) T
  let branch (i : ι) (g : H) := M.rawStageRefinementAssignmentActionGraph (t.encode g)
    (i.val 1) (i.val 2) (i.val 3) (i.val 4)
    t.carrier nodes nodeOrder nodeAction basis T T2 (i.val 0)
  let J := M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history
  let graph := M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history
  have cover (x : ZFSet.{u}) : x ∈ J ↔ ∃ i : ι, x ∈ X i := by
    rw [M.mem_structuralAssignments]
    constructor
    · rintro ⟨level, hl, P, order, top, action, stored, member⟩
      exact ⟨⟨![level, P, order, top, action], hl, stored⟩, member⟩
    · rintro ⟨i, member⟩
      exact ⟨i.val 0, i.property.1, i.val 1, i.val 2, i.val 3, i.val 4, i.property.2, member⟩
  apply RelationActionLaws.of_disjoint_family X branch J (fun g => rawActionSection (t.encode g) graph J) cover
  · intro g z
    constructor
    · intro member
      obtain ⟨x, _hx, y, _hy, rfl, edge⟩ :=
        (BoundedFormula.truth_actionSectionEntryFormula 0 1 2 3 _).1
          ((mem_rawActionSection (t.encode g) graph J z).1 member)
      obtain ⟨_hg, level, hl, P, order, top, action, stored, entry⟩ :=
        (M.pair_mem_structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) x y).1 edge
      exact ⟨⟨![level, P, order, top, action], hl, stored⟩, entry⟩
    · rintro ⟨i, member⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1
        (M.rawStageRefinementAssignmentActionGraph_branch_bound (t.encode g)
          (i.val 1) (i.val 2) (i.val 3) (i.val 4) t.carrier nodes nodeOrder nodeAction basis T T2 (i.val 0) member)
      exact (pair_mem_rawActionSection _ _ _ _ _).2
        ⟨(cover x).2 ⟨i, hx⟩, (cover y).2 ⟨i, hy⟩,
          (M.pair_mem_structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) x y).2
            ⟨t.encode_mem g, i.val 0, i.property.1, i.val 1, i.val 2, i.val 3, i.val 4, i.property.2, member⟩⟩
  · intro i j x hi hj
    have equal := M.structuralAssignment_branch_unique t.carrier nodes nodeOrder basis T T2
      function i.property.2 j.property.2 hi hj
    apply Subtype.ext
    exact funext (Fin.cases equal.1 (Fin.cases equal.2.1 (Fin.cases equal.2.2.1
      (Fin.cases equal.2.2.2.1 (Fin.cases equal.2.2.2.2 (fun k => Fin.elim0 k))))))
  · intro i
    exact branches (i.val 0) i.property.1 (i.val 1) (i.val 2) (i.val 3) (i.val 4) i.property.2

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
