import OAI.SetTheory.PartitionPrinciple.Forcing.StructuralAssignmentActionGraphs

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

private def witnessBounds : BoundedFormula 20 :=
  let w := prefixIndex 10 10
  let old := suffixIndex 10 10
  .conj (.mem (w 0) (old 1))
    (.conj (BoundedFormula.orderedTripleFormula (old 0) (w 0) (w 1) (w 2))
      (.conj (.mem (w 3) (old 8)) (.conj (.mem (w 9) (old 9))
        (.conj (BoundedFormula.nonemptyTupleFormula 4 (w 9) ![w 3,w 4,w 5,w 6,w 7])
          (BoundedFormula.pairMembershipFormula (w 1) (w 2) (w 8))))))

private def operationSlots : Fin 14 → Fin 20 :=
  let w := prefixIndex 10 10
  let old := suffixIndex 10 10
  extend (w 8) ![w 0,w 4,w 5,w 6,w 7,old 1,old 2,old 3,old 4,old 5,old 6,old 7,w 3]

noncomputable def structuralAssignmentEntryFormula : SetFormula 10 :=
  exBlock 10 (.conj witnessBounds.toFormula
    (SetFormula.reindex operationSlots
      (M.definable_rawStageRefinementAssignmentActionGraph pairing unions powers separation collection).formula))

theorem realize_structuralAssignmentEntryFormula (env : Fin 10 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.structuralAssignmentEntryFormula pairing unions powers separation collection) env ↔
      env 0 ∈ M.structuralAssignmentActionGraph (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) := by
  unfold structuralAssignmentEntryFormula
  rw [realize_exBlock, M.mem_structuralAssignmentActionGraph]
  have meaning (f : Fin 10 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj witnessBounds.toFormula
        (SetFormula.reindex operationSlots
          (M.definable_rawStageRefinementAssignmentActionGraph pairing unions powers separation collection).formula))
          (extendMany 10 f env) ↔
      f 0 ∈ env 1 ∧ env 0 = ZFSet.pair (ZFSet.pair (f 0) (f 1)) (f 2) ∧
        f 3 ∈ env 8 ∧ f 9 ∈ env 9 ∧
        f 9 = ZFSet.pair (f 3) (forcingStageCode (f 4) (f 5) (f 6) (f 7)) ∧
        ZFSet.pair (f 1) (f 2) ∈ f 8 ∧
        f 8 = M.rawStageRefinementAssignmentActionGraph (f 0) (f 4) (f 5) (f 6) (f 7)
          (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) (f 3) := by
    change (Realize M.sets witnessBounds.toFormula _ ∧ _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 10 f env ground members)]
    simp only [witnessBounds, BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_nonemptyTupleFormula, BoundedFormula.truth_pairMembershipFormula,
      extendMany_prefix, extendMany_suffix]
    rw [realize_reindex]
    have args : (fun j => extendMany 10 f env (operationSlots j)) =
        extend (f 8) ![f 0,f 4,f 5,f 6,f 7,env 1,env 2,env 3,env 4,env 5,env 6,env 7,f 3] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))))))))) j
    have argGround : ∀ j, (![f 0,f 4,f 5,f 6,f 7,env 1,env 2,env 3,env 4,env 5,env 6,env 7,f 3] : Fin 13 → ZFSet.{u}) j ∈ M.sets :=
      (Fin.cases (ground 0) (Fin.cases (ground 4) (Fin.cases (ground 5) (Fin.cases (ground 6) (Fin.cases (ground 7) (Fin.cases (members 1) (Fin.cases (members 2) (Fin.cases (members 3) (Fin.cases (members 4) (Fin.cases (members 5) (Fin.cases (members 6) (Fin.cases (members 7) (Fin.cases (ground 3) (fun j => Fin.elim0 j))))))))))))))
    rw [args, (M.definable_rawStageRefinementAssignmentActionGraph pairing unions powers separation collection).correct _ argGround _ (ground 8)]
    change ((_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ∧ _) ↔ _
    tauto
  constructor
  · rintro ⟨f, ground, holds⟩
    obtain ⟨hg, equal, hl, source, shape, edge, graph⟩ := (meaning f ground).1 holds
    exact ⟨f 0, hg, f 1, f 2, equal, f 3, hl, f 4, f 5, f 6, f 7, shape ▸ source, graph ▸ edge⟩
  · rintro ⟨g, hg, x, y, equal, level, hl, P, order, top, action, stored, edge⟩
    let source := ZFSet.pair level (forcingStageCode P order top action)
    let graph := M.rawStageRefinementAssignmentActionGraph g P order top action
      (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) level
    have hSource := M.transitive (members 9) stored
    have fields := M.nonemptyTupleCode_field_mem 4 ![level,P,order,top,action] hSource
    have hOuter : ZFSet.pair (ZFSet.pair g x) y ∈ M.sets := equal ▸ members 0
    have outer := M.nonemptyTupleCode_field_mem 1 ![ZFSet.pair g x,y] hOuter
    have inner := M.nonemptyTupleCode_field_mem 1 ![g,x] (outer 0)
    have hGraph : graph ∈ M.sets :=
      (M.definable_rawStageRefinementAssignmentActionGraph pairing unions powers separation collection).closed
        ![g,P,order,top,action,env 1,env 2,env 3,env 4,env 5,env 6,env 7,level]
        (Fin.cases (inner 0) (Fin.cases (fields 1) (Fin.cases (fields 2) (Fin.cases (fields 3)
          (Fin.cases (fields 4) (Fin.cases (members 1) (Fin.cases (members 2) (Fin.cases (members 3)
            (Fin.cases (members 4) (Fin.cases (members 5) (Fin.cases (members 6)
              (Fin.cases (members 7) (Fin.cases (fields 0) (fun j => Fin.elim0 j))))))))))))))
    let f : Fin 10 → ZFSet.{u} := ![g,x,y,level,P,order,top,action,graph,source]
    have ground : ∀ j, f j ∈ M.sets :=
      Fin.cases (inner 0) (Fin.cases (inner 1) (Fin.cases (outer 1) (Fin.cases (fields 0)
        (Fin.cases (fields 1) (Fin.cases (fields 2) (Fin.cases (fields 3)
          (Fin.cases (fields 4) (Fin.cases hGraph (Fin.cases hSource (fun j => Fin.elim0 j))))))))))
    exact ⟨f, ground, (meaning f ground).2 ⟨hg, equal, hl, stored, rfl, edge, rfl⟩⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
