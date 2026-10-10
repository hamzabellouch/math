import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStructuralForcingActionGraphs

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem rawStageRefinementAssignmentActionGraph_branch_bound
    (g P order top action G nodes nodeOrder nodeAction basis T T2 level : ZFSet.{u}) :
    M.rawStageRefinementAssignmentActionGraph g P order top action G nodes nodeOrder nodeAction basis T T2 level ⊆
      ZFSet.prod
        (stageOneAssignments (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T)
        (stageOneAssignments (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T) := by
  intro z member
  unfold rawStageRefinementAssignmentActionGraph rawRefinementAssignmentActionGraph relationProduct at member
  exact (ZFSet.mem_sep.1 member).1

variable (G nodes nodeOrder basis T T2 : ZFSet.{u})

theorem mem_structuralAssignments (stages history x : ZFSet.{u}) :
    x ∈ M.structuralAssignments G nodes nodeOrder basis T T2 stages history ↔
      ∃ level ∈ stages, ∃ P order top action,
        ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
        x ∈ stageOneAssignments
          (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T := by
  rw [structuralAssignments, mem_stageOneAssignments]
  constructor
  · rintro ⟨i, hi, u, hu, w, hw, rfl⟩
    obtain ⟨level, hl, data, entry, member⟩ := (mem_refinementDataHistoryIndices _ _ _).1 hi
    obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
      M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
    exact ⟨level, hl, P, order, top, action, stored,
      (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨member, hu, hw⟩⟩
  · rintro ⟨level, hl, P, order, top, action, stored, member⟩
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments _ _ _).1 member
    refine ⟨i, ?_, u, hu, w, hw, rfl⟩
    exact (mem_refinementDataHistoryIndices _ _ _).2
      ⟨level, hl, M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level,
        (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
          ⟨hl, P, order, top, action, stored, rfl⟩, hi⟩

theorem structuralAssignment_branch_unique {stages history level other P order top action
    P' order' top' action' x : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
    (stored' : ZFSet.pair other (forcingStageCode P' order' top' action') ∈ history)
    (member : x ∈ stageOneAssignments
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T)
    (member' : x ∈ stageOneAssignments
      (M.rawRefinementFormulaData P' order' top' action' G nodes nodeOrder basis T T2 other 0) T) :
    level = other ∧ P = P' ∧ order = order' ∧ top = top' ∧ action = action' := by
  obtain ⟨i, hi, u, _hu, w, _hw, rfl⟩ := (mem_stageOneAssignments _ _ _).1 member
  have hi' := ((stageOneAssignment_mem_assignments _ _ _ _ _).1 member').1
  obtain ⟨v, eqv, hv⟩ := M.rawRefinementFormulaData_level P order top action G nodes nodeOrder basis T T2 level i hi
  obtain ⟨v', eqv', hv'⟩ := M.rawRefinementFormulaData_level P' order' top' action' G nodes nodeOrder basis T T2 other i hi'
  have fields := nonemptyTupleCode_injective 5 (eqv.symm.trans eqv')
  have equal : level = other := hv.symm.trans ((congrFun fields 0).trans hv')
  rw [← equal] at stored'
  exact ⟨equal, (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 (function.unique stored stored')⟩

theorem structuralAssignmentActionGraph_branch_entry
    (nodeAction : ZFSet.{u}) {stages history level P order top action x : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
    (member : x ∈ stageOneAssignments
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T)
    (g y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g x) y ∈
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history ↔
        g ∈ G ∧ ZFSet.pair x y ∈ M.rawStageRefinementAssignmentActionGraph g P order top action
          G nodes nodeOrder nodeAction basis T T2 level := by
  rw [M.pair_mem_structuralAssignmentActionGraph]
  constructor
  · rintro ⟨hg, other, _ho, P', order', top', action', stored', edge⟩
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_branch_bound g P' order' top' action'
        G nodes nodeOrder nodeAction basis T T2 other edge)
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
      M.structuralAssignment_branch_unique G nodes nodeOrder basis T T2 function stored stored' member bounds.1
    exact ⟨hg, edge⟩
  · rintro ⟨hg, edge⟩
    exact ⟨hg, level, function.pair_source stored, P, order, top, action, stored, edge⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u})
local notation "J" => M.structuralAssignments G nodes nodeOrder basis T T2 stages history
local notation "graph" => M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history

noncomputable def structuralAssignmentImage (g A : ZFSet.{u}) : ZFSet.{u} :=
  relationImage A J (rawActionSection g graph J)

theorem structuralAssignmentImage_subset (g A : ZFSet.{u}) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A ⊆ J :=
  fun y hy => ((mem_relationImage A J (rawActionSection g graph J) y).1 hy).1

theorem structuralAssignmentImage_mono (g : ZFSet.{u}) {A B : ZFSet.{u}} (subset : A ⊆ B) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A ⊆
      M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g B := by
  intro y hy
  obtain ⟨hy, x, hx, edge⟩ := (mem_relationImage A J (rawActionSection g graph J) y).1 hy
  exact (mem_relationImage B J (rawActionSection g graph J) y).2 ⟨hy, x, subset hx, edge⟩

variable {H : Type u} [Group H] (t : Presentation H)
variable (laws : RelationActionLaws H
  (M.structuralAssignments G nodes nodeOrder basis T T2 stages history)
  (fun g => rawActionSection (t.encode g)
    (M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history)
    (M.structuralAssignments G nodes nodeOrder basis T T2 stages history)))

include laws in
theorem structuralAssignmentImage_one {A : ZFSet.{u}} (subset : A ⊆ J) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history (t.encode 1) A = A :=
  laws.image_one subset

include laws in
theorem structuralAssignmentImage_mul (g h : H) {A : ZFSet.{u}} (subset : A ⊆ J) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history (t.encode (g * h)) A =
      M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history (t.encode g)
        (M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history (t.encode h) A) :=
  laws.image_mul g h subset

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder basis T T2 : ZFSet.{u})

theorem structuralAssignmentLevels_entry (stages history x level : ZFSet.{u}) :
    ZFSet.pair x level ∈ refinementDataHistoryLevels stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T ↔
      level ∈ stages ∧ ∃ P order top action,
        ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
        x ∈ stageOneAssignments
          (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T := by
  rw [pair_mem_refinementDataHistoryLevels]
  constructor
  · rintro ⟨i, hi, u, hu, w, hw, rfl, hl, fields, eqFields, levelEq⟩
    obtain ⟨other, _ho, data, entry, member⟩ := (mem_refinementDataHistoryIndices _ _ _).1 hi
    obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
      M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
    obtain ⟨v, eqv, hv⟩ :=
      M.rawRefinementFormulaData_level P order top action G nodes nodeOrder basis T T2 other i member
    have tupleEq := nonemptyTupleCode_injective 5 (eqFields.symm.trans eqv)
    have same : level = other := levelEq.trans ((congrFun tupleEq 0).trans hv)
    cases same
    exact ⟨hl, P, order, top, action, stored,
      (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨member, hu, hw⟩⟩
  · rintro ⟨hl, P, order, top, action, stored, member⟩
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments _ _ _).1 member
    obtain ⟨v, eqv, hv⟩ :=
      M.rawRefinementFormulaData_level P order top action G nodes nodeOrder basis T T2 level i hi
    refine ⟨i, ?_, u, hu, w, hw, rfl, hl, v, eqv, hv.symm⟩
    exact (mem_refinementDataHistoryIndices _ _ _).2
      ⟨level, hl, M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level,
        (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
          ⟨hl, P, order, top, action, stored, rfl⟩, hi⟩

theorem structuralAssignments_cut_eq {stages earlier : ZFSet.{u}}
    (subset : earlier ⊆ stages) (history A : ZFSet.{u}) :
    assignmentCut (refinementDataHistoryLevels stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T) earlier A =
        ZFSet.sep (fun x => x ∈ M.structuralAssignments G nodes nodeOrder basis T T2 earlier history) A := by
  apply ZFSet.ext
  intro x
  rw [mem_assignmentCut, ZFSet.mem_sep, M.mem_structuralAssignments]
  constructor
  · rintro ⟨member, level, hl, edge⟩
    obtain ⟨_, P, order, top, action, stored, branch⟩ :=
      (M.structuralAssignmentLevels_entry G nodes nodeOrder basis T T2 stages history x level).1 edge
    exact ⟨member, level, hl, P, order, top, action, stored, branch⟩
  · rintro ⟨member, level, hl, P, order, top, action, stored, branch⟩
    exact ⟨member, level, hl,
      (M.structuralAssignmentLevels_entry G nodes nodeOrder basis T T2 stages history x level).2
        ⟨subset hl, P, order, top, action, stored, branch⟩⟩

theorem structuralAssignments_mono {stages earlier : ZFSet.{u}}
    (subset : earlier ⊆ stages) (history : ZFSet.{u}) :
    M.structuralAssignments G nodes nodeOrder basis T T2 earlier history ⊆
      M.structuralAssignments G nodes nodeOrder basis T T2 stages history := by
  intro x member
  obtain ⟨level, hl, rest⟩ := (M.mem_structuralAssignments G nodes nodeOrder basis T T2 earlier history x).1 member
  exact (M.mem_structuralAssignments G nodes nodeOrder basis T T2 stages history x).2 ⟨level, subset hl, rest⟩

theorem structuralAssignments_history_restrict (stages history : ZFSet.{u}) :
    M.structuralAssignments G nodes nodeOrder basis T T2 stages (graphRestriction stages history) =
      M.structuralAssignments G nodes nodeOrder basis T T2 stages history := by
  apply ZFSet.ext
  intro x
  rw [M.mem_structuralAssignments, M.mem_structuralAssignments]
  constructor
  · rintro ⟨level, hl, P, order, top, action, stored, member⟩
    exact ⟨level, hl, P, order, top, action, (pair_mem_graphRestriction.1 stored).1, member⟩
  · rintro ⟨level, hl, P, order, top, action, stored, member⟩
    exact ⟨level, hl, P, order, top, action, pair_mem_graphRestriction.2 ⟨stored, hl⟩, member⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable {G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u}}
variable (hG : G ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
variable (hna : nodeAction ∈ M.sets) (hb : basis ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
local notation "J" => M.structuralAssignments G nodes nodeOrder basis T T2 stages history
local notation "graph" => M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history

include pairing unions powers separation collection hG hn hno hna hb hT hT2 hs hh in
theorem structuralAssignmentSection_mem {g : ZFSet.{u}} (hg : g ∈ M.sets) :
    rawActionSection g graph J ∈ M.sets := by
  have hJ := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![G,nodes,nodeOrder,basis,T,T2,stages,history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb (Fin.cases hT
      (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hF := M.structuralAssignmentActionGraph_mem pairing unions powers separation collection
    hG hn hno hna hb hT hT2 hs hh
  exact (M.definable_rawActionSection pairing unions powers separation).closed ![g,graph,J]
    (Fin.cases hg (Fin.cases hF (Fin.cases hJ (fun j => Fin.elim0 j))))

include pairing unions powers separation collection hG hn hno hna hb hT hT2 hs hh in
theorem structuralAssignmentImage_mem {g A : ZFSet.{u}} (hg : g ∈ M.sets) (hA : A ∈ M.sets) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A ∈ M.sets := by
  have hJ := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![G,nodes,nodeOrder,basis,T,T2,stages,history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb (Fin.cases hT
      (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  exact M.relationImage_mem separation hA hJ
    (M.structuralAssignmentSection_mem pairing unions powers separation collection
      hG hn hno hna hb hT hT2 hs hh hg)

include pairing unions powers separation collection hG hn hno hna hb hT hT2 hs hh in
theorem structuralAssignmentImage_small (omega : ZFSet.omega ∈ M.sets)
    {g A : ZFSet.{u}} (hg : g ∈ M.sets)
    (injection : InjectionCode J J (rawActionSection g graph J))
    (member : A ∈ M.groundSmallSubsets J ZFSet.omega) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A ∈
      M.groundSmallSubsets J ZFSet.omega := by
  obtain ⟨hA, subset, small⟩ := (M.mem_groundSmallSubsets J ZFSet.omega A).1 member
  have hJ := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![G,nodes,nodeOrder,basis,T,T2,stages,history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb (Fin.cases hT
      (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hF := M.structuralAssignmentSection_mem pairing unions powers separation collection
    hG hn hno hna hb hT hT2 hs hh hg
  exact (M.mem_groundSmallSubsets J ZFSet.omega _).2
    ⟨M.relationImage_mem separation hA hJ hF,
      M.structuralAssignmentImage_subset G nodes nodeOrder nodeAction basis T T2 stages history g A,
      M.groundEmbeddable_image pairing unions powers separation hA hJ omega hF injection subset small⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})

theorem structuralAssignmentActionGraph_history_restrict (stages history : ZFSet.{u}) :
    M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages (graphRestriction stages history) =
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history := by
  apply ZFSet.ext
  intro z
  rw [M.mem_structuralAssignmentActionGraph, M.mem_structuralAssignmentActionGraph]
  constructor
  · rintro ⟨g, hg, x, y, equal, level, hl, P, order, top, action, stored, edge⟩
    exact ⟨g, hg, x, y, equal, level, hl, P, order, top, action,
      (pair_mem_graphRestriction.1 stored).1, edge⟩
  · rintro ⟨g, hg, x, y, equal, level, hl, P, order, top, action, stored, edge⟩
    exact ⟨g, hg, x, y, equal, level, hl, P, order, top, action,
      pair_mem_graphRestriction.2 ⟨stored, hl⟩, edge⟩

theorem structuralAssignmentActionGraph_prefix_entry {stages earlier history : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (subset : earlier ⊆ stages) (g x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g x) y ∈
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 earlier history ↔
      ZFSet.pair (ZFSet.pair g x) y ∈
        M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history ∧
      x ∈ M.structuralAssignments G nodes nodeOrder basis T T2 earlier history := by
  constructor
  · intro edge
    obtain ⟨hg, level, hl, P, order, top, action, stored, branch⟩ :=
      (M.pair_mem_structuralAssignmentActionGraph _ _ _ _ _ _ _ _ _ _ _ _).1 edge
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_branch_bound g P order top action
        G nodes nodeOrder nodeAction basis T T2 level branch)
    exact ⟨(M.pair_mem_structuralAssignmentActionGraph _ _ _ _ _ _ _ _ _ _ _ _).2
      ⟨hg, level, subset hl, P, order, top, action, stored, branch⟩,
      (M.mem_structuralAssignments G nodes nodeOrder basis T T2 earlier history x).2
        ⟨level, hl, P, order, top, action, stored, bounds.1⟩⟩
  · rintro ⟨edge, source⟩
    obtain ⟨hg, level, _hl, P, order, top, action, stored, branch⟩ :=
      (M.pair_mem_structuralAssignmentActionGraph _ _ _ _ _ _ _ _ _ _ _ _).1 edge
    obtain ⟨other, ho, P', order', top', action', stored', member⟩ :=
      (M.mem_structuralAssignments G nodes nodeOrder basis T T2 earlier history x).1 source
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_branch_bound g P order top action
        G nodes nodeOrder nodeAction basis T T2 level branch)
    obtain ⟨same, _⟩ := M.structuralAssignment_branch_unique G nodes nodeOrder basis T T2
      function stored stored' bounds.1 member
    exact (M.pair_mem_structuralAssignmentActionGraph _ _ _ _ _ _ _ _ _ _ _ _).2
      ⟨hg, level, same.symm ▸ ho, P, order, top, action, stored, branch⟩

theorem structuralAssignmentActionGraph_domain_restrict {stages earlier history : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (subset : earlier ⊆ stages) :
    M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 earlier history =
      graphRestriction (ZFSet.prod G (M.structuralAssignments G nodes nodeOrder basis T T2 earlier history))
        (M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro edge
    obtain ⟨g, hg, x, y, rfl, _⟩ := (M.mem_structuralAssignmentActionGraph _ _ _ _ _ _ _ _ _ _).1 edge
    obtain ⟨whole, source⟩ :=
      (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2 function subset g x y).1 edge
    exact pair_mem_graphRestriction.2 ⟨whole, ZFSet.pair_mem_prod.2 ⟨hg, source⟩⟩
  · intro member
    obtain ⟨source, hs, y, rfl, edge⟩ := mem_graphRestriction.1 member
    obtain ⟨g, _hg, x, hx, rfl⟩ := ZFSet.mem_prod.1 hs
    exact (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2 function subset g x y).2
      ⟨edge, hx⟩

theorem structuralAssignmentSection_entry (stages history g x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ rawActionSection g
      (M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history)
      (M.structuralAssignments G nodes nodeOrder basis T T2 stages history) ↔
      ZFSet.pair (ZFSet.pair g x) y ∈
        M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history := by
  rw [pair_mem_rawActionSection]
  constructor
  · exact fun member => member.2.2
  · intro edge
    obtain ⟨_hg, level, hl, P, order, top, action, stored, branch⟩ :=
      (M.pair_mem_structuralAssignmentActionGraph _ _ _ _ _ _ _ _ _ _ _ _).1 edge
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_bound g G nodes nodeOrder nodeAction basis T T2
        stages history level P order top action hl stored branch)
    exact ⟨bounds.1, bounds.2, edge⟩

theorem structuralAssignmentSection_domain_restrict {stages earlier history : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (subset : earlier ⊆ stages) (g : ZFSet.{u}) :
    rawActionSection g
      (M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 earlier history)
      (M.structuralAssignments G nodes nodeOrder basis T T2 earlier history) =
      graphRestriction (M.structuralAssignments G nodes nodeOrder basis T T2 earlier history)
        (rawActionSection g
          (M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history)
          (M.structuralAssignments G nodes nodeOrder basis T T2 stages history)) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨x, _hx, y, _hy, rfl⟩ := ZFSet.mem_prod.1 ((ZFSet.mem_sep.1 member).1)
    have edge := (M.structuralAssignmentSection_entry G nodes nodeOrder nodeAction basis T T2 earlier history g x y).1 member
    obtain ⟨whole, source⟩ :=
      (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2 function subset g x y).1 edge
    exact pair_mem_graphRestriction.2
      ⟨(M.structuralAssignmentSection_entry G nodes nodeOrder nodeAction basis T T2 stages history g x y).2 whole, source⟩
  · intro member
    obtain ⟨x, hx, y, rfl, edge⟩ := mem_graphRestriction.1 member
    apply (M.structuralAssignmentSection_entry G nodes nodeOrder nodeAction basis T T2 earlier history g x y).2
    apply (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2 function subset g x y).2
    exact ⟨(M.structuralAssignmentSection_entry G nodes nodeOrder nodeAction basis T T2 stages history g x y).1 edge, hx⟩

theorem structuralAssignmentActionGraph_earlier_iff {stages history g x y : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (earlier : ZFSet.{u})
    (edge : ZFSet.pair (ZFSet.pair g x) y ∈
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history) :
    x ∈ M.structuralAssignments G nodes nodeOrder basis T T2 earlier history ↔
      y ∈ M.structuralAssignments G nodes nodeOrder basis T T2 earlier history := by
  obtain ⟨_hg, level, _hl, P, order, top, action, stored, branch⟩ :=
    (M.pair_mem_structuralAssignmentActionGraph _ _ _ _ _ _ _ _ _ _ _ _).1 edge
  have bounds := ZFSet.pair_mem_prod.1
    (M.rawStageRefinementAssignmentActionGraph_branch_bound g P order top action
      G nodes nodeOrder nodeAction basis T T2 level branch)
  constructor
  · intro member
    obtain ⟨other, ho, P', order', top', action', stored', source⟩ :=
      (M.mem_structuralAssignments G nodes nodeOrder basis T T2 earlier history x).1 member
    have same := (M.structuralAssignment_branch_unique G nodes nodeOrder basis T T2
      function stored stored' bounds.1 source).1
    exact (M.mem_structuralAssignments G nodes nodeOrder basis T T2 earlier history y).2
      ⟨level, same.symm ▸ ho, P, order, top, action, stored, bounds.2⟩
  · intro member
    obtain ⟨other, ho, P', order', top', action', stored', target⟩ :=
      (M.mem_structuralAssignments G nodes nodeOrder basis T T2 earlier history y).1 member
    have same := (M.structuralAssignment_branch_unique G nodes nodeOrder basis T T2
      function stored stored' bounds.2 target).1
    exact (M.mem_structuralAssignments G nodes nodeOrder basis T T2 earlier history x).2
      ⟨level, same.symm ▸ ho, P, order, top, action, stored, bounds.1⟩





theorem structuralAssignmentImage_entry (stages history g A y : ZFSet.{u}) :
    y ∈ M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A ↔
      ∃ x ∈ A, ZFSet.pair (ZFSet.pair g x) y ∈
        M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history := by
  rw [structuralAssignmentImage, mem_relationImage]
  constructor
  · rintro ⟨_, x, hx, edge⟩
    exact ⟨x, hx, (M.structuralAssignmentSection_entry G nodes nodeOrder nodeAction basis T T2 stages history g x y).1 edge⟩
  · rintro ⟨x, hx, edge⟩
    have sectionEdge := (M.structuralAssignmentSection_entry G nodes nodeOrder nodeAction basis T T2 stages history g x y).2 edge
    exact ⟨((pair_mem_rawActionSection _ _ _ _ _).1 sectionEdge).2.1, x, hx, sectionEdge⟩

theorem structuralAssignmentImage_history_restrict (stages history g A : ZFSet.{u}) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages (graphRestriction stages history) g A =
      M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A := by
  unfold structuralAssignmentImage
  rw [M.structuralAssignments_history_restrict, M.structuralAssignmentActionGraph_history_restrict]

theorem structuralAssignmentImage_branch {stages history level P order top action g A : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (actor : g ∈ G)
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
    (subset : A ⊆ stageOneAssignments
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A =
      relationImage A
        (stageOneAssignments (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T)
        (M.rawStageRefinementAssignmentActionGraph g P order top action G nodes nodeOrder nodeAction basis T T2 level) := by
  apply ZFSet.ext
  intro y
  rw [M.structuralAssignmentImage_entry, mem_relationImage]
  constructor
  · rintro ⟨x, hx, edge⟩
    have branch := (M.structuralAssignmentActionGraph_branch_entry G nodes nodeOrder basis T T2
      nodeAction function stored (subset hx) g y).1 edge |>.2
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_branch_bound g P order top action
        G nodes nodeOrder nodeAction basis T T2 level branch)
    exact ⟨bounds.2, x, hx, branch⟩
  · rintro ⟨_, x, hx, branch⟩
    exact ⟨x, hx, (M.structuralAssignmentActionGraph_branch_entry G nodes nodeOrder basis T T2
      nodeAction function stored (subset hx) g y).2 ⟨actor, branch⟩⟩

theorem structuralAssignmentImage_domain_restrict {stages earlier history : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (subset : earlier ⊆ stages) (g A : ZFSet.{u}) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 earlier history g A =
      M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g
        (ZFSet.sep (fun x => x ∈ M.structuralAssignments G nodes nodeOrder basis T T2 earlier history) A) := by
  apply ZFSet.ext
  intro y
  rw [M.structuralAssignmentImage_entry, M.structuralAssignmentImage_entry]
  constructor
  · rintro ⟨x, hx, edge⟩
    obtain ⟨whole, source⟩ :=
      (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2 function subset g x y).1 edge
    exact ⟨x, ZFSet.mem_sep.2 ⟨hx, source⟩, whole⟩
  · rintro ⟨x, hx, edge⟩
    obtain ⟨member, source⟩ := ZFSet.mem_sep.1 hx
    exact ⟨x, member,
      (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2 function subset g x y).2
        ⟨edge, source⟩⟩

theorem structuralAssignmentImage_cut {stages earlier history : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (subset : earlier ⊆ stages) (g A : ZFSet.{u}) :
    assignmentCut (refinementDataHistoryLevels stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T) earlier
      (M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A) =
      M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 earlier history g
        (assignmentCut (refinementDataHistoryLevels stages
          (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T) earlier A) := by
  rw [M.structuralAssignments_cut_eq G nodes nodeOrder basis T T2 subset,
    M.structuralAssignments_cut_eq G nodes nodeOrder basis T T2 subset]
  apply ZFSet.ext
  intro y
  rw [ZFSet.mem_sep, M.structuralAssignmentImage_entry, M.structuralAssignmentImage_entry]
  constructor
  · rintro ⟨⟨x, hx, edge⟩, target⟩
    have source := (M.structuralAssignmentActionGraph_earlier_iff G nodes nodeOrder nodeAction basis T T2
      function earlier edge).2 target
    exact ⟨x, ZFSet.mem_sep.2 ⟨hx, source⟩,
      (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2 function subset g x y).2
        ⟨edge, source⟩⟩
  · rintro ⟨x, hx, edge⟩
    obtain ⟨member, source⟩ := ZFSet.mem_sep.1 hx
    have whole := (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2
      function subset g x y).1 edge |>.1
    exact ⟨⟨x, member, whole⟩,
      (M.structuralAssignmentActionGraph_earlier_iff G nodes nodeOrder nodeAction basis T T2
        function earlier whole).1 source⟩

theorem structuralAssignmentImage_prefix_cut {stages earlier history : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (subset : earlier ⊆ stages) (g A : ZFSet.{u}) :
    assignmentCut (refinementDataHistoryLevels stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T) earlier
      (M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A) =
      M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 earlier (graphRestriction earlier history) g
        (assignmentCut (refinementDataHistoryLevels stages
          (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T) earlier A) := by
  rw [M.structuralAssignmentImage_history_restrict]
  exact M.structuralAssignmentImage_cut G nodes nodeOrder nodeAction basis T T2 function subset g A

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
variable {stages history level P order top action : ZFSet.{u}}
variable (function : FunctionGraphOn stages history)
variable (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
include function stored

theorem structuralAssignmentActionGraph_branch_iff {g x y : ZFSet.{u}}
    (edge : ZFSet.pair (ZFSet.pair g x) y ∈
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history) :
    x ∈ stageOneAssignments
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T ↔
    y ∈ stageOneAssignments
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T := by
  constructor
  · intro member
    have branch := (M.structuralAssignmentActionGraph_branch_entry G nodes nodeOrder basis T T2
      nodeAction function stored member g y).1 edge |>.2
    exact (ZFSet.pair_mem_prod.1 (M.rawStageRefinementAssignmentActionGraph_branch_bound
      g P order top action G nodes nodeOrder nodeAction basis T T2 level branch)).2
  · intro member
    obtain ⟨_, other, _, P', order', top', action', stored', branch⟩ :=
      (M.pair_mem_structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2
        stages history g x y).1 edge
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_branch_bound g P' order' top' action'
        G nodes nodeOrder nodeAction basis T T2 other branch)
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := M.structuralAssignment_branch_unique
      G nodes nodeOrder basis T T2 function stored stored' member bounds.2
    exact bounds.1

theorem structuralAssignmentImage_select_branch (g A : ZFSet.{u}) :
    let I := M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0
    assignmentOnIndices I T
      (M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A) =
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g
      (assignmentOnIndices I T A) := by
  dsimp only
  apply ZFSet.ext
  intro y
  rw [mem_assignmentOnIndices, M.structuralAssignmentImage_entry, M.structuralAssignmentImage_entry]
  constructor
  · rintro ⟨⟨x, hx, edge⟩, hy⟩
    exact ⟨x, (mem_assignmentOnIndices _ _ _ _).2 ⟨hx,
      (M.structuralAssignmentActionGraph_branch_iff G nodes nodeOrder nodeAction basis T T2
        function stored edge).2 hy⟩, edge⟩
  · rintro ⟨x, hx, edge⟩
    obtain ⟨member, branch⟩ := (mem_assignmentOnIndices _ _ _ _).1 hx
    exact ⟨⟨x, member, edge⟩,
      (M.structuralAssignmentActionGraph_branch_iff G nodes nodeOrder nodeAction basis T T2
        function stored edge).1 branch⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
variable {stages history level P order top action g : ZFSet.{u}}
variable (function : FunctionGraphOn stages history) (actor : g ∈ G)
variable (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
local notation "d" => M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level
local notation "J" => stageOneAssignments (d 0) T
local notation "branch" => M.rawStageRefinementAssignmentActionGraph g P order top action
  G nodes nodeOrder nodeAction basis T T2 level
local notation "image" => M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g

include function actor stored in
theorem structuralAssignmentImage_target_branch_iff {A y : ZFSet.{u}} (target : y ∈ J) :
    y ∈ image A ↔ y ∈ relationImage A J branch := by
  rw [M.structuralAssignmentImage_entry, mem_relationImage]
  constructor
  · rintro ⟨x, hx, edge⟩
    obtain ⟨_hg, other, _ho, P', order', top', action', stored', entry⟩ :=
      (M.pair_mem_structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2
        stages history g x y).1 edge
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_branch_bound g P' order' top' action'
        G nodes nodeOrder nodeAction basis T T2 other entry)
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
      M.structuralAssignment_branch_unique G nodes nodeOrder basis T T2
        function stored stored' target bounds.2
    exact ⟨target, x, hx, entry⟩
  · rintro ⟨_, x, hx, entry⟩
    exact ⟨x, hx, (M.pair_mem_structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2
      stages history g x y).2
        ⟨actor, level, function.pair_source stored, P, order, top, action, stored, entry⟩⟩

include function actor stored in
theorem structuralAssignmentImage_rawTests_branch_iff (A lower : ZFSet.{u}) :
    stageOneRawTests M d (image A) lower ↔
      stageOneRawTests M d (relationImage A J branch) lower := by
  apply stageOneRawTests_congr
  intro i hi u hu w hw
  change u ∈ T at hu
  change w ∈ T at hw
  exact M.structuralAssignmentImage_target_branch_iff G nodes nodeOrder nodeAction basis T T2
    function actor stored ((stageOneAssignment_mem_assignments (d 0) T i u w).2 ⟨hi, hu, hw⟩)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (level T T2 : ZFSet.{u})
variable (system : RefinementStageSystem M a s t b d base directed level T T2)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
include system pairing unions powers separation collection carrier order group nodes supports hLevel hT

theorem structuralAssignmentImage_decode
    {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
      (a.actionGraph s t)) ∈ history)
    (h : G) (A sharedIdx rawU rawW : ZFSet.{u})
    (index : sharedIdx ∈ M.niceRefinementIndices a s b d level T T2 system.valid1)
    (hu : rawU ∈ T) (hw : rawW ∈ T)
    (member : stageOneAssignment sharedIdx rawU rawW ∈
      M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) A) :
    ∃ (C E : L) (U Rf Rc u w : (M.nameDomain s).names),
      refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices a s b d level T T2 system.valid1 ∧
      u.val.val ∈ T ∧ w.val.val ∈ T ∧
      stageOneAssignment
        (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val.val w.val.val ∈ A ∧
      sharedIdx = refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
        (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val ∧
      rawU = (a.act s h u.val).val ∧ rawW = (a.act s h w.val).val ∧
      ZFSet.pair (ZFSet.pair (t.encode h) (stageOneAssignment
        (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val.val w.val.val)) (stageOneAssignment sharedIdx rawU rawW) ∈
        M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history := by
  obtain ⟨x, source, edge⟩ := (M.structuralAssignmentImage_entry t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history
    (t.encode h) A _).1 member
  have dataEq := M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports system.inputs.condition_maps level T T2 system.valid1 system.valid2
  have target : stageOneAssignment sharedIdx rawU rawW ∈ stageOneAssignments
      (M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)
        t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level 0) T := by
    rw [dataEq]
    exact (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨index, hu, hw⟩
  have branchMember := (M.structuralAssignmentActionGraph_branch_iff t.carrier b.carrier
    b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2
    function stored edge).2 target
  have original := branchMember
  rw [dataEq] at original
  obtain ⟨idx, hi, originalU, hOriginalU, originalW, hOriginalW, rfl⟩ :=
    (mem_stageOneAssignments _ _ x).1 original
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d level T T2 system.valid1 system.valid2 hi
  let u : (M.nameDomain s).names :=
    ⟨⟨originalU, system.valid1 originalU hOriginalU⟩, M.transitive hT hOriginalU⟩
  let w : (M.nameDomain s).names :=
    ⟨⟨originalW, system.valid1 originalW hOriginalW⟩, M.transitive hT hOriginalW⟩
  have branch := ((M.structuralAssignmentActionGraph_branch_entry t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 (d.actionGraph b t) function stored
    branchMember (t.encode h) (stageOneAssignment sharedIdx rawU rawW)).1 edge).2
  rw [M.rawStageRefinementAssignmentActionGraph_eq a s t b d pairing unions powers separation collection
    carrier group nodes order system.inputs.condition_maps system.inputs.node_maps supports level T T2
    hLevel hT system.valid1 system.valid2 system.inputs.terms_closed system.inputs.pairs_closed
    system.inputs.family_ground system.indices.index_ground h] at branch
  have moved := (M.refinementAssignmentActionGraph_entry a s b d level T T2 system.valid1
    system.valid2 system.inputs.terms_closed t pairing unions powers separation collection carrier
    order system.inputs.condition_maps system.inputs.pairs_closed system.inputs.family_ground
    h C E U Rf Rc u.val w.val hi hOriginalU hOriginalW _).1 branch
  obtain ⟨sameIndex, sameU, sameW⟩ := (stageOneAssignment_eq_iff _ _ _ _ _ _).1 moved
  exact ⟨C, E, U, Rf, Rc, u, w, hi, hOriginalU, hOriginalW, source,
    sameIndex, sameU, sameW, edge⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})

theorem structuralAssignmentImage_selected_edge
    {stages history level P order top action g sourceA x y : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
    (member : x ∈ assignmentOnIndices
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T sourceA)
    (edge : ZFSet.pair (ZFSet.pair g x) y ∈
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history) :
    y ∈ assignmentOnIndices
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T
      (M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g sourceA) := by
  obtain ⟨source, branch⟩ := (mem_assignmentOnIndices _ _ _ _).1 member
  exact (mem_assignmentOnIndices _ _ _ _).2
    ⟨(M.structuralAssignmentImage_entry G nodes nodeOrder nodeAction basis T T2
      stages history g sourceA y).2 ⟨x, source, edge⟩,
      (M.structuralAssignmentActionGraph_branch_iff G nodes nodeOrder nodeAction basis T T2
        function stored edge).1 branch⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
