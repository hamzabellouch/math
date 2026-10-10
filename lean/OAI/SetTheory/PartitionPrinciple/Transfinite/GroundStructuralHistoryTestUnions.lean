import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRawRefinementStageWitnesses

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def structuralRefinementHistory
    (G nodes nodeOrder basis T T2 stages history : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun x : {x : SetMembers history //
      ∃ f : Fin 5 → ZFSet.{u}, SetMembers.raw x = nonemptyTupleCode 4 f ∧ f 0 ∈ stages} =>
    let f := Classical.choose x.property
    ZFSet.pair (f 0) (M.rawRefinementFormulaDataCode (f 1) (f 2) (f 3) (f 4)
      G nodes nodeOrder basis T T2 (f 0)))

theorem mem_structuralRefinementHistory
    (G nodes nodeOrder basis T T2 stages history z : ZFSet.{u}) :
    z ∈ M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history ↔
      ∃ level ∈ stages, ∃ P order top action,
        ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
        z = ZFSet.pair level (M.rawRefinementFormulaDataCode P order top action
          G nodes nodeOrder basis T T2 level) := by
  rw [structuralRefinementHistory, ZFSet.mem_range]
  constructor
  · rintro ⟨x, equal⟩
    let f := Classical.choose x.property
    have shape := Classical.choose_spec x.property
    refine ⟨f 0, shape.2, f 1, f 2, f 3, f 4, ?_, equal.symm⟩
    have tuple : nonemptyTupleCode 4 f = ZFSet.pair (f 0)
        (forcingStageCode (f 1) (f 2) (f 3) (f 4)) := rfl
    exact tuple ▸ shape.1 ▸ SetMembers.raw_mem x.val
  · rintro ⟨level, hl, P, order, top, action, entry, rfl⟩
    let f : Fin 5 → ZFSet.{u} := ![level, P, order, top, action]
    let x : {x : SetMembers history // ∃ f : Fin 5 → ZFSet.{u},
        SetMembers.raw x = nonemptyTupleCode 4 f ∧ f 0 ∈ stages} :=
      ⟨SetMembers.ofMem _ entry, f, SetMembers.raw_ofMem _ entry, hl⟩
    refine ⟨x, ?_⟩
    have same : Classical.choose x.property = f := nonemptyTupleCode_injective 4
      ((Classical.choose_spec x.property).1.symm.trans (SetMembers.raw_ofMem _ entry))
    dsimp only
    rw [same]
    rfl

theorem pair_mem_structuralRefinementHistory
    (G nodes nodeOrder basis T T2 stages history level output : ZFSet.{u}) :
    ZFSet.pair level output ∈ M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history ↔
      level ∈ stages ∧ ∃ P order top action,
        ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
        output = M.rawRefinementFormulaDataCode P order top action G nodes nodeOrder basis T T2 level := by
  rw [M.mem_structuralRefinementHistory]
  constructor
  · rintro ⟨l, hl, P, order, top, action, entry, equal⟩
    obtain ⟨rfl, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hl, P, order, top, action, entry, value⟩
  · rintro ⟨hl, P, order, top, action, entry, rfl⟩
    exact ⟨level, hl, P, order, top, action, entry, rfl⟩

theorem structuralRefinementHistory_entry
    (G nodes nodeOrder basis T T2 stages history level P order top action output : ZFSet.{u})
    (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history) :
    ZFSet.pair level output ∈ M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history ↔
      output = M.rawRefinementFormulaDataCode P order top action G nodes nodeOrder basis T T2 level := by
  rw [M.pair_mem_structuralRefinementHistory]
  constructor
  · rintro ⟨_, P', order', top', action', entry, value⟩
    have same := function.unique entry stored
    obtain ⟨rfl, rfl, rfl, rfl⟩ := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 same
    exact value
  · intro value
    exact ⟨function.pair_source stored, P, order, top, action, stored, value⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder basis T T2 : ZFSet.{u})

 theorem structuralRefinementHistory_domain_restrict {stages earlier history : ZFSet.{u}}
    (subset : earlier ⊆ stages) :
    M.structuralRefinementHistory G nodes nodeOrder basis T T2 earlier history =
      graphRestriction earlier (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨level, hl, P, order, top, action, stored, rfl⟩ := (M.mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _).1 member
    exact pair_mem_graphRestriction.2 ⟨(M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
      ⟨subset hl, P, order, top, action, stored, rfl⟩, hl⟩
  · intro member
    obtain ⟨level, hl, output, rfl, entry⟩ := mem_graphRestriction.1 member
    obtain ⟨_, P, order, top, action, stored, value⟩ := (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).1 entry
    exact (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
      ⟨hl, P, order, top, action, stored, value⟩

theorem structuralRefinementHistory_history_restrict (stages history : ZFSet.{u}) :
    M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages (graphRestriction stages history) =
      M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history := by
  apply ZFSet.ext
  intro z
  rw [M.mem_structuralRefinementHistory, M.mem_structuralRefinementHistory]
  constructor
  · rintro ⟨level, hl, P, order, top, action, stored, value⟩
    exact ⟨level, hl, P, order, top, action, (pair_mem_graphRestriction.1 stored).1, value⟩
  · rintro ⟨level, hl, P, order, top, action, stored, value⟩
    exact ⟨level, hl, P, order, top, action, pair_mem_graphRestriction.2 ⟨stored, hl⟩, value⟩

theorem structuralRefinementHistory_append {stages history level : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (P order top action : ZFSet.{u}) :
    M.structuralRefinementHistory G nodes nodeOrder basis T T2 (insert level stages)
      (insert (ZFSet.pair level (forcingStageCode P order top action)) history) =
    insert (ZFSet.pair level (M.rawRefinementFormulaDataCode P order top action G nodes nodeOrder basis T T2 level))
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨l, _, P', order', top', action', stored, rfl⟩ := (M.mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _).1 member
    rcases ZFSet.mem_insert_iff.1 stored with equal | old
    · obtain ⟨rfl, same⟩ := ZFSet.pair_inj.1 equal
      obtain ⟨rfl, rfl, rfl, rfl⟩ := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 same
      exact ZFSet.mem_insert _ _
    · exact ZFSet.mem_insert_iff.2 (Or.inr ((M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
        ⟨function.pair_source old, P', order', top', action', old, rfl⟩))
  · intro member
    rcases ZFSet.mem_insert_iff.1 member with rfl | old
    · exact (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
        ⟨ZFSet.mem_insert _ _, P, order, top, action, ZFSet.mem_insert _ _, rfl⟩
    · obtain ⟨l, hl, P', order', top', action', stored, rfl⟩ := (M.mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _).1 old
      exact (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
        ⟨ZFSet.mem_insert_of_mem _ hl, P', order', top', action', ZFSet.mem_insert_of_mem _ stored, rfl⟩

theorem structuralRefinementHistory_function {stages history : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (shape : ∀ level ∈ stages, ∃ P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history) :
    FunctionGraphOn stages (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
  let H := M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history
  refine ⟨⋃₀ ⋃₀ H, ?_, ?_⟩
  · intro z hz
    obtain ⟨level, hl, P, order, top, action, _, equal⟩ := (M.mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _).1 hz
    rw [equal] at hz ⊢
    exact ZFSet.pair_mem_prod.2 ⟨hl, pair_second_mem_doubleUnion hz⟩
  · intro level hl
    obtain ⟨P, order, top, action, stored⟩ := shape level hl
    have exactEntry := M.structuralRefinementHistory_entry G nodes nodeOrder basis T T2 stages history
      level P order top action
    refine ⟨_, (exactEntry _ function stored).2 rfl, ?_⟩
    intro y hy
    exact (exactEntry y function stored).1 hy

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace BoundedFormula

noncomputable def refinementDataHistoryFieldFormula {n : Nat}
    (stages history z : Fin n) (j : Fin 15) : BoundedFormula n :=
  exPairFields z (.conj (.mem 1 stages.succ.succ)
    (exGraphFields history.succ.succ
      (.conj (.equal 1 3) (tupleFieldFormula 14 0 2 j))))

theorem truth_refinementDataHistoryFieldFormula {n : Nat}
    (stages history z : Fin n) (j : Fin 15) (env : Fin n → ZFSet.{u}) :
    Truth (refinementDataHistoryFieldFormula stages history z j) env ↔
      ∃ alpha ∈ env stages, ∃ d : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode d) ∈ env history ∧
          env z = ZFSet.pair alpha (d j) := by
  simp only [refinementDataHistoryFieldFormula, truth_exPairFields, Truth,
    truth_exGraphFields, truth_tupleFieldFormula]
  change (∃ alpha y, env z = ZFSet.pair alpha y ∧ alpha ∈ env stages ∧
    ∃ key data, ZFSet.pair key data ∈ env history ∧ key = alpha ∧
      ∃ d : Fin 15 → ZFSet.{u}, data = refinementFormulaDataCode d ∧ y = d j) ↔ _
  constructor
  · rintro ⟨alpha, y, pair, halpha, key, data, entry, rfl, d, rfl, rfl⟩
    exact ⟨key, halpha, d, entry, pair⟩
  · rintro ⟨alpha, halpha, d, entry, equal⟩
    exact ⟨alpha, d j, equal, halpha, alpha, refinementFormulaDataCode d, entry, rfl, d, rfl, rfl⟩

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem refinementDataHistoryField_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages history : ZFSet.{u}} (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (j : Fin 15) : refinementDataHistoryField stages history j ∈ M.sets := by
  have bound := M.prod_mem pairing unions powers separation hStages
    (M.tupleFieldBound_mem pairing unions 14 (M.union_mem unions (M.union_mem unions hHistory)))
  let params := extend stages (extend history Fin.elim0)
  have ground := M.bounded_separation_mem separation
    (BoundedFormula.refinementDataHistoryFieldFormula 1 2 0 j) params
    (Fin.cases hStages (Fin.cases hHistory (fun i => Fin.elim0 i))) bound
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.refinementDataHistoryFieldFormula 1 2 0 j) (extend z params))
      (ZFSet.prod stages (tupleFieldBound 14 (⋃₀ ⋃₀ history))) =
        refinementDataHistoryField stages history j := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, refinementDataHistoryField, ZFSet.mem_sep]
    exact and_congr_right (fun _ => BoundedFormula.truth_refinementDataHistoryFieldFormula 1 2 0 j _)
  exact equal ▸ ground

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure RefinementDataHistory (stages history T : ZFSet.{u}) : Prop where
  function : FunctionGraphOn stages history
  decoded : ∀ alpha data, ZFSet.pair alpha data ∈ history →
    ∃ d : Fin 15 → ZFSet.{u}, data = refinementFormulaDataCode d
  terms : ∀ alpha (d : Fin 15 → ZFSet.{u}),
    ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history → d 6 = T
  literal : ∀ alpha (d : Fin 15 → ZFSet.{u}),
    ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history → RefinementIndexLevelCode (d 0) alpha

noncomputable def refinementDataHistoryIndices (stages history : ZFSet.{u}) : ZFSet.{u} :=
  refinementHistoryIndices stages (refinementDataHistoryField stages history 0)

noncomputable def refinementDataHistoryLevels (stages history T : ZFSet.{u}) : ZFSet.{u} :=
  refinementHistoryAssignmentLevels stages (refinementDataHistoryField stages history 0) T

namespace RefinementDataHistory
variable {stages history T : ZFSet.{u}} (valid : RefinementDataHistory stages history T)
include valid

theorem index_function : FunctionGraphOn stages (refinementDataHistoryField stages history 0) :=
  refinementDataHistoryField_function valid.function valid.decoded 0

theorem index_literal : ∀ alpha I, ZFSet.pair alpha I ∈ refinementDataHistoryField stages history 0 →
    RefinementIndexLevelCode I alpha :=
  refinementDataHistoryField_index_levels valid.literal

theorem levels_function :
    ZFSet.IsFunc (stageOneAssignments (refinementDataHistoryIndices stages history) T) stages
      (refinementDataHistoryLevels stages history T) :=
  refinementHistoryAssignmentLevels_function valid.index_literal

theorem coverage : ForcingHistoryLevelCoverage stages history (refinementDataHistoryLevels stages history T) := by
  intro beta _ d entry t ht u hu w hw
  apply (refinementHistoryAssignmentLevels_entry valid.index_function valid.index_literal T t u w beta).2
  have same := valid.terms beta d entry
  exact ⟨d 0, (refinementDataHistoryField_entry valid.function d entry 0 _).2 rfl,
    ht, same ▸ hu, same ▸ hw⟩

end RefinementDataHistory
namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem refinementDataHistoryIndices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages history : ZFSet.{u}} (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) :
    refinementDataHistoryIndices stages history ∈ M.sets :=
  M.refinementHistoryIndices_mem unions separation hStages
    (M.refinementDataHistoryField_mem pairing unions powers separation hStages hHistory 0)

theorem refinementDataHistoryLevels_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages history T : ZFSet.{u}} (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (hT : T ∈ M.sets) : refinementDataHistoryLevels stages history T ∈ M.sets :=
  M.refinementHistoryAssignmentLevels_mem pairing unions powers separation hStages
    (M.refinementDataHistoryField_mem pairing unions powers separation hStages hHistory 0) hT

end TransitiveGround




namespace RefinementDataHistory
variable {stages history T : ZFSet.{u}} (valid : RefinementDataHistory stages history T)
include valid

theorem restrict {earlier : ZFSet.{u}} (subset : earlier ⊆ stages) :
    RefinementDataHistory earlier (graphRestriction earlier history) T := by
  refine ⟨valid.function.restrict subset, ?_, ?_, ?_⟩
  · intro alpha data entry
    exact valid.decoded alpha data (pair_mem_graphRestriction.1 entry).1
  · intro alpha d entry
    exact valid.terms alpha d (pair_mem_graphRestriction.1 entry).1
  · intro alpha d entry
    exact valid.literal alpha d (pair_mem_graphRestriction.1 entry).1

theorem append {alpha : ZFSet.{u}} (outside : alpha ∉ stages) (d : Fin 15 → ZFSet.{u})
    (terms : d 6 = T) (literal : RefinementIndexLevelCode (d 0) alpha) :
    RefinementDataHistory (insert alpha stages)
      (insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history) T := by
  refine ⟨valid.function.insert outside _, ?_, ?_, ?_⟩
  · intro beta data entry
    rcases ZFSet.mem_insert_iff.1 entry with equal | old
    · exact ⟨d, (ZFSet.pair_inj.1 equal).2⟩
    · exact valid.decoded beta data old
  · intro beta fields entry
    rcases ZFSet.mem_insert_iff.1 entry with equal | old
    · have same := refinementFormulaDataCode_injective (ZFSet.pair_inj.1 equal).2
      exact (congrFun same 6).trans terms
    · exact valid.terms beta fields old
  · intro beta fields entry
    rcases ZFSet.mem_insert_iff.1 entry with equal | old
    · obtain ⟨rfl, code⟩ := ZFSet.pair_inj.1 equal
      have same := refinementFormulaDataCode_injective code
      exact (congrFun same 0).symm ▸ literal
    · exact valid.literal beta fields old

theorem prefix_cut {alpha beta : ZFSet.{u}} (subset : alpha ⊆ stages) (below : beta ⊆ alpha)
    (A : ZFSet.{u}) :
    assignmentCut (refinementDataHistoryLevels alpha (graphRestriction alpha history) T) beta A =
      assignmentCut (refinementDataHistoryLevels stages history T) beta A :=
  refinementDataHistoryAssignmentCut_prefix valid.function valid.decoded valid.literal subset below T A

end RefinementDataHistory
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.RefinementDataHistory
universe u
variable {stages history T : ZFSet.{u}} (valid : RefinementDataHistory stages history T)
variable {beta : ZFSet.{u}} {d : Fin 15 → ZFSet.{u}}
variable (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
include valid entry

theorem assignment_level_iff (t : ZFSet.{u}) (ht : t ∈ d 0)
    (u : ZFSet.{u}) (hu : u ∈ d 6) (w : ZFSet.{u}) (hw : w ∈ d 6) (xi : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment t u w) xi ∈ refinementDataHistoryLevels stages history T ↔
      xi = beta := by
  have actual := valid.coverage beta (valid.function.pair_source entry) d entry t ht u hu w hw
  have source := (ZFSet.pair_mem_prod.1 (valid.levels_function.1 actual)).1
  obtain ⟨value, _, unique⟩ := valid.levels_function.2 _ source
  exact ⟨fun member => (unique xi member).trans (unique beta actual).symm,
    fun equal => equal.symm ▸ actual⟩

theorem rawTests_splice_below (M : TransitiveGround.{u}) (alpha Aq Ap lower : ZFSet.{u})
    (inside : beta ∈ alpha) :
    stageOneRawTests M d (assignmentSplice (refinementDataHistoryLevels stages history T) alpha Aq Ap) lower ↔
      stageOneRawTests M d Aq lower := by
  apply stageOneRawTests_congr
  intro t ht u hu w hw
  have chosen : ∃ xi ∈ alpha, ZFSet.pair (stageOneAssignment t u w) xi ∈
      refinementDataHistoryLevels stages history T :=
    ⟨beta, inside, (valid.assignment_level_iff entry t ht u hu w hw beta).2 rfl⟩
  rw [mem_assignmentSplice]
  exact ⟨fun h => h.elim And.left (fun upper => False.elim (upper.2 chosen)),
    fun member => Or.inl ⟨member, chosen⟩⟩

theorem rawTests_splice_above (M : TransitiveGround.{u}) (alpha Aq Ap lower : ZFSet.{u})
    (outside : beta ∉ alpha) :
    stageOneRawTests M d (assignmentSplice (refinementDataHistoryLevels stages history T) alpha Aq Ap) lower ↔
      stageOneRawTests M d Ap lower := by
  apply stageOneRawTests_congr
  intro t ht u hu w hw
  have absent : ¬ ∃ xi ∈ alpha, ZFSet.pair (stageOneAssignment t u w) xi ∈
      refinementDataHistoryLevels stages history T := by
    rintro ⟨xi, hxi, member⟩
    exact outside ((valid.assignment_level_iff entry t ht u hu w hw xi).1 member ▸ hxi)
  rw [mem_assignmentSplice]
  exact ⟨fun h => h.elim (fun lower => False.elim (absent lower.2)) And.left,
    fun member => Or.inr ⟨member, absent⟩⟩

theorem rawTests_on_earlier_cut (M : TransitiveGround.{u}) (alpha A lower : ZFSet.{u})
    (outside : beta ∉ alpha) :
    stageOneRawTests M d (assignmentCut (refinementDataHistoryLevels stages history T) alpha A) lower := by
  have absent : ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
      stageOneAssignment t u w ∉ assignmentCut (refinementDataHistoryLevels stages history T) alpha A := by
    intro t ht u hu w hw member
    obtain ⟨_, xi, hxi, level⟩ := (mem_assignmentCut _ _ _ _).1 member
    exact outside ((valid.assignment_level_iff entry t ht u hu w hw xi).1 level ▸ hxi)
  exact ⟨fun t ht u hu w hw member => False.elim (absent t ht u hu w hw member),
    fun t ht u hu _ _ w hw _ _ member _ => False.elim (absent t ht u hu w hw member)⟩

end PartitionPilot.Forcing.RefinementDataHistory



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

 theorem rawRefinementFormulaData_level
    (P order top action G nodes nodeOrder basis T T2 level : ZFSet.{u}) :
    RefinementIndexLevelCode (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) level := by
  intro z hz
  obtain ⟨fields, equal, bound⟩ := M.refinementIndices_fields _ _ _ _ _ _ _ _ _ _ _ hz
  exact ⟨fields, equal, ZFSet.mem_singleton.1 (bound 0)⟩

variable (G nodes nodeOrder basis T T2 stages history : ZFSet.{u})

theorem structuralRefinementHistory_decoded {level output : ZFSet.{u}}
    (entry : ZFSet.pair level output ∈ M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) :
    ∃ data : Fin 15 → ZFSet.{u}, output = refinementFormulaDataCode data := by
  obtain ⟨_, P, order, top, action, _, equal⟩ := (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).1 entry
  exact ⟨_, equal⟩

theorem structuralRefinementHistory_fields {level : ZFSet.{u}} (data : Fin 15 → ZFSet.{u})
    (entry : ZFSet.pair level (refinementFormulaDataCode data) ∈
      M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) :
    level ∈ stages ∧ ∃ P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
      data = M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level := by
  obtain ⟨hl, P, order, top, action, stored, equal⟩ := (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).1 entry
  exact ⟨hl, P, order, top, action, stored, refinementFormulaDataCode_injective equal⟩

theorem structuralRefinementHistory_structural_fields {level : ZFSet.{u}} (data : Fin 15 → ZFSet.{u})
    (entry : ZFSet.pair level (refinementFormulaDataCode data) ∈
      M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) :
    data 6 = T ∧ RefinementIndexLevelCode (data 0) level ∧
      ∃ action, ZFSet.pair level (forcingStageCode (data 7) (data 8) (data 9) action) ∈ history := by
  obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
    M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
  exact ⟨rfl, M.rawRefinementFormulaData_level _ _ _ _ _ _ _ _ _ _ _, action, stored⟩

theorem structuralRefinementHistory_dataHistory
    (function : FunctionGraphOn stages history)
    (shape : ∀ level ∈ stages, ∃ P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history) :
    RefinementDataHistory stages (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T where
  function := M.structuralRefinementHistory_function G nodes nodeOrder basis T T2 function shape
  decoded := fun _ _ entry => M.structuralRefinementHistory_decoded G nodes nodeOrder basis T T2 stages history entry
  terms := fun _ data entry =>
    (M.structuralRefinementHistory_structural_fields G nodes nodeOrder basis T T2 stages history data entry).1
  literal := fun _ data entry =>
    (M.structuralRefinementHistory_structural_fields G nodes nodeOrder basis T T2 stages history data entry).2.1

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G L : Type u} [Group G] [PartialOrder L]
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 stages history : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable (witnesses : ∀ level P order top action,
  ZFSet.pair level (forcingStageCode P order top action) ∈ history →
    RawRefinementStageWitness M t b d base directed T T2 level P order top action)
include pairing unions powers separation collection group nodes supports hHistory hT witnesses

theorem structuralHistory_rawTests_union :
    ∀ level (data : Fin 15 → ZFSet.{u}), ZFSet.pair level (refinementFormulaDataCode data) ∈
      M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history →
      ∀ (family lower : Nat → ZFSet.{u}) q,
        (∀ n m, n ≤ m → family n ⊆ family m) →
        (∀ n, ZFSet.pair q (lower n) ∈ data 8) →
        (∀ n, stageOneRawTests M data (family n) (lower n)) →
        stageOneRawTests M data (stageOneAssignmentUnion family) q := by
  intro level data entry family lower q increasing below tests
  obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
    M.structuralRefinementHistory_fields t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history data entry
  have ground := M.forcingStageCode_fields
    (M.transitive (M.union_mem unions (M.union_mem unions hHistory))
      (pair_second_mem_doubleUnion stored))
  exact (witnesses level P order top action stored).rawTests_union
    pairing unions powers separation collection ground.1 group nodes ground.2.1 supports hT
    family lower q increasing below tests

end PartitionPilot.Forcing.TransitiveGround

end OAI
