import OAI.SetTheory.PartitionPrinciple.Definability.RefinementDataHistoryEntryFormulas

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

private noncomputable def storedClassFormula (side : Fin 2) : SetFormula 4 :=
  let w := prefixIndex 4 15
  let old := suffixIndex 4 15
  exBlock 15 (.ex (.conj
    (BoundedFormula.nonemptyTupleFormula 14 0 (fun j => (w j).succ)).toFormula
    (.conj (BoundedFormula.pairMembershipFormula (old 0).succ 0 (old 2).succ).toFormula
      (reindex (extend (old 1).succ (extend (old 3).succ (fun j => (w j).succ)))
        (M.definable_storedAssignmentClassGraph pairing unions powers separation side).formula))))

private theorem realize_storedClassFormula (side : Fin 2)
    (env : Fin 4 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (storedClassFormula M pairing unions powers separation side) env ↔
      ∃ d : Fin 15 → ZFSet.{u}, (∀ j, d j ∈ M.sets) ∧
        ZFSet.pair (env 0) (refinementFormulaDataCode d) ∈ env 2 ∧
        env 1 = M.storedAssignmentClassGraph (env 3) d side := by
  unfold storedClassFormula
  rw [realize_exBlock]
  apply exists_congr
  intro d
  apply and_congr_right
  intro ground
  have args (code : ZFSet.{u}) :
      (fun j => extend code (extendMany 15 d env)
        (extend (suffixIndex 4 15 1).succ
          (extend (suffixIndex 4 15 3).succ (fun j => (prefixIndex 4 15 j).succ)) j)) =
        extend (env 1) (extend (env 3) d) := by
    rw [map_extend, map_extend]
    simp only [extend, Fin.cases_succ, extendMany_suffix, extendMany_prefix]
  simp only [realize_ex]
  constructor
  · rintro ⟨code, hc, tuple, stored, output⟩
    have all : ∀ j, (extend code (extendMany 15 d env)) j ∈ M.sets :=
      Fin.cases hc (extendMany_members 15 d env ground members)
    have eqCode := (BoundedFormula.truth_nonemptyTupleFormula 14 0
      (fun j => (prefixIndex 4 15 j).succ) _).1
      ((BoundedFormula.realize_toFormula M _ _ all).1 tuple)
    change code = refinementFormulaDataCode d at eqCode
    have edge := (BoundedFormula.truth_pairMembershipFormula
      (suffixIndex 4 15 0).succ 0 (suffixIndex 4 15 2).succ _).1
      ((BoundedFormula.realize_toFormula M _ _ all).1 stored)
    change ZFSet.pair (env 0) code ∈ env 2 at edge
    rw [realize_reindex, args] at output
    have value := ((M.definable_storedAssignmentClassGraph pairing unions powers separation side).correct
      (extend (env 3) d) (Fin.cases (members 3) ground) (env 1) (members 1)).1 output
    exact ⟨eqCode ▸ edge, value⟩
  · rintro ⟨edge, value⟩
    let code := refinementFormulaDataCode d
    have hc := M.refinementFormulaDataCode_mem pairing d ground
    have all : ∀ j, (extend code (extendMany 15 d env)) j ∈ M.sets :=
      Fin.cases hc (extendMany_members 15 d env ground members)
    refine ⟨code, hc, ?_, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ all).2
      exact (BoundedFormula.truth_nonemptyTupleFormula 14 0
        (fun j => (prefixIndex 4 15 j).succ) _).2 rfl
    · apply (BoundedFormula.realize_toFormula M _ _ all).2
      exact (BoundedFormula.truth_pairMembershipFormula
        (suffixIndex 4 15 0).succ 0 (suffixIndex 4 15 2).succ _).2 edge
    · rw [realize_reindex, args]
      exact ((M.definable_storedAssignmentClassGraph pairing unions powers separation side).correct
        (extend (env 3) d) (Fin.cases (members 3) ground) (env 1) (members 1)).2 value

include pairing unions powers separation in
theorem exists_storedAssignmentClassFamily
    (collection : CollectionSchema M.sets) (side : Fin 2)
    {levels stages history A T : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hHistory : history ∈ M.sets) (hA : A ∈ M.sets)
    (inside : levels ⊆ stages) (valid : RefinementDataHistory stages history T) :
    ∃ graph ∈ M.sets, FunctionGraphOn levels graph ∧
      ∀ alpha (d : Fin 15 → ZFSet.{u}),
        ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history →
        ∀ y, ZFSet.pair alpha y ∈ graph ↔
          alpha ∈ levels ∧ y = M.storedAssignmentClassGraph A d side := by
  let params : Fin 2 → ZFSet.{u} := ![history, A]
  have members : ∀ j, params j ∈ M.sets := Fin.cases hHistory (Fin.cases hA (fun j => Fin.elim0 j))
  let formula := storedClassFormula M pairing unions powers separation side
  have meaning (alpha y : ZFSet.{u}) (ha : alpha ∈ M.sets) (hy : y ∈ M.sets) :=
    realize_storedClassFormula M pairing unions powers separation side
      (extend alpha (extend y params)) (Fin.cases ha (Fin.cases hy members))
  have unique (alpha y z : ZFSet.{u}) (ha : alpha ∈ M.sets) (hy : y ∈ M.sets) (hz : z ∈ M.sets)
      (first : Realize M.sets formula (extend alpha (extend y params)))
      (second : Realize M.sets formula (extend alpha (extend z params))) : y = z := by
    obtain ⟨d, _, de, dy⟩ := (meaning alpha y ha hy).1 first
    obtain ⟨e, _, ee, ez⟩ := (meaning alpha z ha hz).1 second
    have same := refinementFormulaDataCode_injective (valid.function.unique de ee)
    exact dy.trans (same ▸ ez.symm)
  obtain ⟨B, hB, bounded⟩ := M.collection_witness collection formula params members hLevels (by
    intro alpha ha
    obtain ⟨code, entry⟩ := valid.function.total (inside ha)
    obtain ⟨d, rfl⟩ := valid.decoded alpha code entry
    have fields := M.refinementFormulaDataCode_fields_mem _ (M.pair_right (M.transitive hHistory entry))
    have output := (M.definable_storedAssignmentClassGraph pairing unions powers separation side).closed
      (extend A d) (Fin.cases hA fields)
    exact ⟨_, output, (meaning alpha _ (M.transitive hLevels ha) output).2 ⟨d, fields, entry, rfl⟩⟩)
  let graph := M.definableRelation formula params levels B
  have hGraph := M.definableRelation_mem pairing unions powers separation formula params members hLevels hB
  refine ⟨graph, hGraph, ⟨B, fun _ h => (ZFSet.mem_sep.1 h).1, ?_⟩, ?_⟩
  · intro alpha ha
    obtain ⟨y, hy, rel⟩ := bounded alpha ha
    refine ⟨y, (M.pair_mem_definableRelation formula params levels B alpha y).2 ⟨ha, hy, rel⟩, ?_⟩
    intro z hz
    obtain ⟨_, hz, rz⟩ := (M.pair_mem_definableRelation formula params levels B alpha z).1 hz
    exact unique alpha z y (M.transitive hLevels ha) (M.transitive hB hz) (M.transitive hB hy) rz rel
  · intro alpha d entry y
    rw [M.pair_mem_definableRelation]
    constructor
    · rintro ⟨ha, hy, rel⟩
      obtain ⟨e, _, ee, ey⟩ := (meaning alpha y (M.transitive hLevels ha) (M.transitive hB hy)).1 rel
      have same := refinementFormulaDataCode_injective (valid.function.unique ee entry)
      exact ⟨ha, same ▸ ey⟩
    · rintro ⟨ha, rfl⟩
      obtain ⟨z, hz, rel⟩ := bounded alpha ha
      obtain ⟨e, _, ee, ez⟩ := (meaning alpha z (M.transitive hLevels ha) (M.transitive hB hz)).1 rel
      have same := refinementFormulaDataCode_injective (valid.function.unique ee entry)
      have eq : z = M.storedAssignmentClassGraph A d side := same ▸ ez
      exact eq ▸ ⟨ha, hz, rel⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include pairing unions powers separation collection infinite choice

open scoped ZFSet

theorem exists_assignmentRequestBatch {stages history T A : ZFSet.{u}}
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
    (hA : A ∈ M.sets) (smallA : M.groundEmbeddable A ZFSet.omega)
    (valid : RefinementDataHistory stages history T)
    (shape : A ⊆ stageOneAssignments (refinementDataHistoryIndices stages history) T)
    (localFunctions : ∀ alpha (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history →
      ∀ side, FunctionGraphOn (assignmentOnIndices (d 0) T A)
        (M.storedAssignmentClassGraph A d side)) :
    let levels := relationImage A stages (refinementDataHistoryLevels stages history T)
    levels ∈ M.sets ∧ M.groundEmbeddable levels ZFSet.omega ∧ levels ⊆ stages ∧
    ∃ families : Fin 2 → ZFSet.{u},
      (∀ side, families side ∈ M.sets ∧ FunctionGraphOn levels (families side)) ∧
      (∀ side alpha (d : Fin 15 → ZFSet.{u}),
        ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history →
        ∀ graph, ZFSet.pair alpha graph ∈ families side ↔
          alpha ∈ levels ∧ graph = M.storedAssignmentClassGraph A d side) ∧
      let flat := fun side => ⋃₀ functionGraphRange levels (families side)
      let requests := fun side => functionGraphRange A (flat side)
      (∀ side, flat side ∈ M.sets ∧ FunctionGraphOn A (flat side)) ∧
      (requests 0 ∪ requests 1) ∈ M.sets ∧
      M.groundEmbeddable (requests 0 ∪ requests 1) ZFSet.omega := by
  let levels := relationImage A stages (refinementDataHistoryLevels stages history T)
  have hOmega := M.omega_mem separation infinite
  have hLevelGraph := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT
  have hLevels := M.relationImage_mem separation hA hStages hLevelGraph
  have smallLevels := M.groundEmbeddable_function_image pairing unions powers separation choice
    hA hStages hOmega hLevelGraph valid.levels_function smallA
  have inside : levels ⊆ stages := fun _ h => (mem_relationImage _ _ _ _).1 h |>.1
  have family (side : Fin 2) := M.exists_storedAssignmentClassFamily pairing unions powers separation
    collection side hLevels hHistory hA inside valid
  choose families ground functions entries using family
  let flat := fun side => ⋃₀ functionGraphRange levels (families side)
  have flatEntry (side : Fin 2) (z : ZFSet.{u}) : z ∈ flat side ↔
      ∃ alpha ∈ levels, ∃ d : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history ∧
          z ∈ M.storedAssignmentClassGraph A d side := by
    rw [ZFSet.mem_sUnion]
    constructor
    · rintro ⟨g, hg, hz⟩
      obtain ⟨alpha, ha, stored⟩ := (mem_functionGraphRange levels (families side) g).1 hg
      obtain ⟨code, entry⟩ := valid.function.total (inside ha)
      obtain ⟨d, rfl⟩ := valid.decoded alpha code entry
      exact ⟨alpha, ha, d, entry, ((entries side alpha d entry g).1 stored).2 ▸ hz⟩
    · rintro ⟨alpha, ha, d, entry, hz⟩
      exact ⟨_, (mem_functionGraphRange levels (families side) _).2
        ⟨alpha, ha, (entries side alpha d entry _).2 ⟨ha, rfl⟩⟩, hz⟩
  have levelOf {alpha : ZFSet.{u}} {d : Fin 15 → ZFSet.{u}}
      (entry : ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history)
      {x : ZFSet.{u}} (hx : x ∈ assignmentOnIndices (d 0) T A) :
      ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages history T := by
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments _ _ _).1
      ((mem_assignmentOnIndices _ _ _ _).1 hx).2
    have terms := valid.terms alpha d entry
    exact valid.coverage alpha (valid.function.pair_source entry) d entry i hi u
      (terms.symm ▸ hu) w (terms.symm ▸ hw)
  have cover (x : ZFSet.{u}) (hx : x ∈ A) :
      ∃ alpha ∈ levels, ∃ d : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history ∧
        x ∈ assignmentOnIndices (d 0) T A := by
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments _ _ _).1 (shape hx)
    obtain ⟨alpha, ha, d, entry, idx⟩ := (mem_refinementDataHistoryIndices _ _ _).1 hi
    have selected := (mem_assignmentOnIndices (d 0) T A _).2
      ⟨hx, (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨idx, hu, hw⟩⟩
    exact ⟨alpha, (mem_relationImage _ _ _ _).2 ⟨ha, _, hx, levelOf entry selected⟩,
      d, entry, selected⟩
  have flatGround (side : Fin 2) : flat side ∈ M.sets :=
    M.union_mem unions (M.functionGraphRange_mem unions separation hLevels (ground side))
  have flatFunction (side : Fin 2) : FunctionGraphOn A (flat side) := by
    refine ⟨⋃₀ ⋃₀ flat side, ?_, ?_⟩
    · intro z hz
      obtain ⟨alpha, _, d, entry, member⟩ := (flatEntry side z).1 hz
      obtain ⟨x, hx, y, rfl⟩ := (localFunctions alpha d entry side).shape z member
      exact ZFSet.pair_mem_prod.2
        ⟨((mem_assignmentOnIndices _ _ _ _).1 hx).1, pair_second_mem_doubleUnion hz⟩
    · intro x hx
      obtain ⟨alpha, ha, d, entry, selected⟩ := cover x hx
      obtain ⟨y, hy⟩ := (localFunctions alpha d entry side).total selected
      refine ⟨y, (flatEntry side _).2 ⟨alpha, ha, d, entry, hy⟩, ?_⟩
      intro z hz
      obtain ⟨beta, _, e, ee, ez⟩ := (flatEntry side _).1 hz
      have betaSelected := (localFunctions beta e ee side).pair_source ez
      have sameLevel := (functionCode_partial valid.levels_function).unique x beta alpha
        (levelOf ee betaSelected) (levelOf entry selected)
      subst beta
      have same := refinementFormulaDataCode_injective (valid.function.unique ee entry)
      subst e
      exact (localFunctions alpha d entry side).unique ez hy
  let requests := fun side => functionGraphRange A (flat side)
  have requestGround (side : Fin 2) : requests side ∈ M.sets :=
    M.functionGraphRange_mem unions separation hA (flatGround side)
  have requestSmall (side : Fin 2) : M.groundEmbeddable (requests side) ZFSet.omega :=
    M.groundEmbeddable_function_image pairing unions powers separation choice hA
      (M.union_mem unions (M.union_mem unions (flatGround side))) hOmega (flatGround side)
      (flatFunction side).to_isFunc smallA
  exact ⟨hLevels, smallLevels, inside, families, fun side => ⟨ground side, functions side⟩,
    entries, fun side => ⟨flatGround side, flatFunction side⟩,
    M.binary_union_mem pairing unions (requestGround 0) (requestGround 1),
    M.groundCountable_binary_union pairing unions powers separation infinite choice
      (requestGround 0) (requestGround 1) (requestSmall 0) (requestSmall 1)⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
