import OAI.SetTheory.PartitionPrinciple.Definability.GroundPackedRefinementFormulaData

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
universe u

noncomputable def refinementHistoryIndices (alpha history : ZFSet.{u}) : ZFSet.{u} :=
  ⋃₀ functionGraphRange alpha history

theorem mem_refinementHistoryIndices (alpha history x : ZFSet.{u}) :
    x ∈ refinementHistoryIndices alpha history ↔
      ∃ xi ∈ alpha, ∃ I, ZFSet.pair xi I ∈ history ∧ x ∈ I := by
  rw [refinementHistoryIndices, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨I, hI, hx⟩
    obtain ⟨xi, hxi, entry⟩ := (mem_functionGraphRange alpha history I).1 hI
    exact ⟨xi, hxi, I, entry, hx⟩
  · rintro ⟨xi, hxi, I, entry, hx⟩
    exact ⟨I, (mem_functionGraphRange alpha history I).2 ⟨xi, hxi, entry⟩, hx⟩

theorem refinementHistoryIndices_mono {alpha beta history : ZFSet.{u}}
    (subset : alpha ⊆ beta) :
    refinementHistoryIndices alpha history ⊆ refinementHistoryIndices beta history := by
  intro x hx
  obtain ⟨xi, hxi, I, entry, hi⟩ := (mem_refinementHistoryIndices alpha history x).1 hx
  exact (mem_refinementHistoryIndices beta history x).2 ⟨xi, subset hxi, I, entry, hi⟩

noncomputable def refinementHistoryLevels (alpha history : ZFSet.{u}) : ZFSet.{u} :=
  refinementIndexFieldGraph (refinementHistoryIndices alpha history) alpha 0

theorem pair_mem_refinementHistoryLevels {alpha history : ZFSet.{u}}
    (function : FunctionGraphOn alpha history)
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi)
    (x xi : ZFSet.{u}) :
    ZFSet.pair x xi ∈ refinementHistoryLevels alpha history ↔
      ∃ I, ZFSet.pair xi I ∈ history ∧ x ∈ I := by
  rw [refinementHistoryLevels, pair_mem_refinementIndexFieldGraph]
  constructor
  · rintro ⟨hx, _, v, eqv, hxi⟩
    obtain ⟨eta, _, I, entry, hi⟩ := (mem_refinementHistoryIndices alpha history x).1 hx
    obtain ⟨w, eqw, hw⟩ := literal eta I entry x hi
    have same := nonemptyTupleCode_injective 5 (eqv.symm.trans eqw)
    have equal : xi = eta := hxi.trans ((congrFun same 0).trans hw)
    exact ⟨I, equal.symm ▸ entry, hi⟩
  · rintro ⟨I, entry, hi⟩
    obtain ⟨v, eqv, hv⟩ := literal xi I entry x hi
    exact ⟨(mem_refinementHistoryIndices alpha history x).2
      ⟨xi, function.pair_source entry, I, entry, hi⟩,
      function.pair_source entry, v, eqv, hv.symm⟩

theorem refinementHistoryLevels_function {alpha history : ZFSet.{u}}
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi) :
    ZFSet.IsFunc (refinementHistoryIndices alpha history) alpha
      (refinementHistoryLevels alpha history) := by
  apply refinementIndexFieldGraph_function
  intro x hx
  obtain ⟨xi, hxi, I, entry, hi⟩ := (mem_refinementHistoryIndices alpha history x).1 hx
  obtain ⟨v, eqv, hv⟩ := literal xi I entry x hi
  exact ⟨v, eqv, hv.symm ▸ hxi⟩

theorem refinementHistory_fibers_disjoint {history xi eta I J : ZFSet.{u}}
    (literal : ∀ level K, ZFSet.pair level K ∈ history → RefinementIndexLevelCode K level)
    (first : ZFSet.pair xi I ∈ history) (second : ZFSet.pair eta J ∈ history)
    (different : xi ≠ eta) : ∀ x, ¬ (x ∈ I ∧ x ∈ J) :=
  (literal xi I first).disjoint (literal eta J second) different

theorem refinementHistoryAnchor_entry (alpha history B : ZFSet.{u})
    (v : Fin 6 → ZFSet.{u}) (y : ZFSet.{u}) :
    ZFSet.pair (nonemptyTupleCode 5 v) y ∈
        refinementIndexFieldGraph (refinementHistoryIndices alpha history) B 2 ↔
      (∃ xi ∈ alpha, ∃ I, ZFSet.pair xi I ∈ history ∧ nonemptyTupleCode 5 v ∈ I) ∧
        y ∈ B ∧ y = v 2 := by
  rw [refinementIndexFieldGraph_entry, mem_refinementHistoryIndices]

theorem refinementHistoryAnchor_function {alpha history B : ZFSet.{u}}
    (decoded : ∀ xi I, ZFSet.pair xi I ∈ history →
      ∀ x ∈ I, ∃ v : Fin 6 → ZFSet.{u}, x = nonemptyTupleCode 5 v ∧ v 2 ∈ B) :
    ZFSet.IsFunc (refinementHistoryIndices alpha history) B
      (refinementIndexFieldGraph (refinementHistoryIndices alpha history) B 2) := by
  apply refinementIndexFieldGraph_function
  intro x hx
  obtain ⟨xi, _, I, entry, hi⟩ := (mem_refinementHistoryIndices alpha history x).1 hx
  exact decoded xi I entry x hi





noncomputable def refinementHistoryAssignmentLevels (alpha history T : ZFSet.{u}) : ZFSet.{u} :=
  assignmentIndexLevels (refinementHistoryIndices alpha history) T alpha
    (refinementHistoryLevels alpha history)

theorem mem_refinementHistoryAssignments (alpha history T z : ZFSet.{u}) :
    z ∈ stageOneAssignments (refinementHistoryIndices alpha history) T ↔
      ∃ xi ∈ alpha, ∃ I, ZFSet.pair xi I ∈ history ∧ z ∈ stageOneAssignments I T := by
  rw [mem_stageOneAssignments]
  constructor
  · rintro ⟨i, hi, u, hu, w, hw, rfl⟩
    obtain ⟨xi, hxi, I, entry, member⟩ := (mem_refinementHistoryIndices alpha history i).1 hi
    exact ⟨xi, hxi, I, entry,
      (stageOneAssignment_mem_assignments I T i u w).2 ⟨member, hu, hw⟩⟩
  · rintro ⟨xi, hxi, I, entry, member⟩
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T z).1 member
    exact ⟨i, (mem_refinementHistoryIndices alpha history i).2 ⟨xi, hxi, I, entry, hi⟩,
      u, hu, w, hw, rfl⟩

theorem pair_mem_refinementHistoryAssignmentLevels {alpha history : ZFSet.{u}}
    (function : FunctionGraphOn alpha history)
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi)
    (T z xi : ZFSet.{u}) :
    ZFSet.pair z xi ∈ refinementHistoryAssignmentLevels alpha history T ↔
      ∃ I, ZFSet.pair xi I ∈ history ∧ z ∈ stageOneAssignments I T := by
  rw [refinementHistoryAssignmentLevels, pair_mem_assignmentIndexLevels]
  constructor
  · rintro ⟨i, _, u, hu, w, hw, rfl, _, entry⟩
    obtain ⟨I, hI, hi⟩ := (pair_mem_refinementHistoryLevels function literal i xi).1 entry
    exact ⟨I, hI, (stageOneAssignment_mem_assignments I T i u w).2 ⟨hi, hu, hw⟩⟩
  · rintro ⟨I, entry, member⟩
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T z).1 member
    exact ⟨i, (mem_refinementHistoryIndices alpha history i).2
      ⟨xi, function.pair_source entry, I, entry, hi⟩,
      u, hu, w, hw, rfl, function.pair_source entry,
      (pair_mem_refinementHistoryLevels function literal i xi).2 ⟨I, entry, hi⟩⟩

theorem refinementHistoryAssignmentLevels_entry {alpha history : ZFSet.{u}}
    (function : FunctionGraphOn alpha history)
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi)
    (T i u w xi : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u w) xi ∈ refinementHistoryAssignmentLevels alpha history T ↔
      ∃ I, ZFSet.pair xi I ∈ history ∧ i ∈ I ∧ u ∈ T ∧ w ∈ T := by
  rw [pair_mem_refinementHistoryAssignmentLevels function literal]
  simp only [stageOneAssignment_mem_assignments]

theorem refinementHistoryAssignmentLevels_function {alpha history T : ZFSet.{u}}
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi) :
    ZFSet.IsFunc (stageOneAssignments (refinementHistoryIndices alpha history) T) alpha
      (refinementHistoryAssignmentLevels alpha history T) :=
  assignmentIndexLevels_function (refinementHistoryLevels_function literal)

theorem refinementHistoryAssignmentCut_eq {alpha beta history : ZFSet.{u}}
    (function : FunctionGraphOn alpha history)
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi)
    (subset : beta ⊆ alpha) (T A : ZFSet.{u}) :
    assignmentCut (refinementHistoryAssignmentLevels alpha history T) beta A =
      ZFSet.sep (fun z => z ∈ stageOneAssignments (refinementHistoryIndices beta history) T) A := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentCut, ZFSet.mem_sep]
  apply and_congr_right
  intro _
  rw [mem_refinementHistoryAssignments]
  constructor
  · rintro ⟨xi, hxi, entry⟩
    obtain ⟨I, hI, member⟩ := (pair_mem_refinementHistoryAssignmentLevels function literal T z xi).1 entry
    exact ⟨xi, hxi, I, hI, member⟩
  · rintro ⟨xi, hxi, I, entry, member⟩
    have _ : xi ∈ alpha := subset hxi
    exact ⟨xi, hxi, (pair_mem_refinementHistoryAssignmentLevels function literal T z xi).2
      ⟨I, entry, member⟩⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem refinementHistoryIndices_mem
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    {alpha history : ZFSet.{u}} (hAlpha : alpha ∈ M.sets) (hHistory : history ∈ M.sets) :
    refinementHistoryIndices alpha history ∈ M.sets :=
  M.union_mem unions (M.functionGraphRange_mem unions separation hAlpha hHistory)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem refinementHistoryLevels_mem {alpha history : ZFSet.{u}}
    (hAlpha : alpha ∈ M.sets) (hHistory : history ∈ M.sets) :
    refinementHistoryLevels alpha history ∈ M.sets :=
  M.refinementIndexFieldGraph_mem pairing unions powers separation
    (M.refinementHistoryIndices_mem unions separation hAlpha hHistory) hAlpha 0

theorem refinementHistoryAssignmentLevels_mem {alpha history T : ZFSet.{u}}
    (hAlpha : alpha ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets) :
    refinementHistoryAssignmentLevels alpha history T ∈ M.sets :=
  M.assignmentIndexLevels_mem pairing unions powers separation
    (M.refinementHistoryIndices_mem unions separation hAlpha hHistory) hT hAlpha
    (M.refinementHistoryLevels_mem pairing unions powers separation hAlpha hHistory)

theorem refinementHistoryAnchors_mem {alpha history B : ZFSet.{u}}
    (hAlpha : alpha ∈ M.sets) (hHistory : history ∈ M.sets) (hB : B ∈ M.sets) :
    refinementIndexFieldGraph (refinementHistoryIndices alpha history) B 2 ∈ M.sets :=
  M.refinementIndexFieldGraph_mem pairing unions powers separation
    (M.refinementHistoryIndices_mem unions separation hAlpha hHistory) hB 2

theorem refinementHistoryData {alpha history T B : ZFSet.{u}}
    (hAlpha : alpha ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets) (hB : B ∈ M.sets)
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi)
    (decoded : ∀ xi I, ZFSet.pair xi I ∈ history →
      ∀ x ∈ I, ∃ v : Fin 6 → ZFSet.{u}, x = nonemptyTupleCode 5 v ∧ v 2 ∈ B) :
    refinementHistoryIndices alpha history ∈ M.sets ∧
      refinementHistoryLevels alpha history ∈ M.sets ∧
      refinementHistoryAssignmentLevels alpha history T ∈ M.sets ∧
      refinementIndexFieldGraph (refinementHistoryIndices alpha history) B 2 ∈ M.sets ∧
      ZFSet.IsFunc (refinementHistoryIndices alpha history) alpha (refinementHistoryLevels alpha history) ∧
      ZFSet.IsFunc (stageOneAssignments (refinementHistoryIndices alpha history) T) alpha
        (refinementHistoryAssignmentLevels alpha history T) ∧
      ZFSet.IsFunc (refinementHistoryIndices alpha history) B
        (refinementIndexFieldGraph (refinementHistoryIndices alpha history) B 2) :=
  ⟨M.refinementHistoryIndices_mem unions separation hAlpha hHistory,
    M.refinementHistoryLevels_mem pairing unions powers separation hAlpha hHistory,
    M.refinementHistoryAssignmentLevels_mem pairing unions powers separation hAlpha hHistory hT,
    M.refinementHistoryAnchors_mem pairing unions powers separation hAlpha hHistory hB,
    refinementHistoryLevels_function literal, refinementHistoryAssignmentLevels_function literal,
    refinementHistoryAnchor_function decoded⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_historyUnion
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} =>
      refinementHistoryIndices (env 0) (env 1)) where
  formula := exactSetFormula 0 (.ex (.ex
    (.conj (.mem 1 4) (.conj (pairMembershipFormula 1 0 5) (.mem 2 0)))))
  closed := fun _ members => M.refinementHistoryIndices_mem unions separation (members 0) (members 1)
  correct := by
    intro env members z hz
    have ground := M.refinementHistoryIndices_mem unions separation (members 0) (members 1)
    apply M.realize_exactSetFormula 0 _ (extend z env) hz (fun _ h => M.transitive ground h)
    intro w _
    simp only [realize_ex]
    change (∃ a ∈ M.sets, ∃ Y ∈ M.sets, a ∈ env 0 ∧
      Realize M.sets (pairMembershipFormula 1 0 5)
        (extend Y (extend a (extend w (extend z env)))) ∧ w ∈ Y) ↔ _
    rw [mem_refinementHistoryIndices]
    constructor
    · rintro ⟨a, ha, Y, hY, member, entry, inside⟩
      exact ⟨a, member, Y,
        (M.realize_pairMembershipFormula pairing 1 0 5 (extend Y (extend a (extend w (extend z env)))) ha hY (members 1)).1 entry, inside⟩
    · rintro ⟨a, member, Y, entry, inside⟩
      have ha := M.transitive (members 0) member
      have hY := M.transitive (M.union_mem unions (M.union_mem unions (members 1)))
        (pair_second_mem_doubleUnion entry)
      exact ⟨a, ha, Y, hY, member,
        (M.realize_pairMembershipFormula pairing 1 0 5 (extend Y (extend a (extend w (extend z env)))) ha hY (members 1)).2 entry, inside⟩





theorem historyUnion_countable_capture
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {history B : ZFSet.{u}} (hh : history ∈ M.sets) (hB : B ∈ M.sets)
    (small : M.groundEmbeddable B ZFSet.omega)
    (subset : B ⊆ refinementHistoryIndices
      (M.groundOmegaOne pairing unions powers separation collection infinite) history) :
    ∃ beta ∈ M.groundOmegaOne pairing unions powers separation collection infinite,
      B ⊆ refinementHistoryIndices beta history := by
  let C := M.groundOmegaOne pairing unions powers separation collection infinite
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let formula : SetFormula 3 := .ex (.conj (pairMembershipFormula 2 0 3) (.mem 1 0))
  let params : Fin 1 → ZFSet.{u} := ![history]
  have members : ∀ j, params j ∈ M.sets := Fin.cases hh (fun j => Fin.elim0 j)
  have recognize (x alpha : ZFSet.{u}) (ha : alpha ∈ M.sets) :
      Realize M.sets formula (extend x (extend alpha params)) ↔
        ∃ Y, ZFSet.pair alpha Y ∈ history ∧ x ∈ Y := by
    rw [show formula = .ex (.conj (pairMembershipFormula 2 0 3) (.mem 1 0)) from rfl, realize_ex]
    constructor
    · rintro ⟨Y, hY, entry, inside⟩
      exact ⟨Y, (M.realize_pairMembershipFormula pairing 2 0 3
        (extend Y (extend x (extend alpha params))) ha hY hh).1 entry, inside⟩
    · rintro ⟨Y, entry, inside⟩
      have hY := M.transitive (M.union_mem unions (M.union_mem unions hh))
        (pair_second_mem_doubleUnion entry)
      exact ⟨Y, hY, (M.realize_pairMembershipFormula pairing 2 0 3
        (extend Y (extend x (extend alpha params))) ha hY hh).2 entry, inside⟩
  let relation := M.definableRelation formula params B C
  have relationGround := M.definableRelation_mem pairing unions powers separation formula params members hB hC
  have total : ∀ x ∈ B, ∃ alpha ∈ C, ZFSet.pair x alpha ∈ relation := by
    intro x hx
    obtain ⟨alpha, ha, Y, entry, inside⟩ := (mem_refinementHistoryIndices C history x).1 (subset hx)
    exact ⟨alpha, ha, (M.pair_mem_definableRelation formula params B C x alpha).2
      ⟨hx, ha, (recognize x alpha (M.transitive hC ha)).2 ⟨Y, entry, inside⟩⟩⟩
  obtain ⟨selection, ground, function, selected⟩ :=
    M.uniformize_relation pairing unions powers separation choice hB hC relationGround total
  have rangeGround := M.relationImage_mem separation hB hC ground
  have rangeSmall := M.groundEmbeddable_function_image pairing unions powers separation choice
    hB hC (M.omega_mem separation infinite) ground function small
  obtain ⟨beta, hBeta, bounds⟩ := M.groundOmegaOne_countable_bound
    pairing unions powers separation collection infinite choice rangeGround
    (fun _ h => ((mem_relationImage B C selection _).1 h).1) rangeSmall
  refine ⟨beta, hBeta, ?_⟩
  intro x hx
  obtain ⟨alpha, entry, _⟩ := function.2 x hx
  have ha := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  obtain ⟨Y, stored, inside⟩ := (recognize x alpha (M.transitive hC ha)).1
    ((M.pair_mem_definableRelation formula params B C x alpha).1 (selected entry)).2.2
  exact (mem_refinementHistoryIndices beta history x).2
    ⟨alpha, bounds alpha ((mem_relationImage B C selection alpha).2 ⟨ha, x, hx, entry⟩), Y, stored, inside⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
universe u

noncomputable def refinementDataHistoryField (stages history : ZFSet.{u}) (j : Fin 15) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ alpha ∈ stages, ∃ d : Fin 15 → ZFSet.{u},
    ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history ∧ z = ZFSet.pair alpha (d j))
    (ZFSet.prod stages (tupleFieldBound 14 (⋃₀ ⋃₀ history)))

theorem mem_refinementDataHistoryField (stages history z : ZFSet.{u}) (j : Fin 15) :
    z ∈ refinementDataHistoryField stages history j ↔
      ∃ alpha ∈ stages, ∃ d : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history ∧ z = ZFSet.pair alpha (d j) := by
  rw [refinementDataHistoryField, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨alpha, halpha, d, entry, rfl⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨halpha,
      nonemptyTupleCode_field_mem_bound 14 d (pair_second_mem_doubleUnion entry) j⟩,
      alpha, halpha, d, entry, rfl⟩

theorem pair_mem_refinementDataHistoryField (stages history alpha y : ZFSet.{u}) (j : Fin 15) :
    ZFSet.pair alpha y ∈ refinementDataHistoryField stages history j ↔
      alpha ∈ stages ∧ ∃ d : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history ∧ y = d j := by
  rw [mem_refinementDataHistoryField]
  constructor
  · rintro ⟨beta, hbeta, d, entry, equal⟩
    obtain ⟨rfl, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hbeta, d, entry, value⟩
  · rintro ⟨halpha, d, entry, rfl⟩
    exact ⟨alpha, halpha, d, entry, rfl⟩

theorem refinementDataHistoryField_entry {stages history alpha : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (d : Fin 15 → ZFSet.{u})
    (entry : ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history) (j : Fin 15) (y : ZFSet.{u}) :
    ZFSet.pair alpha y ∈ refinementDataHistoryField stages history j ↔ y = d j := by
  rw [pair_mem_refinementDataHistoryField]
  constructor
  · rintro ⟨_, fields, stored, value⟩
    have same := refinementFormulaDataCode_injective (function.unique stored entry)
    exact value.trans (congrFun same j)
  · intro equal
    exact ⟨function.pair_source entry, d, entry, equal⟩

theorem refinementDataHistoryField_function {stages history : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (decoded : ∀ alpha data, ZFSet.pair alpha data ∈ history →
      ∃ d : Fin 15 → ZFSet.{u}, data = refinementFormulaDataCode d) (j : Fin 15) :
    FunctionGraphOn stages (refinementDataHistoryField stages history j) := by
  refine ⟨tupleFieldBound 14 (⋃₀ ⋃₀ history), fun _ member => (ZFSet.mem_sep.1 member).1, ?_⟩
  intro alpha halpha
  obtain ⟨data, entry⟩ := function.total halpha
  obtain ⟨d, rfl⟩ := decoded alpha data entry
  refine ⟨d j, (refinementDataHistoryField_entry function d entry j _).2 rfl, ?_⟩
  intro y member
  exact (refinementDataHistoryField_entry function d entry j y).1 member

theorem refinementDataHistoryField_index_levels {stages history : ZFSet.{u}}
    (literal : ∀ alpha (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history → RefinementIndexLevelCode (d 0) alpha) :
    ∀ alpha I, ZFSet.pair alpha I ∈ refinementDataHistoryField stages history 0 →
      RefinementIndexLevelCode I alpha := by
  intro alpha I entry
  obtain ⟨_, d, stored, rfl⟩ := (pair_mem_refinementDataHistoryField stages history alpha I 0).1 entry
  exact literal alpha d stored





theorem refinementDataHistoryField_domain_restrict {stages earlier history : ZFSet.{u}}
    (subset : earlier ⊆ stages) (j : Fin 15) :
    refinementDataHistoryField earlier history j =
      graphRestriction earlier (refinementDataHistoryField stages history j) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨alpha, halpha, d, entry, rfl⟩ := (mem_refinementDataHistoryField _ _ _ _).1 member
    exact pair_mem_graphRestriction.2
      ⟨(pair_mem_refinementDataHistoryField _ _ _ _ _).2 ⟨subset halpha, d, entry, rfl⟩, halpha⟩
  · intro member
    obtain ⟨alpha, halpha, y, rfl, entry⟩ := mem_graphRestriction.1 member
    obtain ⟨_, d, stored, rfl⟩ := (pair_mem_refinementDataHistoryField _ _ _ _ _).1 entry
    exact (pair_mem_refinementDataHistoryField _ _ _ _ _).2 ⟨halpha, d, stored, rfl⟩

theorem refinementDataHistoryField_history_restrict (stages history : ZFSet.{u}) (j : Fin 15) :
    refinementDataHistoryField stages (graphRestriction stages history) j =
      refinementDataHistoryField stages history j := by
  apply ZFSet.ext
  intro z
  rw [mem_refinementDataHistoryField, mem_refinementDataHistoryField]
  constructor
  · rintro ⟨alpha, halpha, d, entry, equal⟩
    exact ⟨alpha, halpha, d, (pair_mem_graphRestriction.1 entry).1, equal⟩
  · rintro ⟨alpha, halpha, d, entry, equal⟩
    exact ⟨alpha, halpha, d, pair_mem_graphRestriction.2 ⟨entry, halpha⟩, equal⟩

theorem refinementDataHistoryField_restrict {stages earlier history : ZFSet.{u}}
    (subset : earlier ⊆ stages) (j : Fin 15) :
    refinementDataHistoryField earlier (graphRestriction earlier history) j =
      graphRestriction earlier (refinementDataHistoryField stages history j) := by
  rw [refinementDataHistoryField_history_restrict, refinementDataHistoryField_domain_restrict subset]

theorem refinementDataHistoryField_append {stages history alpha : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (d : Fin 15 → ZFSet.{u}) (j : Fin 15) :
    refinementDataHistoryField (insert alpha stages)
      (insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history) j =
        insert (ZFSet.pair alpha (d j)) (refinementDataHistoryField stages history j) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨beta, _, fields, entry, rfl⟩ := (mem_refinementDataHistoryField _ _ _ _).1 member
    rcases ZFSet.mem_insert_iff.1 entry with equal | old
    · obtain ⟨rfl, code⟩ := ZFSet.pair_inj.1 equal
      have same := refinementFormulaDataCode_injective code
      exact ZFSet.mem_insert_iff.2 (Or.inl (congrArg (ZFSet.pair beta) (congrFun same j)))
    · exact ZFSet.mem_insert_iff.2 (Or.inr
        ((pair_mem_refinementDataHistoryField _ _ _ _ _).2
          ⟨function.pair_source old, fields, old, rfl⟩))
  · intro member
    rcases ZFSet.mem_insert_iff.1 member with rfl | old
    · exact (pair_mem_refinementDataHistoryField _ _ _ _ _).2
        ⟨ZFSet.mem_insert _ _, d, ZFSet.mem_insert _ _, rfl⟩
    · obtain ⟨beta, hbeta, fields, entry, rfl⟩ := (mem_refinementDataHistoryField _ _ _ _).1 old
      exact (pair_mem_refinementDataHistoryField _ _ _ _ _).2
        ⟨ZFSet.mem_insert_of_mem alpha hbeta, fields,
          ZFSet.mem_insert_of_mem _ entry, rfl⟩





theorem refinementHistoryIndices_restrict {alpha beta history : ZFSet.{u}}
    (below : beta ⊆ alpha) :
    refinementHistoryIndices beta (graphRestriction alpha history) =
      refinementHistoryIndices beta history := by
  apply ZFSet.ext
  intro x
  rw [mem_refinementHistoryIndices, mem_refinementHistoryIndices]
  constructor
  · rintro ⟨xi, hxi, I, entry, member⟩
    exact ⟨xi, hxi, I, (pair_mem_graphRestriction.1 entry).1, member⟩
  · rintro ⟨xi, hxi, I, entry, member⟩
    exact ⟨xi, hxi, I, pair_mem_graphRestriction.2 ⟨entry, below hxi⟩, member⟩

theorem refinementHistoryAssignmentCut_restrict {stages alpha beta history : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi)
    (subset : alpha ⊆ stages) (below : beta ⊆ alpha) (T A : ZFSet.{u}) :
    assignmentCut (refinementHistoryAssignmentLevels alpha (graphRestriction alpha history) T) beta A =
      assignmentCut (refinementHistoryAssignmentLevels stages history T) beta A := by
  rw [refinementHistoryAssignmentCut_eq (function.restrict subset)
    (fun xi I entry => literal xi I (pair_mem_graphRestriction.1 entry).1) below]
  rw [refinementHistoryAssignmentCut_eq function literal (fun _ h => subset (below h))]
  rw [refinementHistoryIndices_restrict below]

theorem refinementDataHistoryIndices_prefix {stages alpha beta history : ZFSet.{u}}
    (subset : alpha ⊆ stages) (below : beta ⊆ alpha) :
    refinementHistoryIndices beta
      (refinementDataHistoryField alpha (graphRestriction alpha history) 0) =
        refinementHistoryIndices beta (refinementDataHistoryField stages history 0) := by
  rw [refinementDataHistoryField_restrict subset, refinementHistoryIndices_restrict below]

theorem refinementDataHistoryAssignmentCut_prefix {stages alpha beta history : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (decoded : ∀ xi data, ZFSet.pair xi data ∈ history →
      ∃ d : Fin 15 → ZFSet.{u}, data = refinementFormulaDataCode d)
    (literal : ∀ xi (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair xi (refinementFormulaDataCode d) ∈ history → RefinementIndexLevelCode (d 0) xi)
    (subset : alpha ⊆ stages) (below : beta ⊆ alpha) (T A : ZFSet.{u}) :
    assignmentCut (refinementHistoryAssignmentLevels alpha
      (refinementDataHistoryField alpha (graphRestriction alpha history) 0) T) beta A =
        assignmentCut (refinementHistoryAssignmentLevels stages
          (refinementDataHistoryField stages history 0) T) beta A := by
  rw [refinementDataHistoryField_restrict subset]
  exact refinementHistoryAssignmentCut_restrict
    (refinementDataHistoryField_function function decoded 0)
    (refinementDataHistoryField_index_levels literal) subset below T A

end PartitionPilot.Forcing

end OAI
