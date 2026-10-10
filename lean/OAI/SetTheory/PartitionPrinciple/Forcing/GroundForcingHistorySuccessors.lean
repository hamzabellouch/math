import OAI.SetTheory.PartitionPrinciple.Definability.ForcingHistoryConditionFormulas
import OAI.SetTheory.PartitionPrinciple.Transfinite.FiniteFlatHistoryCoherence

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def stageTwoConditions (rawRowCarrier I levels alpha : ZFSet.{u})
    (d : Fin 15 → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (StageTwoConditionCode M levels alpha d)
    (M.stageOneCandidateBound rawRowCarrier I (d 6))

theorem mem_stageTwoConditions (rawRowCarrier I levels alpha : ZFSet.{u})
    (d : Fin 15 → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ M.stageTwoConditions rawRowCarrier I levels alpha d ↔
      z ∈ M.stageOneCandidateBound rawRowCarrier I (d 6) ∧
        StageTwoConditionCode M levels alpha d z := ZFSet.mem_sep

theorem pair_mem_stageTwoConditions (rawRowCarrier I levels alpha : ZFSet.{u})
    (d : Fin 15 → ZFSet.{u}) (row A : ZFSet.{u}) :
    ZFSet.pair row A ∈ M.stageTwoConditions rawRowCarrier I levels alpha d ↔
      row ∈ rawRowCarrier ∧ A ∈ M.sets ∧ A ⊆ stageOneAssignments I (d 6) ∧
        M.groundEmbeddable A ZFSet.omega ∧
        ZFSet.pair row (assignmentCut levels alpha A) ∈ d 7 ∧
        stageOneRawTests M d A (ZFSet.pair row (assignmentCut levels alpha A)) := by
  rw [M.mem_stageTwoConditions, M.pair_mem_stageOneCandidateBound]
  constructor
  · rintro ⟨⟨hr, hA, subset, small⟩, row', A', equal, lower, tests⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective equal
    exact ⟨hr, hA, subset, small, lower, tests⟩
  · rintro ⟨hr, hA, subset, small, lower, tests⟩
    exact ⟨⟨hr, hA, subset, small⟩, row, A, rfl, lower, tests⟩

theorem stageTwoConditions_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {rawRowCarrier I levels alpha : ZFSet.{u}} (d : Fin 15 → ZFSet.{u})
    (hRow : rawRowCarrier ∈ M.sets) (hI : I ∈ M.sets)
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (members : ∀ j, d j ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.stageTwoConditions rawRowCarrier I levels alpha d ∈ M.sets := by
  have bound := M.stageOneCandidateBound_mem pairing unions powers separation
    hRow hI (members 6) omega
  let params : Fin 17 → ZFSet.{u} := extend levels (extend alpha d)
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hLevels (Fin.cases hAlpha members)
  let phi : SetFormula 18 := stageTwoConditionFormula (fun j => j.succ.succ.succ) 1 2 0
  have selected := M.separation_mem separation phi params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets phi (extend z params))
      (M.stageOneCandidateBound rawRowCarrier I (d 6)) =
      M.stageTwoConditions rawRowCarrier I levels alpha d := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_stageTwoConditions]
    apply and_congr_right
    intro hz
    exact M.realize_stageTwoConditionFormula pairing separation
      (fun j => j.succ.succ.succ) 1 2 0 (extend z params)
      (Fin.cases (M.transitive bound hz) ground)
  exact equal ▸ selected

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (rawRowCarrier I0 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
local notation "I1" => M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid
local notation "levels" => stageTwoAssignmentLevels I0 I1 T
local notation "data" => M.refinementLevelFormulaData a s b d (natSetCode 1) T T2 valid

noncomputable def stageTwoForcing : ZFSet.{u} :=
  M.stageTwoConditions rawRowCarrier (I0 ∪ I1) levels (natSetCode 1) data

theorem stageTwoForcing_raw_entry (row A : ZFSet.{u}) :
    ZFSet.pair row A ∈ M.stageTwoForcing rawRowCarrier I0 a s b d T T2 valid ↔
      row ∈ rawRowCarrier ∧
      A ∈ M.groundSmallSubsets (stageOneAssignments (I0 ∪ I1) T) ZFSet.omega ∧
      ZFSet.pair row (assignmentCut levels (natSetCode 1) A) ∈ s.carrier ∧
      stageOneRawTests M data A (ZFSet.pair row (assignmentCut levels (natSetCode 1) A)) := by
  rw [stageTwoForcing, M.pair_mem_stageTwoConditions, M.mem_groundSmallSubsets]
  exact ⟨fun h => ⟨h.1, ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩,
    fun h => ⟨h.1, h.2.1.1, h.2.1.2.1, h.2.1.2.2, h.2.2⟩⟩

theorem stageTwoForcing_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hRow : rawRowCarrier ∈ M.sets) (hI0 : I0 ∈ M.sets)
    (hT : T ∈ M.sets) (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (valid2 : ∀ z ∈ T2, IsName s z)
    (indices : NiceRefinementIndexSystem M a s b d (natSetCode 1) T T2 valid valid2)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (system : NiceNameSystem M a s b d base directed T valid)
    (omega : ZFSet.omega ∈ M.sets) :
    M.stageTwoForcing rawRowCarrier I0 a s b d T T2 valid ∈ M.sets := by
  have hI1 := indices.index_ground
  have hLevels := M.stageTwoAssignmentLevels_mem pairing unions powers separation hI0 hI1 hT
  have hOne : natSetCode 1 ∈ M.sets := M.transitive omega (natSetCode_mem_omega 1)
  exact M.stageTwoConditions_mem pairing unions powers separation data hRow
    (M.binary_union_mem pairing unions hI0 hI1) hLevels hOne
    (M.refinementLevelFormulaData_members a s b d (natSetCode 1) T T2 valid
      pairing unions powers separation hT carrier order nodes nodeOrder valid2 indices base directed system) omega

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (rawRowCarrier I0 I1 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
local notation "I2" => M.niceRefinementIndices a s b d (natSetCode 2) T T2 valid
local notation "levels" => stageThreeAssignmentLevels I0 I1 I2 T
local notation "data" => M.refinementLevelFormulaData a s b d (natSetCode 2) T T2 valid

noncomputable def stageThreeForcing : ZFSet.{u} :=
  M.stageTwoConditions rawRowCarrier ((I0 ∪ I1) ∪ I2) levels (natSetCode 2) data

theorem stageThreeForcing_raw_entry (row A : ZFSet.{u}) :
    ZFSet.pair row A ∈ M.stageThreeForcing rawRowCarrier I0 I1 a s b d T T2 valid ↔
      row ∈ rawRowCarrier ∧
      A ∈ M.groundSmallSubsets (stageOneAssignments ((I0 ∪ I1) ∪ I2) T) ZFSet.omega ∧
      ZFSet.pair row (assignmentCut levels (natSetCode 2) A) ∈ s.carrier ∧
      stageOneRawTests M data A (ZFSet.pair row (assignmentCut levels (natSetCode 2) A)) := by
  rw [stageThreeForcing, M.pair_mem_stageTwoConditions, M.mem_groundSmallSubsets]
  exact ⟨fun h => ⟨h.1, ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩,
    fun h => ⟨h.1, h.2.1.1, h.2.1.2.1, h.2.1.2.2, h.2.2⟩⟩

theorem stageThreeForcing_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hRow : rawRowCarrier ∈ M.sets) (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets)
    (hT : T ∈ M.sets) (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (valid2 : ∀ z ∈ T2, IsName s z)
    (indices : NiceRefinementIndexSystem M a s b d (natSetCode 2) T T2 valid valid2)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (system : NiceNameSystem M a s b d base directed T valid)
    (omega : ZFSet.omega ∈ M.sets) :
    M.stageThreeForcing rawRowCarrier I0 I1 a s b d T T2 valid ∈ M.sets := by
  have hI2 := indices.index_ground
  have hLevels := M.stageThreeAssignmentLevels_mem pairing unions powers separation hI0 hI1 hI2 hT
  have hTwo : natSetCode 2 ∈ M.sets := M.transitive omega (natSetCode_mem_omega 2)
  exact M.stageTwoConditions_mem pairing unions powers separation data hRow
    (M.binary_union_mem pairing unions (M.binary_union_mem pairing unions hI0 hI1) hI2) hLevels hTwo
    (M.refinementLevelFormulaData_members a s b d (natSetCode 2) T T2 valid
      pairing unions powers separation hT carrier order nodes nodeOrder valid2 indices base directed system) omega

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

theorem stageTwoForcing_empty (rawRowCarrier I0 : ZFSet.{u})
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (hRow : rawRowCarrier ∈ M.sets) {row : ZFSet.{u}} (rowMem : row ∈ rawRowCarrier)
    (lower : ZFSet.pair row ∅ ∈ s.carrier) :
    ZFSet.pair row ∅ ∈ M.stageTwoForcing rawRowCarrier I0 a s b d T T2 valid := by
  apply (M.stageTwoForcing_raw_entry rawRowCarrier I0 a s b d T T2 valid row ∅).2
  have small : (∅ : ZFSet.{u}) ∈ M.groundSmallSubsets
      (stageOneAssignments (I0 ∪ M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T)
      ZFSet.omega :=
    (M.mem_groundSmallSubsets _ _ ∅).2
      ⟨M.empty_mem ⟨rawRowCarrier, hRow⟩, ZFSet.empty_subset _,
        M.empty_groundEmbeddable ZFSet.omega ⟨rawRowCarrier, hRow⟩⟩
  have cut : ∀ levels alpha : ZFSet.{u}, assignmentCut levels alpha ∅ = ∅ := by
    intro levels alpha
    apply ZFSet.ext
    intro z
    rw [mem_assignmentCut]
    exact ⟨fun h => h.1, fun h => False.elim (ZFSet.notMem_empty z h)⟩
  refine ⟨rowMem, small, ?_, ?_⟩
  · rw [cut]
    exact lower
  · constructor
    · intro t ht u hu w hw entry
      exact False.elim (ZFSet.notMem_empty _ entry)
    · intro t ht u hu u' hu' w hw w' hw' entry
      exact False.elim (ZFSet.notMem_empty _ entry)

theorem stageThreeForcing_empty (rawRowCarrier I0 I1 : ZFSet.{u})
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (hRow : rawRowCarrier ∈ M.sets) {row : ZFSet.{u}} (rowMem : row ∈ rawRowCarrier)
    (lower : ZFSet.pair row ∅ ∈ s.carrier) :
    ZFSet.pair row ∅ ∈ M.stageThreeForcing rawRowCarrier I0 I1 a s b d T T2 valid := by
  apply (M.stageThreeForcing_raw_entry rawRowCarrier I0 I1 a s b d T T2 valid row ∅).2
  have small : (∅ : ZFSet.{u}) ∈ M.groundSmallSubsets
      (stageOneAssignments ((I0 ∪ I1) ∪ M.niceRefinementIndices a s b d (natSetCode 2) T T2 valid) T)
      ZFSet.omega :=
    (M.mem_groundSmallSubsets _ _ ∅).2
      ⟨M.empty_mem ⟨rawRowCarrier, hRow⟩, ZFSet.empty_subset _,
        M.empty_groundEmbeddable ZFSet.omega ⟨rawRowCarrier, hRow⟩⟩
  have cut : ∀ levels alpha : ZFSet.{u}, assignmentCut levels alpha ∅ = ∅ := by
    intro levels alpha
    apply ZFSet.ext
    intro z
    rw [mem_assignmentCut]
    exact ⟨fun h => h.1, fun h => False.elim (ZFSet.notMem_empty z h)⟩
  refine ⟨rowMem, small, ?_, ?_⟩
  · rw [cut]
    exact lower
  · constructor
    · intro t ht u hu w hw entry
      exact False.elim (ZFSet.notMem_empty _ entry)
    · intro t ht u hu u' hu' w hw w' hw' entry
      exact False.elim (ZFSet.notMem_empty _ entry)

end

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def forcingHistoryConditions (rows I T stages history levels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (ForcingHistoryConditionCode M stages history levels) (M.stageOneCandidateBound rows I T)

theorem mem_forcingHistoryConditions (rows I T stages history levels z : ZFSet.{u}) :
    z ∈ M.forcingHistoryConditions rows I T stages history levels ↔
      z ∈ M.stageOneCandidateBound rows I T ∧ ForcingHistoryConditionCode M stages history levels z :=
  ZFSet.mem_sep

theorem pair_mem_forcingHistoryConditions (rows I T stages history levels row A : ZFSet.{u}) :
    ZFSet.pair row A ∈ M.forcingHistoryConditions rows I T stages history levels ↔
      row ∈ rows ∧ A ∈ M.sets ∧ A ⊆ stageOneAssignments I T ∧
        M.groundEmbeddable A ZFSet.omega ∧
        ForcingHistoryConditionCode M stages history levels (ZFSet.pair row A) := by
  rw [M.mem_forcingHistoryConditions, M.pair_mem_stageOneCandidateBound]
  exact ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2⟩,
    fun h => ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩⟩

theorem forcingHistoryConditions_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {rows I T stages history levels : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hLevels : levels ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.forcingHistoryConditions rows I T stages history levels ∈ M.sets := by
  have bound := M.stageOneCandidateBound_mem pairing unions powers separation hRows hI hT omega
  let params : Fin 3 → ZFSet.{u} := ![stages, history, levels]
  have ground : ∀ j, params j ∈ M.sets :=
    Fin.cases hStages (Fin.cases hHistory (Fin.cases hLevels (fun j => Fin.elim0 j)))
  have selected := M.separation_mem separation (forcingHistoryConditionFormula 1 2 3 0) params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets (forcingHistoryConditionFormula 1 2 3 0)
      (extend z params)) (M.stageOneCandidateBound rows I T) =
      M.forcingHistoryConditions rows I T stages history levels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_forcingHistoryConditions]
    apply and_congr_right
    intro member
    exact M.realize_forcingHistoryConditionFormula pairing separation 1 2 3 0 (extend z params)
      (Fin.cases (M.transitive bound member) ground)
  exact equal ▸ selected

theorem forcingHistoryConditions_empty (rows I T history levels : ZFSet.{u}) :
    M.forcingHistoryConditions rows I T ∅ history levels = M.stageOneCandidateBound rows I T := by
  apply ZFSet.ext
  intro z
  rw [M.mem_forcingHistoryConditions]
  exact ⟨And.left, fun member => ⟨member, forcingHistoryConditionCode_empty M history levels z⟩⟩

theorem forcingHistoryConditions_initial {rows : ZFSet.{u}} (hRows : rows ∈ M.sets)
    (T history levels : ZFSet.{u}) :
    M.forcingHistoryConditions rows ∅ T ∅ history levels = ZFSet.prod rows {∅} := by
  rw [M.forcingHistoryConditions_empty]
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨row, hrow, A, _, subset, _, rfl⟩ := (M.mem_stageOneCandidateBound _ _ _ _).1 member
    have empty : A = ∅ := by
      apply ZFSet.ext
      intro x
      constructor
      · intro hx
        obtain ⟨t, ht, _, _, _, _, _⟩ := (mem_stageOneAssignments ∅ T x).1 (subset hx)
        exact False.elim (ZFSet.notMem_empty t ht)
      · intro hx
        exact False.elim (ZFSet.notMem_empty x hx)
    exact ZFSet.pair_mem_prod.2 ⟨hrow, ZFSet.mem_singleton.2 empty⟩
  · intro member
    obtain ⟨row, hrow, A, hA, rfl⟩ := ZFSet.mem_prod.1 member
    obtain rfl := ZFSet.mem_singleton.1 hA
    exact M.stageOneCandidateBound_empty hRows hrow

theorem forcingHistoryConditions_restrict {rows I T stages earlier history levels z : ZFSet.{u}}
    (member : z ∈ M.forcingHistoryConditions rows I T stages history levels) (subset : earlier ⊆ stages) :
    z ∈ M.forcingHistoryConditions rows I T earlier (graphRestriction earlier history) levels := by
  obtain ⟨candidate, valid⟩ := (M.mem_forcingHistoryConditions _ _ _ _ _ _ _).1 member
  exact (M.mem_forcingHistoryConditions _ _ _ _ _ _ _).2
    ⟨candidate, forcingHistoryConditionCode_mono valid subset⟩

theorem forcingHistoryConditions_successor_eq
    (rows oldI I alpha history levels : ZFSet.{u}) (d : Fin 15 → ZFSet.{u})
    (function : FunctionGraphOn alpha history) (ordinal : ordinalSetProperty alpha)
    (coverage : ForcingHistoryLevelCoverage alpha history levels)
    (lower : d 7 = M.forcingHistoryConditions rows oldI (d 6) alpha history levels) :
    M.forcingHistoryConditions rows I (d 6) (insert alpha alpha)
      (insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history) levels =
      M.stageTwoConditions rows I levels alpha d := by
  apply ZFSet.ext
  intro z
  rw [M.mem_forcingHistoryConditions, M.mem_stageTwoConditions,
    forcingHistoryConditionCode_insert_iff function (ZFSet.mem_irrefl alpha),
    packedSuccessorConditionCode_code_iff]
  constructor
  · rintro ⟨candidate, _, current⟩
    exact ⟨candidate, current⟩
  · rintro ⟨candidate, current⟩
    obtain ⟨row, A, equal, member, tests⟩ := current
    rw [lower] at member
    have priorCut := ((M.mem_forcingHistoryConditions rows oldI (d 6) alpha history levels _).1 member).2
    have prior := (forcingHistoryConditionCode_ordinalCut_iff M alpha history levels alpha row A
      ordinal (fun _ hx => hx) coverage).1 priorCut
    exact ⟨candidate, equal.symm ▸ prior, row, A, equal, lower.symm ▸ member, tests⟩

theorem forcingHistoryConditions_successor_pair_iff
    (rows oldI I alpha history levels : ZFSet.{u}) (d : Fin 15 → ZFSet.{u})
    (function : FunctionGraphOn alpha history) (ordinal : ordinalSetProperty alpha)
    (coverage : ForcingHistoryLevelCoverage alpha history levels)
    (lower : d 7 = M.forcingHistoryConditions rows oldI (d 6) alpha history levels)
    (row A : ZFSet.{u}) :
    ZFSet.pair row A ∈ M.forcingHistoryConditions rows I (d 6) (insert alpha alpha)
      (insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history) levels ↔
      row ∈ rows ∧ A ∈ M.sets ∧ A ⊆ stageOneAssignments I (d 6) ∧
        M.groundEmbeddable A ZFSet.omega ∧
        ZFSet.pair row (assignmentCut levels alpha A) ∈ d 7 ∧
        stageOneRawTests M d A (ZFSet.pair row (assignmentCut levels alpha A)) := by
  rw [M.forcingHistoryConditions_successor_eq rows oldI I alpha history levels d function ordinal coverage lower]
  exact M.pair_mem_stageTwoConditions rows I levels alpha d row A

end PartitionPilot.Forcing.TransitiveGround

end OAI
