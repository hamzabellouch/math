import OAI.SetTheory.PartitionPrinciple.Forcing.GroundForcingHistoryLimitConnection
import OAI.SetTheory.PartitionPrinciple.Transfinite.RefinementBirthSchedules

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

def BirthLevelEnumerationCode (omega stages A levels e : ZFSet.{u}) : Prop :=
  (relationImage A stages levels = ∅ ∧ e = ∅) ∨
    (ZFSet.IsFunc omega stages e ∧ ∀ alpha ∈ stages,
      (∃ n ∈ omega, ZFSet.pair n alpha ∈ e) ↔
        ∃ x ∈ A, ZFSet.pair x alpha ∈ levels)

theorem BirthLevelEnumerationCode.enumerates {omega stages A levels e : ZFSet.{u}}
    (code : BirthLevelEnumerationCode omega stages A levels e)
    (active : (relationImage A stages levels).Nonempty) :
    ZFSet.IsFunc omega (relationImage A stages levels) e ∧
      ∀ alpha ∈ relationImage A stages levels, ∃ n ∈ omega, ZFSet.pair n alpha ∈ e := by
  rcases code with ⟨empty, _⟩ | ⟨function, range⟩
  · obtain ⟨alpha, ha⟩ := active
    exact False.elim (ZFSet.notMem_empty alpha (empty ▸ ha))
  · refine ⟨⟨?_, function.2⟩, ?_⟩
    · intro z hz
      obtain ⟨n, hn, alpha, ha, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨hn,
        (mem_relationImage A stages levels alpha).2 ⟨ha, (range alpha ha).1 ⟨n, hn, hz⟩⟩⟩
    · intro alpha ha
      obtain ⟨hs, witness⟩ := (mem_relationImage A stages levels alpha).1 ha
      exact (range alpha hs).2 witness

theorem BirthLevelEnumerationCode.idle {omega stages A levels e : ZFSet.{u}}
    (code : BirthLevelEnumerationCode omega stages A levels e)
    (nonempty : omega.Nonempty) (empty : relationImage A stages levels = ∅) : e = ∅ := by
  rcases code with ⟨_, idle⟩ | ⟨function, range⟩
  · exact idle
  · obtain ⟨n, hn⟩ := nonempty
    obtain ⟨alpha, edge, _⟩ := function.2 n hn
    have ha := (ZFSet.pair_mem_prod.1 (function.1 edge)).2
    have attained := (mem_relationImage A stages levels alpha).2
      ⟨ha, (range alpha ha).1 ⟨n, hn, edge⟩⟩
    exact False.elim (ZFSet.notMem_empty alpha (empty ▸ attained))

namespace BoundedFormula
open SetFormula

def birthLevelEnumerationFormula {n} (omega stages A levels e : Fin n) : BoundedFormula n :=
  disj (.conj (.allMem A (.allMem stages.succ
      (.neg (pairMembershipFormula 1 0 levels.succ.succ)))) (emptyFormula e))
    (.conj (functionFormula omega stages e)
      (.allMem stages (.conj
        (imp (exMem omega.succ (pairMembershipFormula 0 1 e.succ.succ))
          (exMem A.succ (pairMembershipFormula 0 1 levels.succ.succ)))
        (imp (exMem A.succ (pairMembershipFormula 0 1 levels.succ.succ))
          (exMem omega.succ (pairMembershipFormula 0 1 e.succ.succ))))))

theorem truth_birthLevelEnumerationFormula {n} (omega stages A levels e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (birthLevelEnumerationFormula omega stages A levels e) env ↔
      BirthLevelEnumerationCode (env omega) (env stages) (env A) (env levels) (env e) := by
  simp only [birthLevelEnumerationFormula, truth_disj, Truth, truth_emptyFormula,
    truth_functionFormula, truth_imp, truth_exMem, truth_pairMembershipFormula, ← iff_def]
  change (((∀ x ∈ env A, ∀ alpha ∈ env stages, ¬ ZFSet.pair x alpha ∈ env levels) ∧
    env e = ∅) ∨ (ZFSet.IsFunc (env omega) (env stages) (env e) ∧
    ∀ alpha ∈ env stages, (∃ k ∈ env omega, ZFSet.pair k alpha ∈ env e) ↔
      ∃ x ∈ env A, ZFSet.pair x alpha ∈ env levels)) ↔ _
  have empty : (∀ x ∈ env A, ∀ alpha ∈ env stages, ¬ ZFSet.pair x alpha ∈ env levels) ↔
      relationImage (env A) (env stages) (env levels) = ∅ := by
    constructor
    · intro no
      apply ZFSet.ext
      intro alpha
      simp only [mem_relationImage, ZFSet.notMem_empty, iff_false]
      rintro ⟨ha, x, hx, edge⟩
      exact no x hx alpha ha edge
    · intro eq x hx alpha ha edge
      have member := (mem_relationImage (env A) (env stages) (env levels) alpha).2
        ⟨ha, x, hx, edge⟩
      exact ZFSet.notMem_empty alpha (eq ▸ member)
  exact or_congr (and_congr empty Iff.rfl) Iff.rfl

def birthLevelEnumerationEntryFormula {n} (entry omega stages levels : Fin n) : BoundedFormula n :=
  exPairFields entry (exPairFields 1
    (birthLevelEnumerationFormula omega.succ.succ.succ.succ
      stages.succ.succ.succ.succ 0 levels.succ.succ.succ.succ 2))

theorem truth_birthLevelEnumerationEntryFormula {n} (entry omega stages levels : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (birthLevelEnumerationEntryFormula entry omega stages levels) env ↔
      ∃ row A e, env entry = ZFSet.pair (ZFSet.pair row A) e ∧
        BirthLevelEnumerationCode (env omega) (env stages) A (env levels) e := by
  simp only [birthLevelEnumerationEntryFormula, truth_exPairFields,
    truth_birthLevelEnumerationFormula]
  change (∃ p e, env entry = ZFSet.pair p e ∧ ∃ row A, p = ZFSet.pair row A ∧
    BirthLevelEnumerationCode (env omega) (env stages) A (env levels) e) ↔ _
  constructor
  · rintro ⟨p, e, eq, row, A, rfl, code⟩
    exact ⟨row, A, e, eq, code⟩
  · rintro ⟨row, A, e, eq, code⟩
    exact ⟨_, e, eq, row, A, rfl, code⟩

end BoundedFormula

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def refinementHistoryForcing (rows T stages history : ZFSet.{u}) : ZFSet.{u} :=
  M.forcingHistoryConditions rows (refinementDataHistoryIndices stages history) T stages history
    (refinementDataHistoryLevels stages history T)

theorem mem_refinementHistoryForcing (rows T stages history z : ZFSet.{u}) :
    z ∈ M.refinementHistoryForcing rows T stages history ↔
      z ∈ M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T ∧
        ForcingHistoryConditionCode M stages history (refinementDataHistoryLevels stages history T) z :=
  M.mem_forcingHistoryConditions _ _ _ _ _ _ _

theorem refinementHistoryForcing_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {rows T stages history : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hT : T ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.refinementHistoryForcing rows T stages history ∈ M.sets :=
  M.forcingHistoryConditions_mem pairing unions powers separation hRows
    (M.refinementDataHistoryIndices_mem pairing unions powers separation hStages hHistory) hT
    hStages hHistory (M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT) omega

theorem refinementHistoryForcing_initial {rows : ZFSet.{u}} (hRows : rows ∈ M.sets)
    (T history : ZFSet.{u}) : M.refinementHistoryForcing rows T ∅ history = ZFSet.prod rows {∅} := by
  have indices : refinementDataHistoryIndices ∅ history = ∅ := by
    apply ZFSet.ext
    intro x
    constructor
    · intro member
      obtain ⟨alpha, impossible, _⟩ := (mem_refinementHistoryIndices ∅ _ x).1 member
      exact False.elim (ZFSet.notMem_empty alpha impossible)
    · intro member
      exact False.elim (ZFSet.notMem_empty x member)
  rw [refinementHistoryForcing, indices]
  exact M.forcingHistoryConditions_initial hRows T history _

theorem refinementHistoryForcing_level_function {stages history T : ZFSet.{u}}
    (valid : RefinementDataHistory stages history T) :
    ZFSet.IsFunc (stageOneAssignments (refinementDataHistoryIndices stages history) T) stages
      (refinementDataHistoryLevels stages history T) :=
  valid.levels_function

theorem refinementHistoryForcing_pair_decomposition {stages history T : ZFSet.{u}}
    (valid : RefinementDataHistory stages history T) (rows row A : ZFSet.{u}) :
    ZFSet.pair row A ∈ M.refinementHistoryForcing rows T stages history ↔
      ZFSet.pair row A ∈ M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T ∧
        FlatHistoryCuts stages (refinementDataHistoryField stages history 7)
          (refinementDataHistoryLevels stages history T) row A ∧
        ∀ beta ∈ stages, forcingHistoryRawTests M history
          (refinementDataHistoryLevels stages history T) beta row A := by
  rw [M.mem_refinementHistoryForcing]
  exact and_congr Iff.rfl (forcingHistoryConditionCode_pair_decomposition valid.function valid.decoded row A)

noncomputable def birthLevelEnumerationRelation (Q stages levels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ row A e, z = ZFSet.pair (ZFSet.pair row A) e ∧
    BirthLevelEnumerationCode ZFSet.omega stages A levels e)
    (ZFSet.prod Q (M.groundRelations ZFSet.omega stages))

theorem pair_mem_birthLevelEnumerationRelation (Q stages levels row A e : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair row A) e ∈ M.birthLevelEnumerationRelation Q stages levels ↔
      ZFSet.pair row A ∈ Q ∧ e ∈ M.groundRelations ZFSet.omega stages ∧
        BirthLevelEnumerationCode ZFSet.omega stages A levels e := by
  rw [birthLevelEnumerationRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hp, he⟩, row', A', e', equal, code⟩
    obtain ⟨pair, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 pair
    exact ⟨hp, he, code⟩
  · rintro ⟨hp, he, code⟩
    exact ⟨⟨hp, he⟩, row, A, e, rfl, code⟩

theorem birthLevelEnumerationRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q stages levels : ZFSet.{u}} (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets)
    (hLevels : levels ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.birthLevelEnumerationRelation Q stages levels ∈ M.sets := by
  let params := extend ZFSet.omega (extend stages (extend levels Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.birthLevelEnumerationEntryFormula 0 1 2 3) params
    (Fin.cases omega (Fin.cases hStages (Fin.cases hLevels (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hQ
      (M.groundRelations_mem pairing unions powers separation omega hStages))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.birthLevelEnumerationEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod Q (M.groundRelations ZFSet.omega stages)) =
      M.birthLevelEnumerationRelation Q stages levels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, birthLevelEnumerationRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_birthLevelEnumerationEntryFormula 0 1 2 3 _)
  exact equal ▸ selected

theorem exists_refinementBirthLevelEnumerations
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows T stages history : ZFSet.{u}} (hRows : rows ∈ M.sets) (hT : T ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (valid : RefinementDataHistory stages history T) :
    let Q := M.refinementHistoryForcing rows T stages history
    let levels := refinementDataHistoryLevels stages history T
    M.birthLevelEnumerationRelation Q stages levels ∈ M.sets ∧
      ∃ selector ∈ M.sets, ZFSet.IsFunc Q (M.groundRelations ZFSet.omega stages) selector ∧
        selector ⊆ M.birthLevelEnumerationRelation Q stages levels ∧
        ∀ row A e, ZFSet.pair (ZFSet.pair row A) e ∈ selector →
          BirthLevelEnumerationCode ZFSet.omega stages A levels e := by
  classical
  dsimp only
  let Q := M.refinementHistoryForcing rows T stages history
  let levels := refinementDataHistoryLevels stages history T
  have omega := M.omega_mem separation infinite
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hStages hHistory omega
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT
  have bound := M.groundRelations_mem pairing unions powers separation omega hStages
  have ground := M.birthLevelEnumerationRelation_mem pairing unions powers separation hQ hStages hLevels omega
  have total : ∀ p ∈ Q, ∃ e ∈ M.groundRelations ZFSet.omega stages,
      ZFSet.pair p e ∈ M.birthLevelEnumerationRelation Q stages levels := by
    intro p hp
    have candidate := ((M.mem_refinementHistoryForcing rows T stages history p).1 hp).1
    obtain ⟨row, _, A, hA, _, smallA, rfl⟩ := (M.mem_stageOneCandidateBound _ _ _ p).1 candidate
    have hAttained := M.relationImage_mem separation hA hStages hLevels
    have small := M.groundEmbeddable_function_image pairing unions powers separation choice
      hA hStages omega hLevels valid.levels_function smallA
    by_cases active : (relationImage A stages levels).Nonempty
    · obtain ⟨e, he, function, onto⟩ := M.groundCountable_enumeration
        pairing unions powers separation infinite hAttained active small
      have upperFunction : ZFSet.IsFunc ZFSet.omega stages e := by
        refine ⟨?_, function.2⟩
        intro z hz
        obtain ⟨n, hn, alpha, ha, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
        exact ZFSet.pair_mem_prod.2 ⟨hn, ((mem_relationImage A stages levels alpha).1 ha).1⟩
      have heBound := (M.mem_groundRelations ZFSet.omega stages e).2 ⟨he, upperFunction.1⟩
      refine ⟨e, heBound, (M.pair_mem_birthLevelEnumerationRelation Q stages levels row A e).2
        ⟨hp, heBound, Or.inr ⟨upperFunction, ?_⟩⟩⟩
      intro alpha ha
      constructor
      · rintro ⟨n, _, edge⟩
        exact ((mem_relationImage A stages levels alpha).1
          (ZFSet.pair_mem_prod.1 (function.1 edge)).2).2
      · intro witness
        exact onto alpha ((mem_relationImage A stages levels alpha).2 ⟨ha, witness⟩)
    · have empty : relationImage A stages levels = ∅ := by
        apply ZFSet.ext
        intro alpha
        exact ⟨fun ha => False.elim (active ⟨alpha, ha⟩),
          fun ha => False.elim (ZFSet.notMem_empty alpha ha)⟩
      have emptyBound := (M.mem_groundRelations ZFSet.omega stages ∅).2
        ⟨M.empty_mem ⟨stages, hStages⟩, ZFSet.empty_subset _⟩
      exact ⟨∅, emptyBound, (M.pair_mem_birthLevelEnumerationRelation Q stages levels row A ∅).2
        ⟨hp, emptyBound, Or.inl ⟨empty, rfl⟩⟩⟩
  obtain ⟨selector, hs, function, selected⟩ :=
    M.uniformize_relation pairing unions powers separation choice hQ bound ground total
  exact ⟨ground, selector, hs, function, selected, fun row A e entry =>
    ((M.pair_mem_birthLevelEnumerationRelation Q stages levels row A e).1 (selected entry)).2.2⟩

end TransitiveGround

section
universe u

theorem refinementDataHistoryIndices_subset {stages alpha history : ZFSet.{u}}
    (subset : alpha ⊆ stages) :
    refinementDataHistoryIndices alpha (graphRestriction alpha history) ⊆
      refinementDataHistoryIndices stages history := by
  change refinementHistoryIndices alpha
    (refinementDataHistoryField alpha (graphRestriction alpha history) 0) ⊆ _
  rw [refinementDataHistoryIndices_prefix subset (fun _ h => h)]
  exact refinementHistoryIndices_mono subset

theorem refinementDataHistoryAssignments_subset {stages alpha history : ZFSet.{u}}
    (subset : alpha ⊆ stages) (T : ZFSet.{u}) :
    stageOneAssignments (refinementDataHistoryIndices alpha (graphRestriction alpha history)) T ⊆
      stageOneAssignments (refinementDataHistoryIndices stages history) T := by
  intro z member
  obtain ⟨t, ht, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments _ _ z).1 member
  exact (mem_stageOneAssignments _ _ _).2
    ⟨t, refinementDataHistoryIndices_subset subset ht, u, hu, w, hw, rfl⟩

theorem RefinementDataHistory.prefix_assignments_cut {stages history T alpha A : ZFSet.{u}}
    (valid : RefinementDataHistory stages history T) (subset : alpha ⊆ stages)
    (data : A ⊆ stageOneAssignments (refinementDataHistoryIndices alpha (graphRestriction alpha history)) T) :
    assignmentCut (refinementDataHistoryLevels stages history T) alpha A = A := by
  rw [← valid.prefix_cut subset (fun _ h => h) A]
  exact assignmentCut_full (valid.restrict subset).levels_function data

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem refinementDataHistoryCandidate_prefix {stages history rows T alpha row A : ZFSet.{u}}
    (subset : alpha ⊆ stages)
    (candidate : ZFSet.pair row A ∈ M.stageOneCandidateBound rows
      (refinementDataHistoryIndices alpha (graphRestriction alpha history)) T) :
    ZFSet.pair row A ∈ M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T := by
  obtain ⟨hrow, ground, data, small⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate
  exact (M.pair_mem_stageOneCandidateBound _ _ _ _ _).2
    ⟨hrow, ground, fun _ h => refinementDataHistoryAssignments_subset subset T (data h), small⟩

theorem refinementDataHistoryCandidate_cut (separation : SeparationSchema M.sets)
    {stages history rows T alpha row A : ZFSet.{u}}
    (valid : RefinementDataHistory stages history T) (subset : alpha ⊆ stages)
    (hLevels : refinementDataHistoryLevels stages history T ∈ M.sets)
    (hAlpha : alpha ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (candidate : ZFSet.pair row A ∈ M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T) :
    ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages history T) alpha A) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices alpha (graphRestriction alpha history)) T := by
  have checked := M.refinementHistoryCandidate_cut separation valid.index_function valid.index_literal
    subset hLevels hAlpha omega candidate
  change ZFSet.pair row _ ∈ M.stageOneCandidateBound rows
    (refinementHistoryIndices alpha (refinementDataHistoryField alpha (graphRestriction alpha history) 0)) T
  rw [refinementDataHistoryIndices_prefix subset (fun _ h => h)]
  exact checked

theorem refinementDataHistoryCandidate_splice
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {stages history rows T alpha q Aq p Ap : ZFSet.{u}}
    (subset : alpha ⊆ stages) (hLevels : refinementDataHistoryLevels stages history T ∈ M.sets)
    (hAlpha : alpha ∈ M.sets)
    (lower : ZFSet.pair q Aq ∈ M.stageOneCandidateBound rows
      (refinementDataHistoryIndices alpha (graphRestriction alpha history)) T)
    (upper : ZFSet.pair p Ap ∈ M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T) :
    ZFSet.pair q (assignmentSplice (refinementDataHistoryLevels stages history T) alpha Aq Ap) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T := by
  have first := ZFSet.pair_mem_prod.1 (M.refinementDataHistoryCandidate_prefix subset lower)
  have second := ZFSet.pair_mem_prod.1 upper
  exact ZFSet.pair_mem_prod.2 ⟨first.1,
    M.assignmentSplice_mem_groundSmallSubsets pairing unions powers separation infinite choice
      hLevels hAlpha first.2 second.2⟩

end TransitiveGround

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem birthEnumerationRange_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q stages levels selector : ZFSet.{u}} (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (hSelector : selector ∈ M.sets)
    (function : ZFSet.IsFunc Q (M.groundRelations ZFSet.omega stages) selector)
    (selected : selector ⊆ M.birthLevelEnumerationRelation Q stages levels) :
    let E0 := relationImage Q (M.groundRelations ZFSet.omega stages) selector
    E0 ∈ M.sets ∧ E0 ⊆ M.groundRelations ZFSet.omega stages ∧
      (∀ e ∈ E0, e = ∅ ∨ ZFSet.IsFunc ZFSet.omega stages e) ∧
      ∀ row A, ZFSet.pair row A ∈ Q →
        ∃ e ∈ E0, ZFSet.pair (ZFSet.pair row A) e ∈ selector ∧
          BirthLevelEnumerationCode ZFSet.omega stages A levels e := by
  dsimp only
  refine ⟨M.relationImage_mem separation hQ
    (M.groundRelations_mem pairing unions powers separation omega hStages) hSelector,
    fun e he => ((mem_relationImage _ _ _ e).1 he).1, ?_, ?_⟩
  · intro e he
    obtain ⟨_, p, _, edge⟩ := (mem_relationImage _ _ _ e).1 he
    have member := selected edge
    obtain ⟨_, row, A, e', equal, code⟩ := ZFSet.mem_sep.1 member
    obtain ⟨_, rfl⟩ := ZFSet.pair_inj.1 equal
    exact code.elim (fun idle => Or.inl idle.2) (fun active => Or.inr active.1)
  · intro row A hp
    obtain ⟨e, edge, _⟩ := function.2 _ hp
    have bound := (ZFSet.pair_mem_prod.1 (function.1 edge)).2
    exact ⟨e, (mem_relationImage _ _ _ e).2 ⟨bound, _, hp, edge⟩, edge,
      ((M.pair_mem_birthLevelEnumerationRelation Q stages levels row A e).1 (selected edge)).2.2⟩

end TransitiveGround

namespace RefinementDataHistory
universe u
variable {stages history T : ZFSet.{u}} (valid : RefinementDataHistory stages history T)
include valid

theorem birthEnumeration_idle_iff {A e : ZFSet.{u}}
    (shape : A ⊆ stageOneAssignments (refinementDataHistoryIndices stages history) T)
    (code : BirthLevelEnumerationCode ZFSet.omega stages A
      (refinementDataHistoryLevels stages history T) e) : e = ∅ ↔ A = ∅ := by
  constructor
  · intro idle
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      obtain ⟨alpha, edge, _⟩ := valid.levels_function.2 x (shape hx)
      have hAlpha := (ZFSet.pair_mem_prod.1 (valid.levels_function.1 edge)).2
      have attained := (mem_relationImage A stages _ alpha).2 ⟨hAlpha, x, hx, edge⟩
      obtain ⟨n, _, scheduled⟩ := (code.enumerates ⟨alpha, attained⟩).2 alpha attained
      exact False.elim (ZFSet.notMem_empty _ (idle ▸ scheduled))
    · intro hx
      exact False.elim (ZFSet.notMem_empty x hx)
  · intro empty
    have emptyLevels : relationImage A stages (refinementDataHistoryLevels stages history T) = ∅ := by
      apply ZFSet.ext
      intro alpha
      constructor
      · intro ha
        obtain ⟨_, x, hx, _⟩ := (mem_relationImage _ _ _ _).1 ha
        exact False.elim (ZFSet.notMem_empty x (empty ▸ hx))
      · intro ha
        exact False.elim (ZFSet.notMem_empty alpha ha)
    exact code.idle ⟨natSetCode 0, natSetCode_mem_omega 0⟩ emptyLevels

theorem birthEnumeration_assignment_visit (assignments enumerations : Nat → ZFSet.{u})
    (shape : ∀ i, assignments i ⊆ stageOneAssignments (refinementDataHistoryIndices stages history) T)
    (retained : ∀ i k, i ≤ k → assignments i ⊆ assignments k)
    (coded : ∀ i, BirthLevelEnumerationCode ZFSet.omega stages (assignments i)
      (refinementDataHistoryLevels stages history T) (enumerations i))
    {x : ZFSet.{u}} (member : x ∈ stageOneAssignmentUnion assignments) :
    ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
      Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
      x ∈ assignments i ∧
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history ∧
      ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages history T ∧
      alpha ∈ relationImage (assignments i) stages (refinementDataHistoryLevels stages history T) ∧
      ZFSet.pair (natSetCode j) alpha ∈ enumerations i ∧
      ∀ k, Nat.pair i j ≤ k → x ∈ assignmentOnIndices (fields 0) T (assignments k) := by
  have onto : ∀ i alpha,
      alpha ∈ relationImage (assignments i) stages (refinementDataHistoryLevels stages history T) →
      ∃ j : Nat, ZFSet.pair (natSetCode j) alpha ∈ enumerations i := by
    intro i alpha attained
    obtain ⟨n, hn, entry⟩ := ((coded i).enumerates ⟨alpha, attained⟩).2 alpha attained
    obtain ⟨j, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    exact ⟨j, entry⟩
  obtain ⟨i, j, alpha, hAlpha, fields, scheduled, before, born, stored,
      level, attained, enumeration, visited⟩ :=
    valid.birthList_assignment_visit assignments enumerations shape retained onto member
  refine ⟨i, j, alpha, hAlpha, fields, scheduled, before, born, stored,
    level, attained, enumeration, ?_⟩
  intro k after
  have parts := (mem_assignmentOnIndices _ _ _ _).1 visited
  exact (mem_assignmentOnIndices _ _ _ _).2
    ⟨retained (Nat.pair i j) k after parts.1, parts.2⟩

end RefinementDataHistory

end PartitionPilot.Forcing

end OAI
