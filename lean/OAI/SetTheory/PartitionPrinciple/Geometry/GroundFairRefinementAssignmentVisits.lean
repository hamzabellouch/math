import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCarrierSequences
import OAI.SetTheory.PartitionPrinciple.Transfinite.FairPreparationBirthPersistence
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRecursiveRowCompleteProjection

namespace OAI

namespace PartitionPilot.Forcing
universe u

theorem fairPreparation_scheduledActiveEvent
    {Q E0 stages U enumSelector prepSelector : ZFSet.{u}}
    (function : ZFSet.IsFunc Q E0 enumSelector)
    (clocks conditions births events enumerations : Nat → ZFSet.{u})
    (enumerationCases : ∀ k, enumerations k = ∅ ∨
      ZFSet.IsFunc ZFSet.omega stages (enumerations k))
    (chosen : ∀ k, ZFSet.pair (conditions k) (enumerations k) ∈ enumSelector)
    (initialClock : clocks 0 = ∅)
    (initialBirths : births 0 = {ZFSet.pair ∅ (enumerations 0)})
    (steps : ∀ k, FairPreparationStepCode ZFSet.omega E0 stages U
      enumSelector prepSelector
      (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv)
      (ZFSet.pair (clocks k) (ZFSet.pair (conditions k) (ZFSet.pair (births k) (events k))))
      (ZFSet.pair (clocks (k + 1))
        (ZFSet.pair (conditions (k + 1)) (ZFSet.pair (births (k + 1)) (events (k + 1))))))
    (i j : Nat) (alpha : ZFSet.{u})
    (entry : ZFSet.pair (natSetCode j) alpha ∈ enumerations i) :
    ∃ y ∈ U,
      (∃ payload, y = ZFSet.pair (conditions (Nat.pair i j + 1)) payload) ∧
      ZFSet.pair (ZFSet.pair alpha (conditions (Nat.pair i j))) y ∈ prepSelector ∧
      events (Nat.pair i j + 1) = ZFSet.pair alpha y := by
  have persistent := fairPreparation_birthPersistence function clocks conditions births events
    enumerations chosen initialClock initialBirths steps (Nat.pair i j)
  obtain ⟨n, p, b, last, m, q, nextBirths, event, source, target, _next,
    oldI, _hi, oldJ, _hj, e, _he, newE, _hNew, grid, old, _selected, _append, branch⟩ :=
    steps (Nat.pair i j)
  obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 source
  obtain ⟨rfl, inner⟩ := ZFSet.pair_inj.1 tail
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
  obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 target
  obtain ⟨rfl, inner⟩ := ZFSet.pair_inj.1 tail
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
  rw [persistent.1] at grid
  have exactGrid : ZFSet.pair (natSetCode (Nat.pair i j))
      (ZFSet.pair (natSetCode i) (natSetCode j)) ∈
      natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv := by
    have edge : ZFSet.pair (natSetCode (Nat.pair i j))
        (ZFSet.pair (natSetCode (Nat.unpair (Nat.pair i j)).1)
          (natSetCode (Nat.unpair (Nat.pair i j)).2)) ∈
        natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv :=
      (natPresentation.pair_mem_graph (natPresentation.product natPresentation)
        omegaGridEquiv ⟨Nat.pair i j⟩ (omegaGridEquiv ⟨Nat.pair i j⟩)).2 rfl
    simpa only [Nat.unpair_pair] using edge
  have gridFunction := natPresentation.graph_isFunc
    (natPresentation.product natPresentation) omegaGridEquiv
  obtain ⟨_, _, gridUnique⟩ := gridFunction.2 _ (natSetCode_mem_omega (Nat.pair i j))
  have sameGrid := (gridUnique _ grid).trans (gridUnique _ exactGrid).symm
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 sameGrid
  have sameEnumeration := ((persistent.2.2.1 i e).1 old).2
  subst e
  have nonempty : enumerations i ≠ ∅ := by
    intro empty
    exact ZFSet.notMem_empty _ (empty ▸ entry)
  rcases branch with idle | active
  · exact False.elim (nonempty idle.1)
  · obtain ⟨level, _hLevel, y, hy, shape, levelEntry, prepared, recorded⟩ := active
    have enumFunction := (enumerationCases i).resolve_left nonempty
    obtain ⟨_, _, unique⟩ := enumFunction.2 _ (natSetCode_mem_omega j)
    have sameLevel := (unique _ levelEntry).trans (unique _ entry).symm
    subst level
    exact ⟨y, hy, shape, prepared, recorded⟩

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {R : Type u} [PartialOrder R]
variable (c : Presentation R) (T stages history : ZFSet.{u})
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "B" => M.groundSmallSubsets
  (stageOneAssignments (refinementDataHistoryIndices stages history) T) ZFSet.omega
local notation "shape" => M.refinementHistoryForcing_shape c.carrier T stages history
local notation "data" => flatCarrierData c Q B shape

theorem refinementHistorySequence_assignment_mono :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    ∀ seq : Nat → SetMembers Q, Antitone seq →
      ∀ i k, i ≤ k → SetMembers.raw (data (seq i)) ⊆ SetMembers.raw (data (seq k)) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  intro seq decreasing i k before
  have below := decreasing before
  change ZFSet.pair (SetMembers.raw (seq k)) (SetMembers.raw (seq i)) ∈
    M.refinementHistoryOrder c.carrier c.conditionOrder T stages history at below
  rw [flatCarrier_coordinates c Q B shape (seq k), flatCarrier_coordinates c Q B shape (seq i)] at below
  exact ((M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages history
    _ _ _ _).1 below).2.2.2

theorem refinementHistorySequence_assignment_visit
    (valid : RefinementDataHistory stages history T) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    ∀ seq : Nat → SetMembers Q, Antitone seq → ∀ enumerations : Nat → ZFSet.{u},
      (∀ i, BirthLevelEnumerationCode ZFSet.omega stages (SetMembers.raw (data (seq i)))
        (refinementDataHistoryLevels stages history T) (enumerations i)) →
      ∀ x ∈ stageOneAssignmentUnion (fun i => SetMembers.raw (data (seq i))),
        ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
          Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
          x ∈ SetMembers.raw (data (seq i)) ∧
          ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history ∧
          ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages history T ∧
          alpha ∈ relationImage (SetMembers.raw (data (seq i))) stages
            (refinementDataHistoryLevels stages history T) ∧
          ZFSet.pair (natSetCode j) alpha ∈ enumerations i ∧
          ∀ k, Nat.pair i j ≤ k →
            x ∈ assignmentOnIndices (fields 0) T (SetMembers.raw (data (seq k))) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  intro seq decreasing enumerations coded x member
  have bounded : ∀ i, SetMembers.raw (data (seq i)) ⊆
      stageOneAssignments (refinementDataHistoryIndices stages history) T := by
    intro i
    exact ((M.mem_groundSmallSubsets _ _ _).1 (SetMembers.raw_mem (data (seq i)))).2.1
  exact valid.birthEnumeration_assignment_visit (fun i => SetMembers.raw (data (seq i))) enumerations
    bounded (M.refinementHistorySequence_assignment_mono c T stages history seq decreasing) coded member

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {R : Type u} [PartialOrder R]
variable (c : Presentation R) (T stages history : ZFSet.{u})
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "B" => M.groundSmallSubsets
  (stageOneAssignments (refinementDataHistoryIndices stages history) T) ZFSet.omega
local notation "shape" => M.refinementHistoryForcing_shape c.carrier T stages history
local notation "data" => flatCarrierData c Q B shape

theorem fairRefinementSequence_assignment_prepared
    (valid : RefinementDataHistory stages history T)
    {E0 U enumSelector prepSelector : ZFSet.{u}}
    (function : ZFSet.IsFunc Q E0 enumSelector)
    (selected : enumSelector ⊆ M.birthLevelEnumerationRelation Q stages
      (refinementDataHistoryLevels stages history T)) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    ∀ (seq : Nat → SetMembers Q), Antitone seq →
    ∀ (clocks births events : Nat → ZFSet.{u}) (initialE : ZFSet.{u}),
    ZFSet.pair (SetMembers.raw (seq 0)) initialE ∈ enumSelector →
    clocks 0 = ∅ → births 0 = {ZFSet.pair ∅ initialE} →
    (∀ k, FairPreparationStepCode ZFSet.omega E0 stages U enumSelector prepSelector
      (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv)
      (ZFSet.pair (clocks k) (ZFSet.pair (SetMembers.raw (seq k))
        (ZFSet.pair (births k) (events k))))
      (ZFSet.pair (clocks (k + 1)) (ZFSet.pair (SetMembers.raw (seq (k + 1)))
        (ZFSet.pair (births (k + 1)) (events (k + 1)))))) →
    ∀ x ∈ stageOneAssignmentUnion (fun i => SetMembers.raw (data (seq i))),
      ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
        Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
        x ∈ SetMembers.raw (data (seq i)) ∧
        ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history ∧
        ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages history T ∧
        (∀ k, Nat.pair i j ≤ k →
          x ∈ assignmentOnIndices (fields 0) T (SetMembers.raw (data (seq k)))) ∧
        ∃ y ∈ U, ∃ payload,
          y = ZFSet.pair (SetMembers.raw (seq (Nat.pair i j + 1))) payload ∧
          ZFSet.pair (ZFSet.pair alpha (SetMembers.raw (seq (Nat.pair i j)))) y ∈ prepSelector ∧
          events (Nat.pair i j + 1) = ZFSet.pair alpha y := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  intro seq decreasing clocks births events initialE initialChosen initialClock initialBirths steps x member
  have available (k : Nat) : ∃ e, ZFSet.pair (SetMembers.raw (seq k)) e ∈ enumSelector := by
    obtain ⟨e, edge, _⟩ := function.2 _ (SetMembers.raw_mem (seq k))
    exact ⟨e, edge⟩
  choose enumerations chosen using available
  have codes (k : Nat) : BirthLevelEnumerationCode ZFSet.omega stages
      (SetMembers.raw (data (seq k))) (refinementDataHistoryLevels stages history T) (enumerations k) := by
    have entry := selected (chosen k)
    rw [flatCarrier_coordinates c Q B shape (seq k)] at entry
    exact ((M.pair_mem_birthLevelEnumerationRelation _ _ _ _ _ _).1 entry).2.2
  have enumerationCases (k : Nat) : enumerations k = ∅ ∨ ZFSet.IsFunc ZFSet.omega stages (enumerations k) :=
    (codes k).elim (fun idle => Or.inl idle.2) (fun active => Or.inr active.1)
  have initialSame : initialE = enumerations 0 := by
    obtain ⟨_, _, unique⟩ := function.2 _ (SetMembers.raw_mem (seq 0))
    exact (unique _ initialChosen).trans (unique _ (chosen 0)).symm
  have initialTable : births 0 = {ZFSet.pair ∅ (enumerations 0)} := by
    rw [← initialSame]
    exact initialBirths
  obtain ⟨i, j, alpha, hAlpha, fields, grid, before, born, stored, level, _attained, enumerated, retained⟩ :=
    M.refinementHistorySequence_assignment_visit c T stages history valid seq decreasing
      enumerations codes x member
  obtain ⟨y, hy, ⟨payload, output⟩, edge, event⟩ :=
    fairPreparation_scheduledActiveEvent function clocks (fun k => SetMembers.raw (seq k)) births events
      enumerations enumerationCases chosen initialClock initialTable steps i j alpha enumerated
  exact ⟨i, j, alpha, hAlpha, fields, grid, before, born, stored, level, retained,
    y, hy, payload, output, edge, event⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
