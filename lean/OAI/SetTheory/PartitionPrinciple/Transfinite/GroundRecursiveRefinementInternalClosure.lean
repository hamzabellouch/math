import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCarrierSequences
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRecursiveRowCompleteProjection

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R : Type u} [PartialOrder R]
variable (c : Presentation R) (T stages history : ZFSet.{u})
variable (run : RecursiveRefinementOrderHistory M c.carrier c.conditionOrder T stages history)
variable (ordinal : ordinalSetProperty stages)
variable (unionTests : ∀ beta (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
  ∀ (family lower : Nat → ZFSet.{u}) q,
    (∀ n m, n ≤ m → family n ⊆ family m) →
    (∀ n, ZFSet.pair q (lower n) ∈ d 8) →
    (∀ n, stageOneRawTests M d (family n) (lower n)) →
    stageOneRawTests M d (stageOneAssignmentUnion family) q)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (carrier : c.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
variable (rowClosed : InternallyCountablyClosed M c)
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "J" => stageOneAssignments (refinementDataHistoryIndices stages history) T
local notation "B" => M.groundSmallSubsets J ZFSet.omega
local notation "shape" => M.refinementHistoryForcing_shape c.carrier T stages history
local notation "row" => flatCarrierRow c Q B shape
local notation "data" => flatCarrierData c Q B shape
include run ordinal unionTests pairing unions powers separation infinite choice carrier hT hStages hHistory rowClosed

theorem refinementHistory_lower_bound :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    ∀ seq : Nat → SetMembers Q, groundSequenceGraph seq ∈ M.sets → Antitone seq →
      ∃ q : R, (∀ n, q ≤ row (seq n)) ∧ ∃ p : SetMembers Q,
        SetMembers.raw p = ZFSet.pair (c.encode q)
          (stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n)))) ∧ ∀ n, p ≤ seq n := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  intro seq whole decreasing
  have omega := M.omega_mem separation infinite
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hStages hHistory omega
  have hJ := M.stageOneAssignments_mem pairing unions powers separation
    (M.refinementDataHistoryIndices_mem pairing unions powers separation hStages hHistory) hT
  have hB := M.groundSmallSubsets_mem powers separation hJ omega
  obtain ⟨rowGround, dataGround⟩ := M.flatCarrierSequence_projections_ground c Q B shape
    pairing unions powers separation hQ carrier hB omega seq whole
  have comparisons {n m : Nat} (less : n ≤ m) :
      row (seq m) ≤ row (seq n) ∧ SetMembers.raw (data (seq n)) ⊆ SetMembers.raw (data (seq m)) := by
    have below := decreasing less
    change ZFSet.pair (SetMembers.raw (seq m)) (SetMembers.raw (seq n)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages history at below
    rw [flatCarrier_coordinates c Q B shape (seq m), flatCarrier_coordinates c Q B shape (seq n)] at below
    have checked := (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages history _ _ _ _).1 below
    exact ⟨(c.pair_mem_conditionOrder _ _).1 checked.2.2.1, checked.2.2.2⟩
  obtain ⟨q, belowRows⟩ := rowClosed (fun n => row (seq n)) rowGround (fun _ _ less => (comparisons less).1)
  have small := M.groundSmallSubset_union_mem pairing unions powers separation infinite choice hJ
    (fun n => data (seq n)) dataGround
  have candidate : ZFSet.pair (c.encode q)
      (stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n)))) ∈
      M.stageOneCandidateBound c.carrier (refinementDataHistoryIndices stages history) T :=
    ZFSet.pair_mem_prod.2 ⟨c.encode_mem q, small⟩
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT
  have members (n : Nat) : ZFSet.pair (c.encode (row (seq n))) (SetMembers.raw (data (seq n))) ∈ Q := by
    rw [← flatCarrier_coordinates c Q B shape (seq n)]
    exact SetMembers.raw_mem (seq n)
  obtain ⟨member, below⟩ := run.union_lower_bound_of_candidates ordinal unionTests
    (fun n => SetMembers.raw (data (seq n))) (fun n => c.encode (row (seq n))) (c.encode q)
    members (fun _ _ less => (comparisons less).2)
    (fun n => (c.pair_mem_conditionOrder _ _).2 (belowRows n)) candidate (by
      intro gamma hgamma
      exact M.refinementDataHistoryCandidate_cut separation run.carriers.data (ordinal.1 gamma hgamma)
        hLevels (M.transitive hStages hgamma) omega candidate)
  let p : SetMembers Q := SetMembers.ofMem _ member
  have code : SetMembers.raw p = ZFSet.pair (c.encode q)
      (stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n)))) := SetMembers.raw_ofMem _ _
  refine ⟨q, belowRows, p, code, ?_⟩
  intro n
  change ZFSet.pair (SetMembers.raw p) (SetMembers.raw (seq n)) ∈
    M.refinementHistoryOrder c.carrier c.conditionOrder T stages history
  rw [code, flatCarrier_coordinates c Q B shape (seq n)]
  exact below n

theorem refinementHistory_internally_closed :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    InternallyCountablyClosed M (SetMembers.presentation Q) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  intro seq whole decreasing
  obtain ⟨_, _, p, _, below⟩ := M.refinementHistory_lower_bound c T stages history run ordinal unionTests
    pairing unions powers separation infinite choice carrier hT hStages hHistory rowClosed seq whole decreasing
  exact ⟨p, below⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
