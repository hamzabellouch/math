import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRecursiveRowNameActions
import OAI.SetTheory.PartitionPrinciple.Forcing.RecursiveRefinementUnionConditions

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization
universe u
namespace RecursiveRefinementDataHistory
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history top : ZFSet.{u}}

theorem greatest (run : RecursiveRefinementDataHistory M rows T stages history)
    (ordinal : ordinalSetProperty stages) (hRows : rows ∈ M.sets)
    (topMem : top ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder) :
    ∀ z ∈ M.refinementHistoryForcing rows T stages history,
      ZFSet.pair z (ZFSet.pair top ∅) ∈ M.refinementHistoryOrder rows rowOrder T stages history :=
  rowAssignmentOrder_top (M.refinementHistoryForcing_shape rows T stages history) topRows
    (run.empty_assignments ordinal hRows topMem)

end RecursiveRefinementDataHistory
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {rows rowOrder : ZFSet.{u}}
variable (order : PartialOrderCode rows rowOrder) (T stages history : ZFSet.{u})

@[instance_reducible] noncomputable def refinementHistoryPartialOrder :
    PartialOrder (SetMembers (M.refinementHistoryForcing rows T stages history)) :=
  (M.refinementHistoryOrder_partialOrder order T stages history).toPartialOrder

theorem refinementHistoryDecodedOrder_eq :
    letI := M.refinementHistoryPartialOrder order T stages history
    (SetMembers.presentation (M.refinementHistoryForcing rows T stages history)).conditionOrder =
      M.refinementHistoryOrder rows rowOrder T stages history :=
  (M.refinementHistoryOrder_partialOrder order T stages history).conditionOrder_eq

@[instance_reducible] noncomputable def refinementHistoryOrderTop
    (run : RecursiveRefinementDataHistory M rows T stages history)
    (ordinal : ordinalSetProperty stages) (hRows : rows ∈ M.sets)
    (top : ZFSet.{u}) (topMem : top ∈ rows)
    (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder) :
    letI := M.refinementHistoryPartialOrder order T stages history
    OrderTop (SetMembers (M.refinementHistoryForcing rows T stages history)) :=
  (M.refinementHistoryOrder_partialOrder order T stages history).toOrderTop (ZFSet.pair top ∅)
    (run.empty_assignments ordinal hRows topMem) (run.greatest ordinal hRows topMem topRows)

theorem refinementHistoryDecodedTop_eq
    (run : RecursiveRefinementDataHistory M rows T stages history)
    (ordinal : ordinalSetProperty stages) (hRows : rows ∈ M.sets)
    (top : ZFSet.{u}) (topMem : top ∈ rows)
    (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder) :
    letI := M.refinementHistoryPartialOrder order T stages history
    letI := M.refinementHistoryOrderTop order T stages history run ordinal hRows top topMem topRows
    (SetMembers.presentation (M.refinementHistoryForcing rows T stages history)).encode ⊤ = ZFSet.pair top ∅ :=
  SetMembers.raw_ofMem _ _

end TransitiveGround

end

namespace TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {R : Type u} [PartialOrder R] (c : Presentation R)
variable {T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M c.carrier T stages history)
variable (ordinal : ordinalSetProperty stages) (carrier : c.carrier ∈ M.sets)
variable (rowTop : R)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode rowTop) ∈ c.conditionOrder)
include run ordinal carrier topRows

theorem refinementHistoryRowNameFamily_power_eq (X : ZFSet.{u})
    (valid : ∀ z ∈ X, IsName c.pairEmpty z) (n : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages history run ordinal carrier
      (c.encode rowTop) (c.encode_mem rowTop) topRows
    Name.renamedFamily (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history))
      (M.refinementHistoryRowInclusion c run ordinal carrier)
      (iteratedPairNameFamily (c.pairEmpty.encode rowTop) X n)
      (iteratedPairNameFamily_valid rowTop valid n) =
    iteratedPairNameFamily
      ((SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)).encode ⊤) X n := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages history run ordinal carrier
    (c.encode rowTop) (c.encode_mem rowTop) topRows
  rw [M.refinementHistoryRowNameFamily_eq c run ordinal carrier,
    M.refinementHistoryDecodedTop_eq]
  rfl

theorem refinementHistoryRowNameFamily_square_eq (X Y : ZFSet.{u})
    (validX : ∀ z ∈ X, IsName c.pairEmpty z) (validY : ∀ z ∈ Y, IsName c.pairEmpty z) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages history run ordinal carrier
      (c.encode rowTop) (c.encode_mem rowTop) topRows
    Name.renamedFamily (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history))
      (M.refinementHistoryRowInclusion c run ordinal carrier)
      (orderedPairNameFamily (c.pairEmpty.encode rowTop) X Y)
      (orderedPairNameFamily_valid rowTop validX validY) =
    orderedPairNameFamily
      ((SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)).encode ⊤) X Y := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages history run ordinal carrier
    (c.encode rowTop) (c.encode_mem rowTop) topRows
  rw [M.refinementHistoryRowNameFamily_eq c run ordinal carrier,
    M.refinementHistoryDecodedTop_eq]
  rfl

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]

theorem recursiveRefinementStageSystem
    (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
    (b : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 stages history : ZFSet.{u})
    (run : RecursiveRefinementDataHistory M c.carrier T stages history)
    (ordinal : ordinalSetProperty stages)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets)
    (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets)
    (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
    (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
      HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
    (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
      HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
    (top : ZFSet.{u}) (topMem : top ∈ c.carrier)
    (topRows : ∀ row ∈ c.carrier, ZFSet.pair row top ∈ c.conditionOrder) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages history
      run ordinal carrier top topMem topRows
    ∀ (e : PosetAction G (SetMembers (M.refinementHistoryForcing c.carrier T stages history)))
      (image : G → ZFSet.{u} → ZFSet.{u}),
      (∀ g (q : SetMembers (M.refinementHistoryForcing c.carrier T stages history)) row A,
        SetMembers.raw q = ZFSet.pair (c.encode row) A →
        SetMembers.raw (e.iso g q) = ZFSet.pair (c.encode (a.iso g row)) (image g A)) →
      (∀ g, image g ∅ = ∅) →
      e.actionGraph (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)) t ∈ M.sets →
      RefinementStageSystem M e
        (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history))
        t b d base directed stages T T2 := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages history
    run ordinal carrier top topMem topRows
  intro e image coordinates emptyImage actionGround
  have nextCarrier : (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)).carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hStages hHistory omega
  have nextOrder : (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)).conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier order hT hStages hHistory omega
  have maps := M.conditionMapFamily_mem_of_actionGraph e
    (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)) t
    pairing unions powers separation collection nextCarrier group actionGround
  obtain ⟨nextValid1, nextClosed1, nextHS1⟩ :=
    M.refinementHistoryRowNameFamily_transport c run ordinal carrier a e image coordinates emptyImage
      (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  obtain ⟨nextValid2, nextClosed2, nextHS2⟩ :=
    M.refinementHistoryRowNameFamily_transport c run ordinal carrier a e image coordinates emptyImage
      (d.principalSupportFamily base directed) T2 valid2 closed2 symmetric2
  exact M.refinementStageSystem e
    (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)) t b d base directed
    pairing unions powers separation collection nextCarrier nextOrder group nodes nodeOrder maps nodeMaps supports
    hStages hT hT2 nextValid1 nextValid2 nextClosed1 nextClosed2 nextHS1 nextHS2

end TransitiveGround

namespace RecursiveRefinementOrderHistory
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable {alpha p Ap q Aq : ZFSet.{u}} (hAlpha : alpha ∈ M.sets)
variable (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha)
variable (cutSubset : alpha ⊆ stages)
variable (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
  ∀ A lower stronger, stageOneRawTests M d A lower →
    ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
include run pairing unions powers separation infinite choice hStages hHistory hT hAlpha ordinal cutOrdinal cutSubset mono
local notation "levels" => refinementDataHistoryLevels stages history T
local notation "spliced" => assignmentSplice levels alpha Aq Ap

theorem splice_mem
    (upper : ZFSet.pair p Ap ∈ M.refinementHistoryForcing rows T stages history)
    (lower : ZFSet.pair q Aq ∈ M.refinementHistoryForcing rows T alpha (graphRestriction alpha history))
    (rowsBelow : ZFSet.pair q p ∈ rowOrder)
    (contains : assignmentCut levels alpha Ap ⊆ assignmentCut levels alpha Aq) :
    ZFSet.pair q spliced ∈ M.refinementHistoryForcing rows T stages history := by
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT
  have candidate := M.refinementDataHistoryCandidate_splice pairing unions powers separation infinite choice
    cutSubset hLevels hAlpha
    ((M.mem_refinementHistoryForcing rows T alpha (graphRestriction alpha history) _).1 lower).1
    ((M.mem_refinementHistoryForcing rows T stages history _).1 upper).1
  exact run.splice_mem_of_candidates ordinal cutOrdinal cutSubset mono upper lower rowsBelow contains candidate
    (fun beta hbeta => M.refinementDataHistoryCandidate_cut separation run.carriers.data
      (ordinal.1 beta hbeta) hLevels (M.transitive hStages hbeta) (M.omega_mem separation infinite) candidate)

theorem splice_lifting
    (upper : ZFSet.pair p Ap ∈ M.refinementHistoryForcing rows T stages history)
    (below : ZFSet.pair (ZFSet.pair q Aq) (ZFSet.pair p (assignmentCut levels alpha Ap)) ∈
      M.refinementHistoryOrder rows rowOrder T alpha (graphRestriction alpha history)) :
    ZFSet.pair q spliced ∈ M.refinementHistoryForcing rows T stages history ∧
      ZFSet.pair (ZFSet.pair q spliced) (ZFSet.pair p Ap) ∈
        M.refinementHistoryOrder rows rowOrder T stages history ∧
      assignmentCut levels alpha spliced = Aq := by
  obtain ⟨lower, _, rowsBelow, contains⟩ :=
    (M.pair_mem_refinementHistoryOrder rows rowOrder T alpha (graphRestriction alpha history) _ _ _ _).1 below
  have lowerData := ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1
    ((M.mem_refinementHistoryForcing rows T alpha (graphRestriction alpha history) _).1 lower).1).2.2.1
  have fullLower := run.carriers.data.prefix_assignments_cut cutSubset lowerData
  have retained : assignmentCut levels alpha Ap ⊆ assignmentCut levels alpha Aq := by
    rw [fullLower]
    exact contains
  have member := run.splice_mem pairing unions powers separation infinite choice hStages hHistory hT hAlpha
    ordinal cutOrdinal cutSubset mono upper lower rowsBelow retained
  refine ⟨member, (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).2
    ⟨member, upper, rowsBelow, assignmentSplice_extends retained⟩, ?_⟩
  rw [assignmentCut_splice, fullLower]

end RecursiveRefinementOrderHistory

namespace RecursiveRefinementOrderHistory
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history alpha : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha)
variable (subset : alpha ⊆ stages)
include run ordinal cutOrdinal subset

theorem cut_mem_le {row A : ZFSet.{u}}
    (member : ZFSet.pair row A ∈ M.refinementHistoryForcing rows T stages history) :
    ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages history T) alpha A) ∈
      M.refinementHistoryForcing rows T alpha (graphRestriction alpha history) := by
  have compare : alpha ∈ stages ∨ alpha = stages := by
    obtain ⟨a, ea⟩ := (ordinalSetProperty_iff alpha).1 cutOrdinal
    obtain ⟨b, eb⟩ := (ordinalSetProperty_iff stages).1 ordinal
    have below := (ordinalCode_subset_iff a b).1 (ea ▸ eb ▸ subset)
    rcases lt_or_eq_of_le below with less | equal
    · exact Or.inl (ea ▸ eb ▸ (mem_ordinalCode_iff a b).2 less)
    · exact Or.inr (ea.trans ((congrArg ordinalCode equal).trans eb.symm))
  rcases compare with earlier | rfl
  · exact run.carriers.cut_mem member earlier
  · rw [run.carriers.data.function.restriction_eq]
    have data := ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1
      ((M.mem_refinementHistoryForcing rows T _ history _).1 member).1).2.2.1
    rw [assignmentCut_full run.carriers.data.levels_function data]
    exact member

theorem cut_order_le {q A p D : ZFSet.{u}}
    (below : ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈
      M.refinementHistoryOrder rows rowOrder T stages history) :
    ZFSet.pair
      (ZFSet.pair q (assignmentCut (refinementDataHistoryLevels stages history T) alpha A))
      (ZFSet.pair p (assignmentCut (refinementDataHistoryLevels stages history T) alpha D)) ∈
      M.refinementHistoryOrder rows rowOrder T alpha (graphRestriction alpha history) := by
  obtain ⟨hq, hp, rowBelow, data⟩ := (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).1 below
  exact (M.pair_mem_refinementHistoryOrder rows rowOrder T alpha (graphRestriction alpha history) _ _ _ _).2
    ⟨run.cut_mem_le ordinal cutOrdinal subset hq, run.cut_mem_le ordinal cutOrdinal subset hp,
      rowBelow, assignmentCut_mono data⟩

theorem include_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
    (hAlpha : alpha ∈ M.sets) (hRows : rows ∈ M.sets)
    (top : ZFSet.{u}) (topMem : top ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder)
    (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ A lower stronger, stageOneRawTests M d A lower →
        ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
    {q Aq : ZFSet.{u}}
    (lower : ZFSet.pair q Aq ∈ M.refinementHistoryForcing rows T alpha (graphRestriction alpha history)) :
    ZFSet.pair q Aq ∈ M.refinementHistoryForcing rows T stages history := by
  have lowerFacts := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1
    ((M.mem_refinementHistoryForcing rows T alpha (graphRestriction alpha history) _).1 lower).1
  have fullLower := run.carriers.data.prefix_assignments_cut subset lowerFacts.2.2.1
  have member := run.splice_mem pairing unions powers separation infinite choice hStages hHistory hT hAlpha
    ordinal cutOrdinal subset mono (run.carriers.empty_assignments ordinal hRows topMem) lower
    (topRows q lowerFacts.1) (by
      rw [assignmentCut_empty_data]
      exact fun z impossible => False.elim (ZFSet.notMem_empty z impossible))
  have equal : assignmentSplice (refinementDataHistoryLevels stages history T) alpha Aq ∅ = Aq := by
    rw [assignmentSplice, fullLower]
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_union, mem_assignmentUpper]
    exact ⟨fun h => h.elim id (fun h => False.elim (ZFSet.notMem_empty z h.1)), Or.inl⟩
  exact equal ▸ member

end RecursiveRefinementOrderHistory

namespace RecursiveRefinementOrderHistory
open SetRealization
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history alpha : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha)
variable (subset : alpha ⊆ stages)
local notation "U" => M.refinementHistoryForcing rows T stages history
local notation "L" => M.refinementHistoryForcing rows T alpha (graphRestriction alpha history)
local notation "levels" => refinementDataHistoryLevels stages history T
local notation "sU" => SetMembers.presentation U
local notation "sL" => SetMembers.presentation L
include run ordinal cutOrdinal subset

theorem restrictionGraph_function :
    ZFSet.IsFunc U L (rowAssignmentCutGraph U L levels alpha) :=
  rowAssignmentCutGraph_function U L levels alpha
    (fun z member => by
      obtain ⟨row, _, A, _, equal⟩ := ZFSet.mem_prod.1 (M.refinementHistoryForcing_shape rows T stages history member)
      exact ⟨row, A, equal⟩)
    (fun _ _ member => run.cut_mem_le ordinal cutOrdinal subset member)

noncomputable def restrictionFunction : SetMembers U → SetMembers L :=
  (sU).decodeFunction sL (rowAssignmentCutGraph U L levels alpha)
    (run.restrictionGraph_function ordinal cutOrdinal subset)

theorem restrictionFunction_raw (x : SetMembers U) (row A : ZFSet.{u})
    (code : SetMembers.raw x = ZFSet.pair row A) :
    SetMembers.raw (run.restrictionFunction ordinal cutOrdinal subset x) =
      ZFSet.pair row (assignmentCut levels alpha A) := by
  have entry := (sU).decodeFunction_mem sL (rowAssignmentCutGraph U L levels alpha)
    (run.restrictionGraph_function ordinal cutOrdinal subset) x
  change ZFSet.pair (SetMembers.raw x)
    (SetMembers.raw (run.restrictionFunction ordinal cutOrdinal subset x)) ∈ _ at entry
  rw [code] at entry
  exact ((pair_mem_rowAssignmentCutGraph U L levels alpha row A _).1 entry).2.2

noncomputable def restriction (order : PartialOrderCode rows rowOrder) :
    letI := M.refinementHistoryPartialOrder order T stages history
    letI := M.refinementHistoryPartialOrder order T alpha (graphRestriction alpha history)
    SetMembers U →o SetMembers L := by
  letI := M.refinementHistoryPartialOrder order T stages history
  letI := M.refinementHistoryPartialOrder order T alpha (graphRestriction alpha history)
  refine { toFun := run.restrictionFunction ordinal cutOrdinal subset, monotone' := ?_ }
  intro x y below
  obtain ⟨q, _, A, _, xCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape rows T stages history (SetMembers.raw_mem x))
  obtain ⟨p, _, D, _, yCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape rows T stages history (SetMembers.raw_mem y))
  change ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ _ at below
  change ZFSet.pair (SetMembers.raw (run.restrictionFunction ordinal cutOrdinal subset x))
    (SetMembers.raw (run.restrictionFunction ordinal cutOrdinal subset y)) ∈ _
  rw [run.restrictionFunction_raw ordinal cutOrdinal subset x q A xCode,
    run.restrictionFunction_raw ordinal cutOrdinal subset y p D yCode]
  rw [xCode, yCode] at below
  exact run.cut_order_le ordinal cutOrdinal subset below

end RecursiveRefinementOrderHistory

namespace RecursiveRefinementOrderHistory
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history alpha : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha)
variable (subset : alpha ⊆ stages)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable (hAlpha : alpha ∈ M.sets) (hRows : rows ∈ M.sets)
variable (top : ZFSet.{u}) (topMem : top ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder)
variable (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
  ∀ A lower stronger, stageOneRawTests M d A lower →
    ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
local notation "U" => M.refinementHistoryForcing rows T stages history
local notation "L" => M.refinementHistoryForcing rows T alpha (graphRestriction alpha history)
include run ordinal cutOrdinal subset pairing unions powers separation infinite choice hStages hHistory hT hAlpha hRows topMem topRows mono

noncomputable def inclusionFunction (x : SetMembers L) : SetMembers U :=
  SetMembers.ofMem (SetMembers.raw x) (by
    obtain ⟨row, _, A, _, equal⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T alpha (graphRestriction alpha history) (SetMembers.raw_mem x))
    rw [equal]
    exact run.include_mem ordinal cutOrdinal subset pairing unions powers separation infinite choice
      hStages hHistory hT hAlpha hRows top topMem topRows mono (equal ▸ SetMembers.raw_mem x))

local notation "inc" => run.inclusionFunction ordinal cutOrdinal subset pairing unions powers separation infinite choice
  hStages hHistory hT hAlpha hRows top topMem topRows mono

theorem inclusionFunction_raw (x : SetMembers L) : SetMembers.raw (inc x) = SetMembers.raw x :=
  SetMembers.raw_ofMem _ _

noncomputable def inclusion (order : PartialOrderCode rows rowOrder) :
    letI := M.refinementHistoryPartialOrder order T stages history
    letI := M.refinementHistoryPartialOrder order T alpha (graphRestriction alpha history)
    SetMembers L ↪o SetMembers U := by
  letI := M.refinementHistoryPartialOrder order T stages history
  letI := M.refinementHistoryPartialOrder order T alpha (graphRestriction alpha history)
  have raw := run.inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
    hStages hHistory hT hAlpha hRows top topMem topRows mono
  refine { toFun := inc, inj' := ?_, map_rel_iff' := ?_ }
  · intro x y equal
    apply SetMembers.raw_injective L
    exact (raw x).symm.trans ((congrArg SetMembers.raw equal).trans (raw y))
  · intro x y
    change ZFSet.pair (SetMembers.raw (inc x)) (SetMembers.raw (inc y)) ∈ _ ↔
      ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ _
    rw [raw x, raw y]
    have hx := SetMembers.raw_mem x
    have hy := SetMembers.raw_mem y
    have ux := SetMembers.raw_mem (inc x)
    have uy := SetMembers.raw_mem (inc y)
    rw [raw x] at ux
    rw [raw y] at uy
    obtain ⟨q, _, A, _, xCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T alpha (graphRestriction alpha history) hx)
    obtain ⟨p, _, D, _, yCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T alpha (graphRestriction alpha history) hy)
    rw [xCode] at hx ux
    rw [yCode] at hy uy
    rw [xCode, yCode, M.pair_mem_refinementHistoryOrder, M.pair_mem_refinementHistoryOrder]
    simp only [hx, hy, ux, uy, true_and]

end RecursiveRefinementOrderHistory

namespace RecursiveRefinementOrderHistory
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history alpha : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha)
variable (subset : alpha ⊆ stages)
local notation "U" => M.refinementHistoryForcing rows T stages history
local notation "L" => M.refinementHistoryForcing rows T alpha (graphRestriction alpha history)
local notation "sU" => SetMembers.presentation U
local notation "sL" => SetMembers.presentation L

theorem restrictionFunction_graph :
    (sU).graph sL (run.restrictionFunction ordinal cutOrdinal subset) =
      rowAssignmentCutGraph U L (refinementDataHistoryLevels stages history T) alpha :=
  (sU).graph_decodeFunction sL _ (run.restrictionGraph_function ordinal cutOrdinal subset)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable (hAlpha : alpha ∈ M.sets) (hRows : rows ∈ M.sets)

include pairing unions powers separation hStages hHistory hT hAlpha hRows in
theorem restrictionFunction_graph_mem (omega : ZFSet.omega ∈ M.sets) :
    (sU).graph sL (run.restrictionFunction ordinal cutOrdinal subset) ∈ M.sets := by
  rw [run.restrictionFunction_graph]
  exact M.rowAssignmentCutGraph_mem pairing unions powers separation
    (M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hStages hHistory omega)
    (M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hHistory) omega)
    (M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT) hAlpha

variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (top : ZFSet.{u}) (topMem : top ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder)
variable (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
    ∀ A lower stronger, stageOneRawTests M d A lower →
      ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
local notation "inc" => run.inclusionFunction ordinal cutOrdinal subset pairing unions powers separation infinite choice
  hStages hHistory hT hAlpha hRows top topMem topRows mono

theorem inclusionFunction_graph : (sL).graph sU inc = identityFunctionGraph L := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph, mem_identityFunctionGraph]
  have code := run.inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
    hStages hHistory hT hAlpha hRows top topMem topRows mono
  constructor
  · rintro ⟨x, rfl⟩
    change ∃ y ∈ L, ZFSet.pair (SetMembers.raw x) (SetMembers.raw (inc x)) = ZFSet.pair y y
    rw [code x]
    exact ⟨SetMembers.raw x, SetMembers.raw_mem x, rfl⟩
  · rintro ⟨x, member, rfl⟩
    let q := SetMembers.ofMem x member
    refine ⟨q, ?_⟩
    change ZFSet.pair (SetMembers.raw q) (SetMembers.raw (inc q)) = ZFSet.pair x x
    rw [code q, SetMembers.raw_ofMem]

include pairing unions powers separation hStages hHistory hT hAlpha hRows in
theorem inclusionFunction_graph_mem (omega : ZFSet.omega ∈ M.sets) :
    (sL).graph sU inc ∈ M.sets := by
  rw [run.inclusionFunction_graph]
  exact M.identityFunctionGraph_mem pairing unions powers separation
    (M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hHistory) omega)

end RecursiveRefinementOrderHistory

namespace RecursiveRefinementOrderHistory
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history alpha : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha)
variable (subset : alpha ⊆ stages)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable (hAlpha : alpha ∈ M.sets) (hRows : rows ∈ M.sets)
variable (top : ZFSet.{u}) (topMem : top ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder)
variable (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
  ∀ A lower stronger, stageOneRawTests M d A lower →
    ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
local notation "U" => M.refinementHistoryForcing rows T stages history
local notation "L" => M.refinementHistoryForcing rows T alpha (graphRestriction alpha history)
local notation "levels" => refinementDataHistoryLevels stages history T
local notation "res" => run.restrictionFunction ordinal cutOrdinal subset
local notation "inc" => run.inclusionFunction ordinal cutOrdinal subset pairing unions powers separation infinite choice
  hStages hHistory hT hAlpha hRows top topMem topRows mono
include run ordinal cutOrdinal subset pairing unions powers separation infinite choice hStages hHistory hT hAlpha hRows topMem topRows mono

theorem completeProjection (order : PartialOrderCode rows rowOrder) :
    letI := M.refinementHistoryPartialOrder order T stages history
    letI := M.refinementHistoryPartialOrder order T alpha (graphRestriction alpha history)
    CompleteProjection (run.restriction ordinal cutOrdinal subset order)
      (run.inclusion ordinal cutOrdinal subset pairing unions powers separation infinite choice
        hStages hHistory hT hAlpha hRows top topMem topRows mono order) := by
  let := M.refinementHistoryPartialOrder order T stages history
  let := M.refinementHistoryPartialOrder order T alpha (graphRestriction alpha history)
  have incRaw := run.inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
    hStages hHistory hT hAlpha hRows top topMem topRows mono
  have resRaw := run.restrictionFunction_raw ordinal cutOrdinal subset
  have lowerFixed : ∀ (x : SetMembers L) row A, SetMembers.raw x = ZFSet.pair row A →
      assignmentCut levels alpha A = A := by
    intro x row A code
    have member := SetMembers.raw_mem x
    rw [code] at member
    exact run.carriers.data.prefix_assignments_cut subset
      (((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1
        ((M.mem_refinementHistoryForcing rows T alpha (graphRestriction alpha history) _).1 member).1).2.2.1)
  refine ⟨?_, ?_, ?_⟩
  · intro q
    change res (inc q) = q
    obtain ⟨row, _, A, _, code⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T alpha (graphRestriction alpha history) (SetMembers.raw_mem q))
    apply SetMembers.raw_injective L
    rw [resRaw (inc q) row A ((incRaw q).trans code), lowerFixed q row A code, code]
  · intro p q
    obtain ⟨rowP, _, Ap, _, pCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T stages history (SetMembers.raw_mem p))
    obtain ⟨rowQ, _, Aq, _, qCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T alpha (graphRestriction alpha history) (SetMembers.raw_mem q))
    have hp := SetMembers.raw_mem p
    have hq := SetMembers.raw_mem q
    have hinc := SetMembers.raw_mem (inc q)
    have hres := SetMembers.raw_mem (res p)
    rw [pCode] at hp
    rw [qCode] at hq
    rw [incRaw q, qCode] at hinc
    rw [resRaw p rowP Ap pCode] at hres
    change ZFSet.pair (SetMembers.raw p) (SetMembers.raw (inc q)) ∈ _ ↔
      ZFSet.pair (SetMembers.raw (res p)) (SetMembers.raw q) ∈ _
    rw [incRaw q, resRaw p rowP Ap pCode, pCode, qCode,
      M.pair_mem_refinementHistoryOrder, M.pair_mem_refinementHistoryOrder]
    simp only [hp, hq, hinc, hres, true_and]
    constructor
    · rintro ⟨rowsBelow, data⟩
      refine ⟨rowsBelow, ?_⟩
      have cutData : assignmentCut levels alpha Aq ⊆ assignmentCut levels alpha Ap := assignmentCut_mono data
      rwa [lowerFixed q rowQ Aq qCode] at cutData
    · rintro ⟨rowsBelow, data⟩
      exact ⟨rowsBelow, fun _ member => assignmentCut_subset levels alpha Ap (data member)⟩
  · intro p q below
    obtain ⟨rowP, _, Ap, _, pCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T stages history (SetMembers.raw_mem p))
    obtain ⟨rowQ, _, Aq, _, qCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T alpha (graphRestriction alpha history) (SetMembers.raw_mem q))
    have hp := SetMembers.raw_mem p
    rw [pCode] at hp
    change ZFSet.pair (SetMembers.raw q) (SetMembers.raw (res p)) ∈ _ at below
    rw [resRaw p rowP Ap pCode, qCode] at below
    obtain ⟨member, stronger, exactCut⟩ := run.splice_lifting pairing unions powers separation infinite choice
      hStages hHistory hT hAlpha ordinal cutOrdinal subset mono hp below
    let r : SetMembers U := SetMembers.ofMem (ZFSet.pair rowQ (assignmentSplice levels alpha Aq Ap)) member
    have rCode : SetMembers.raw r = ZFSet.pair rowQ (assignmentSplice levels alpha Aq Ap) :=
      SetMembers.raw_ofMem _ _
    refine ⟨r, ?_, ?_⟩
    · change ZFSet.pair (SetMembers.raw r) (SetMembers.raw p) ∈ _
      rwa [rCode, pCode]
    · change res r = q
      apply SetMembers.raw_injective L
      rw [resRaw r rowQ (assignmentSplice levels alpha Aq Ap) rCode, exactCut, qCode]

end RecursiveRefinementOrderHistory

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R : Type u}
variable (c : Presentation R) (T stages history : ZFSet.{u})
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "upper" => SetMembers.presentation Q

private theorem rowCarrier_shape : Q ⊆ ZFSet.prod c.carrier (Q).sUnion.sUnion := by
  intro z hz
  obtain ⟨row, hrow, A, _, code⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages history hz)
  rw [code] at hz ⊢
  exact ZFSet.pair_mem_prod.2 ⟨hrow, pair_second_mem_doubleUnion hz⟩

noncomputable def refinementHistoryRowFunction : SetMembers Q → R :=
  (upper).decodeFunction c (rowAssignmentRows Q c.carrier (Q).sUnion.sUnion)
    (rowAssignmentRows_function (M.rowCarrier_shape c T stages history))

theorem refinementHistoryRowFunction_code (p : SetMembers Q) (row : R) (A : ZFSet.{u})
    (code : SetMembers.raw p = ZFSet.pair (c.encode row) A) :
    M.refinementHistoryRowFunction c T stages history p = row := by
  have entry := (upper).decodeFunction_mem c (rowAssignmentRows Q c.carrier (Q).sUnion.sUnion)
    (rowAssignmentRows_function (M.rowCarrier_shape c T stages history)) p
  change ZFSet.pair (SetMembers.raw p)
    (c.encode (M.refinementHistoryRowFunction c T stages history p)) ∈ _ at entry
  rw [code] at entry
  apply c.injective
  exact ((rowAssignmentRows_entry Q c.carrier (Q).sUnion.sUnion (c.encode row) A _).1 entry).2.2.2

theorem refinementHistoryRowFunction_coordinates (p : SetMembers Q) :
    ∃ A, SetMembers.raw p =
      ZFSet.pair (c.encode (M.refinementHistoryRowFunction c T stages history p)) A := by
  obtain ⟨row, hrow, A, _, code⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages history (SetMembers.raw_mem p))
  obtain ⟨r, rfl⟩ := (c.mem_carrier row).1 hrow
  exact ⟨A, (M.refinementHistoryRowFunction_code c T stages history p r A code).symm ▸ code⟩

theorem refinementHistoryRowFunction_graph :
    (upper).graph c (M.refinementHistoryRowFunction c T stages history) =
      rowAssignmentRows Q c.carrier (Q).sUnion.sUnion :=
  (upper).graph_decodeFunction c _ _

variable [PartialOrder R]

noncomputable def refinementHistoryRowRestriction :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    SetMembers Q →o R := by
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  refine { toFun := M.refinementHistoryRowFunction c T stages history, monotone' := ?_ }
  intro p q below
  obtain ⟨A, pCode⟩ := M.refinementHistoryRowFunction_coordinates c T stages history p
  obtain ⟨B, qCode⟩ := M.refinementHistoryRowFunction_coordinates c T stages history q
  change ZFSet.pair (SetMembers.raw p) (SetMembers.raw q) ∈ _ at below
  rw [pCode, qCode] at below
  exact (c.pair_mem_conditionOrder _ _).1
    ((M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages history _ _ _ _).1 below).2.2.1

variable (run : RecursiveRefinementOrderHistory M c.carrier c.conditionOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (carrier : c.carrier ∈ M.sets)
local notation "incl" => M.refinementHistoryRowInclusion c run.carriers ordinal carrier
local notation "res" => M.refinementHistoryRowFunction c T stages history

noncomputable def refinementHistoryRowEmbedding :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    R ↪o SetMembers Q := by
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  have incRaw : ∀ p : R, SetMembers.raw (incl p) = ZFSet.pair (c.encode p) ∅ :=
    M.refinementHistoryRowInclusion_encode c run.carriers ordinal carrier
  refine { toFun := incl, inj' := ?_, map_rel_iff' := ?_ }
  · intro p q equal
    apply c.injective
    have raw := congrArg SetMembers.raw equal
    rw [incRaw p, incRaw q] at raw
    exact (ZFSet.pair_injective raw).1
  · intro p q
    change ZFSet.pair (SetMembers.raw (incl p)) (SetMembers.raw (incl q)) ∈ _ ↔ p ≤ q
    rw [incRaw p, incRaw q, M.pair_mem_refinementHistoryOrder]
    have hp := SetMembers.raw_mem (incl p)
    have hq := SetMembers.raw_mem (incl q)
    rw [incRaw p] at hp
    rw [incRaw q] at hq
    constructor
    · intro below
      exact (c.pair_mem_conditionOrder _ _).1 below.2.2.1
    · intro below
      exact ⟨hp, hq, (c.pair_mem_conditionOrder _ _).2 below, fun _ hz => hz⟩

theorem refinementHistoryRow_retract (q : R) : res (incl q) = q :=
  M.refinementHistoryRowFunction_code c T stages history (incl q) q ∅
    (M.refinementHistoryRowInclusion_encode c run.carriers ordinal carrier q)

theorem refinementHistoryRow_le_include :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    ∀ p : SetMembers Q, ∀ q : R,
      p ≤ M.refinementHistoryRowEmbedding c T stages history run ordinal carrier q ↔ res p ≤ q := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  intro p q
  obtain ⟨A, pCode⟩ := M.refinementHistoryRowFunction_coordinates c T stages history p
  have incCode : SetMembers.raw (incl q) = ZFSet.pair (c.encode q) ∅ :=
    M.refinementHistoryRowInclusion_encode c run.carriers ordinal carrier q
  have hp := SetMembers.raw_mem p
  have hq := SetMembers.raw_mem (incl q)
  rw [pCode] at hp
  rw [incCode] at hq
  change ZFSet.pair (SetMembers.raw p) (SetMembers.raw (incl q)) ∈ _ ↔ res p ≤ q
  rw [pCode, incCode, M.pair_mem_refinementHistoryOrder]
  constructor
  · intro below
    exact (c.pair_mem_conditionOrder _ _).1 below.2.2.1
  · intro below
    exact ⟨hp, hq, (c.pair_mem_conditionOrder _ _).2 below,
      fun z hz => (ZFSet.notMem_empty z hz).elim⟩

theorem refinementHistoryRowInclusion_graph :
    c.graph upper incl = c.graph c.pairEmpty id := by
  apply ZFSet.ext
  intro z
  rw [c.mem_graph, c.mem_graph]
  constructor
  · rintro ⟨p, rfl⟩
    rw [M.refinementHistoryRowInclusion_encode c run.carriers ordinal carrier]
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    rw [M.refinementHistoryRowInclusion_encode c run.carriers ordinal carrier]
    rfl

theorem refinementHistoryRowGraphs_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hQ : Q ∈ M.sets) :
    (upper).graph c res ∈ M.sets ∧ c.graph upper incl ∈ M.sets := by
  constructor
  · rw [M.refinementHistoryRowFunction_graph]
    exact M.rowAssignmentRows_mem pairing unions powers separation hQ carrier
      (M.union_mem unions (M.union_mem unions hQ))
  · rw [M.refinementHistoryRowInclusion_graph c T stages history run ordinal carrier]
    exact M.pairEmpty_forwardGraph_mem pairing unions powers separation c carrier

private theorem assignmentCut_zero (levels A : ZFSet.{u}) : assignmentCut levels ∅ A = ∅ := by
  apply ZFSet.ext
  intro z
  simp only [mem_assignmentCut, ZFSet.notMem_empty, false_and, exists_false, and_false]

theorem refinementHistoryRow_completeProjection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
    (top : ZFSet.{u}) (topMem : top ∈ c.carrier)
    (topRows : ∀ row ∈ c.carrier, ZFSet.pair row top ∈ c.conditionOrder)
    (mono : ∀ beta (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode fields) ∈ history →
      ∀ A lower stronger, stageOneRawTests M fields A lower →
        ZFSet.pair stronger lower ∈ fields 8 → stageOneRawTests M fields A stronger) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    CompleteProjection (M.refinementHistoryRowRestriction c T stages history)
      (M.refinementHistoryRowEmbedding c T stages history run ordinal carrier) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  refine ⟨M.refinementHistoryRow_retract c T stages history run ordinal carrier,
    M.refinementHistoryRow_le_include c T stages history run ordinal carrier, ?_⟩
  intro p q below
  let Q0 := M.refinementHistoryForcing c.carrier T ∅ (graphRestriction ∅ history)
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T ∅ (graphRestriction ∅ history)
  have zeroSubset : (∅ : ZFSet.{u}) ⊆ stages := fun z hz => (ZFSet.notMem_empty z hz).elim
  have hEmpty : (∅ : ZFSet.{u}) ∈ M.sets := M.empty_mem ⟨c.carrier, carrier⟩
  let cut := run.restriction ordinal ordinalSetProperty_empty zeroSubset c.conditionOrder_code
  have projection := run.completeProjection ordinal ordinalSetProperty_empty zeroSubset
    pairing unions powers separation infinite choice hStages hHistory hT hEmpty carrier
    top topMem topRows mono c.conditionOrder_code
  have zeroCode : ZFSet.pair (c.encode q) ∅ ∈ Q0 := by
    change ZFSet.pair (c.encode q) ∅ ∈ M.refinementHistoryForcing c.carrier T ∅ (graphRestriction ∅ history)
    rw [M.refinementHistoryForcing_initial carrier T (graphRestriction ∅ history)]
    exact ZFSet.pair_mem_prod.2 ⟨c.encode_mem q, ZFSet.mem_singleton.2 rfl⟩
  let q0 : SetMembers Q0 := SetMembers.ofMem (ZFSet.pair (c.encode q) ∅) zeroCode
  have q0Code : SetMembers.raw q0 = ZFSet.pair (c.encode q) ∅ := SetMembers.raw_ofMem _ _
  obtain ⟨A, pCode⟩ := M.refinementHistoryRowFunction_coordinates c T stages history p
  have cutCode : SetMembers.raw (cut p) = ZFSet.pair (c.encode (res p)) ∅ := by
    change SetMembers.raw (run.restrictionFunction ordinal ordinalSetProperty_empty zeroSubset p) = _
    rw [run.restrictionFunction_raw ordinal ordinalSetProperty_empty zeroSubset p (c.encode (res p)) A pCode,
      assignmentCut_zero]
  have cutMember := SetMembers.raw_mem (cut p)
  rw [cutCode] at cutMember
  have belowZero : q0 ≤ cut p := by
    change ZFSet.pair (SetMembers.raw q0) (SetMembers.raw (cut p)) ∈ _
    rw [q0Code, cutCode, M.pair_mem_refinementHistoryOrder]
    exact ⟨zeroCode, cutMember, (c.pair_mem_conditionOrder _ _).2 below, fun _ hz => hz⟩
  obtain ⟨r, rp, exactCut⟩ := projection.lift p q0 belowZero
  refine ⟨r, rp, ?_⟩
  obtain ⟨B, rCode⟩ := M.refinementHistoryRowFunction_coordinates c T stages history r
  have cutR : SetMembers.raw (cut r) = ZFSet.pair (c.encode (res r)) ∅ := by
    change SetMembers.raw (run.restrictionFunction ordinal ordinalSetProperty_empty zeroSubset r) = _
    rw [run.restrictionFunction_raw ordinal ordinalSetProperty_empty zeroSubset r (c.encode (res r)) B rCode,
      assignmentCut_zero]
  have equal := congrArg SetMembers.raw exactCut
  change SetMembers.raw (cut r) = SetMembers.raw q0 at equal
  rw [cutR, q0Code] at equal
  exact c.injective (ZFSet.pair_injective equal).1

end TransitiveGround

end PartitionPilot.Forcing

end OAI
