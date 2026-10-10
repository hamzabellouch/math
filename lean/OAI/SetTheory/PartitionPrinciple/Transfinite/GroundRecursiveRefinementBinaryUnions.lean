import OAI.SetTheory.PartitionPrinciple.Forcing.GroundForcingHistoryOrders
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRefinementVisibleLiftInsertions

namespace OAI


namespace PartitionPilot.Forcing
universe u

structure RecursiveRefinementDataHistory (M : TransitiveGround.{u})
    (rows T stages history : ZFSet.{u}) : Prop where
  data : RefinementDataHistory stages history T
  carrier : ∀ beta (d : Fin 15 → ZFSet.{u}),
    ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      d 7 = M.refinementHistoryForcing rows T beta (graphRestriction beta history)

namespace RecursiveRefinementDataHistory
variable {M : TransitiveGround.{u}} {rows T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M rows T stages history)
include run

theorem carrier_entry {beta Q : ZFSet.{u}}
    (entry : ZFSet.pair beta Q ∈ refinementDataHistoryField stages history 7) :
    Q = M.refinementHistoryForcing rows T beta (graphRestriction beta history) := by
  obtain ⟨_, d, packed, rfl⟩ := (pair_mem_refinementDataHistoryField stages history beta Q 7).1 entry
  exact run.carrier beta d packed

theorem cut_mem {row A : ZFSet.{u}}
    (member : ZFSet.pair row A ∈ M.refinementHistoryForcing rows T stages history)
    {beta : ZFSet.{u}} (hbeta : beta ∈ stages) :
    ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages history T) beta A) ∈
      M.refinementHistoryForcing rows T beta (graphRestriction beta history) := by
  have checked := ((M.mem_refinementHistoryForcing rows T stages history _).1 member).2
  obtain ⟨code, entry, d, equal, tests⟩ := checked beta hbeta
  rw [equal] at entry
  have lower := (stageTwoConditionCode_pair_iff M d _ beta row A).1 tests |>.1
  exact run.carrier beta d entry ▸ lower

theorem restrict {earlier : ZFSet.{u}} (ordinal : ordinalSetProperty earlier)
    (subset : earlier ⊆ stages) :
    RecursiveRefinementDataHistory M rows T earlier (graphRestriction earlier history) := by
  refine ⟨run.data.restrict subset, ?_⟩
  intro beta d entry
  have packed := (pair_mem_graphRestriction.1 entry).1
  have hbeta := (pair_mem_graphRestriction.1 entry).2
  rw [graphRestriction_restrict (ordinal.1 beta hbeta)]
  exact run.carrier beta d packed

end RecursiveRefinementDataHistory




namespace RecursiveRefinementDataHistory
variable {M : TransitiveGround.{u}} {rows T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M rows T stages history)
include run

theorem condition_iff_cuts (ordinal : ordinalSetProperty stages)
    (successors : ∀ beta ∈ stages, insert beta beta ∈ stages) (row A : ZFSet.{u}) :
    ForcingHistoryConditionCode M stages history (refinementDataHistoryLevels stages history T)
      (ZFSet.pair row A) ↔
      FlatHistoryCuts stages (refinementDataHistoryField stages history 7)
        (refinementDataHistoryLevels stages history T) row A := by
  constructor
  · intro valid
    exact ((forcingHistoryConditionCode_pair_decomposition run.data.function run.data.decoded row A).1 valid).1
  · intro cuts beta hbeta
    obtain ⟨code, entry⟩ := run.data.function.total hbeta
    obtain ⟨d, rfl⟩ := run.data.decoded beta code entry
    have hNext := successors beta hbeta
    have nextSubset := ordinal.1 (insert beta beta) hNext
    have below : beta ⊆ insert beta beta := fun _ member => ZFSet.mem_insert_of_mem beta member
    obtain ⟨Q, qEntry, member⟩ := cuts (insert beta beta) hNext
    rw [run.carrier_entry qEntry] at member
    have prefixValid := ((M.mem_refinementHistoryForcing rows T (insert beta beta)
      (graphRestriction (insert beta beta) history) _).1 member).2
    have prefixEntry : ZFSet.pair beta (refinementFormulaDataCode d) ∈
        graphRestriction (insert beta beta) history :=
      pair_mem_graphRestriction.2 ⟨entry, ZFSet.mem_insert _ _⟩
    have current := (forcingHistoryConditionCode_lookup_iff
      (run.data.function.restrict nextSubset)).1 prefixValid beta (ZFSet.mem_insert _ _)
      (refinementFormulaDataCode d) prefixEntry
    have currentGlobal := (packedSuccessorConditionCode_levels_congr M
      (refinementDataHistoryLevels (insert beta beta) (graphRestriction (insert beta beta) history) T)
      (refinementDataHistoryLevels stages history T) beta (refinementFormulaDataCode d)
      (ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages history T) (insert beta beta) A))
      (fun B => run.data.prefix_cut nextSubset below B)).1 current
    have covered : ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
        ∃ xi ∈ insert beta beta, ZFSet.pair (stageOneAssignment t u w) xi ∈
          refinementDataHistoryLevels stages history T := by
      intro t ht u hu w hw
      exact ⟨beta, ZFSet.mem_insert _ _, run.data.coverage beta hbeta d entry t ht u hu w hw⟩
    exact ⟨refinementFormulaDataCode d, entry,
      (packedSuccessorConditionCode_cut_iff M d (refinementDataHistoryLevels stages history T)
        beta (insert beta beta) row A below covered).1 currentGlobal⟩

theorem limit_eq (ordinal : ordinalSetProperty stages)
    (successors : ∀ beta ∈ stages, insert beta beta ∈ stages) :
    M.refinementHistoryForcing rows T stages history =
      M.flatLimitConditions rows (refinementDataHistoryIndices stages history) T stages
        (refinementDataHistoryField stages history 7) (refinementDataHistoryLevels stages history T) := by
  apply ZFSet.ext
  intro z
  rw [M.mem_refinementHistoryForcing, M.mem_flatLimitConditions]
  apply and_congr_right
  intro candidate
  obtain ⟨row, _, A, _, _, _, equal⟩ := (M.mem_stageOneCandidateBound _ _ _ _).1 candidate
  rw [equal, flatLimitConditionCode_pair]
  exact run.condition_iff_cuts ordinal successors row A

end RecursiveRefinementDataHistory



namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem forcingHistoryConditions_levels_congr (rows I T stages history first second : ZFSet.{u})
    (cuts : ∀ beta ∈ stages, ∀ A, assignmentCut first beta A = assignmentCut second beta A) :
    M.forcingHistoryConditions rows I T stages history first =
      M.forcingHistoryConditions rows I T stages history second := by
  apply ZFSet.ext
  intro z
  rw [M.mem_forcingHistoryConditions, M.mem_forcingHistoryConditions]
  exact and_congr Iff.rfl (forcingHistoryConditionCode_levels_congr M stages history first second z cuts)

end TransitiveGround
namespace RecursiveRefinementDataHistory
variable {M : TransitiveGround.{u}} {rows T alpha history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M rows T alpha history)
include run

theorem append (ordinal : ordinalSetProperty alpha) (d : Fin 15 → ZFSet.{u})
    (terms : d 6 = T) (literal : RefinementIndexLevelCode (d 0) alpha)
    (lower : d 7 = M.refinementHistoryForcing rows T alpha history) :
    RecursiveRefinementDataHistory M rows T (insert alpha alpha)
      (insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history) := by
  refine ⟨run.data.append (ZFSet.mem_irrefl alpha) d terms literal, ?_⟩
  intro beta fields entry
  rcases ZFSet.mem_insert_iff.1 entry with equal | old
  · obtain ⟨rfl, code⟩ := ZFSet.pair_inj.1 equal
    have same := refinementFormulaDataCode_injective code
    rw [graphRestriction_insert_of_not_mem (ZFSet.mem_irrefl beta), run.data.function.restriction_eq]
    exact (congrFun same 7).trans lower
  · have hbeta := run.data.function.pair_source old
    have outside : alpha ∉ beta := fun member =>
      ZFSet.mem_irrefl alpha (ordinal.1 beta hbeta alpha member)
    rw [graphRestriction_insert_of_not_mem outside]
    exact run.carrier beta fields old

theorem successor_eq (ordinal : ordinalSetProperty alpha) (d : Fin 15 → ZFSet.{u})
    (terms : d 6 = T) (literal : RefinementIndexLevelCode (d 0) alpha)
    (lower : d 7 = M.refinementHistoryForcing rows T alpha history) :
    let next := insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history
    M.refinementHistoryForcing rows T (insert alpha alpha) next =
      M.stageTwoConditions rows (refinementDataHistoryIndices (insert alpha alpha) next)
        (refinementDataHistoryLevels (insert alpha alpha) next T) alpha d := by
  let next := insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history
  let levels := refinementDataHistoryLevels (insert alpha alpha) next T
  let oldI := refinementDataHistoryIndices alpha history
  have extended := run.append ordinal d terms literal lower
  have subset : alpha ⊆ insert alpha alpha := fun _ member => ZFSet.mem_insert_of_mem alpha member
  have prefixHistory : graphRestriction alpha next = history := by
    rw [graphRestriction_insert_of_not_mem (ZFSet.mem_irrefl alpha), run.data.function.restriction_eq]
  have cuts : ∀ beta ∈ alpha, ∀ A,
      assignmentCut (refinementDataHistoryLevels alpha history T) beta A = assignmentCut levels beta A := by
    intro beta hbeta A
    have equal := extended.data.prefix_cut subset (ordinal.1 beta hbeta) A
    rw [prefixHistory] at equal
    exact equal
  have lowerGlobal : d 7 = M.forcingHistoryConditions rows oldI (d 6) alpha history levels := by
    calc
      d 7 = M.refinementHistoryForcing rows T alpha history := lower
      _ = M.forcingHistoryConditions rows oldI T alpha history levels :=
        M.forcingHistoryConditions_levels_congr rows oldI T alpha history _ levels cuts
      _ = M.forcingHistoryConditions rows oldI (d 6) alpha history levels := by rw [terms]
  have coverage : ForcingHistoryLevelCoverage alpha history levels := by
    intro beta hbeta fields entry t ht u hu w hw
    exact extended.data.coverage beta (ZFSet.mem_insert_of_mem alpha hbeta) fields
      (ZFSet.mem_insert_of_mem _ entry) t ht u hu w hw
  simpa only [terms, TransitiveGround.refinementHistoryForcing, levels, next] using
    (M.forcingHistoryConditions_successor_eq rows oldI (refinementDataHistoryIndices (insert alpha alpha) next)
      alpha history levels d run.data.function ordinal coverage lowerGlobal)

end RecursiveRefinementDataHistory
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.RecursiveRefinementDataHistory
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows T alpha history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M rows T alpha history)
include run

theorem successor_insert_extension
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (ordinal : ordinalSetProperty alpha) (d : Fin 15 → ZFSet.{u})
    (terms : d 6 = T) (literal : RefinementIndexLevelCode (d 0) alpha)
    (lower : d 7 = M.refinementHistoryForcing rows T alpha history)
    (hI : d 0 ∈ M.sets) (hT : T ∈ M.sets)
    (rowOrder : ZFSet.{u}) (rowOrderLaw : PartialOrderCode rows rowOrder)
    {row A t u w : ZFSet.{u}} (index : t ∈ d 0) (first : u ∈ T) (second : w ∈ T) :
    let next := insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history
    let levels := refinementDataHistoryLevels (insert alpha alpha) next T
    let P := M.refinementHistoryForcing rows T (insert alpha alpha) next
    ZFSet.pair row A ∈ P →
    stageOneRawSingle M d t u w (ZFSet.pair row (assignmentCut levels alpha A)) →
    (∀ v ∈ T, ∀ z ∈ T, stageOneAssignment t v z ∈ A →
      stageOneRawCollision M d t v u z w (ZFSet.pair row (assignmentCut levels alpha A))) →
    (∀ v ∈ T, ∀ z ∈ T, stageOneAssignment t v z ∈ A →
      stageOneRawCollision M d t u v w z (ZFSet.pair row (assignmentCut levels alpha A))) →
    stageOneRawCollision M d t u u w w (ZFSet.pair row (assignmentCut levels alpha A)) →
    ZFSet.pair row (insert (stageOneAssignment t u w) A) ∈ P ∧
      assignmentCut levels alpha (insert (stageOneAssignment t u w) A) =
        assignmentCut levels alpha A ∧
      ZFSet.pair (ZFSet.pair row (insert (stageOneAssignment t u w) A)) (ZFSet.pair row A) ∈
        M.refinementHistoryOrder rows rowOrder T (insert alpha alpha) next := by
  dsimp only
  intro member single old_new new_old self
  let next := insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history
  have extended := run.append ordinal d terms literal lower
  have stored : ZFSet.pair alpha (refinementFormulaDataCode d) ∈ next := ZFSet.mem_insert _ _
  have level := extended.data.coverage alpha (ZFSet.mem_insert alpha alpha) d stored
    t index u (terms.symm ▸ first) w (terms.symm ▸ second)
  have function : ZFSet.IsFunc
      (stageOneAssignments (refinementDataHistoryIndices (insert alpha alpha) next) (d 6))
      (insert alpha alpha) (refinementDataHistoryLevels (insert alpha alpha) next T) := by
    simpa only [terms] using extended.data.levels_function
  have ground := M.stageOneAssignment_mem pairing (M.transitive hI index)
    (M.transitive hT first) (M.transitive hT second)
  have successor := run.successor_eq ordinal d terms literal lower
  have flat := successor ▸ member
  have result := M.stageTwoConditions_insert pairing unions powers separation infinite d
    function level ground flat single
    (fun v hv z hz old => old_new v (terms ▸ hv) z (terms ▸ hz) old)
    (fun v hv z hz old => new_old v (terms ▸ hv) z (terms ▸ hz) old) self
  have inserted := successor.symm ▸ result.1
  have candidate := ((M.mem_refinementHistoryForcing rows T (insert alpha alpha) next _).1 member).1
  have rowMember := ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate).1
  refine ⟨inserted, result.2, ?_⟩
  exact (M.pair_mem_refinementHistoryOrder rows rowOrder T (insert alpha alpha) next _ _ _ _).2
    ⟨inserted, member, rowOrderLaw.refl row rowMember, fun _ h => ZFSet.mem_insert_of_mem _ h⟩

end PartitionPilot.Forcing.RecursiveRefinementDataHistory



namespace PartitionPilot.Forcing
universe u

structure RecursiveRefinementOrderHistory (M : TransitiveGround.{u})
    (rows rowOrder T stages history : ZFSet.{u}) : Prop where
  carriers : RecursiveRefinementDataHistory M rows T stages history
  order : ∀ beta (d : Fin 15 → ZFSet.{u}),
    ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      d 8 = M.refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)

namespace RecursiveRefinementDataHistory
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}

theorem cut_order (run : RecursiveRefinementDataHistory M rows T stages history)
    {q A p D beta : ZFSet.{u}}
    (below : ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈
      M.refinementHistoryOrder rows rowOrder T stages history) (hbeta : beta ∈ stages) :
    ZFSet.pair (ZFSet.pair q (assignmentCut (refinementDataHistoryLevels stages history T) beta A))
      (ZFSet.pair p (assignmentCut (refinementDataHistoryLevels stages history T) beta D)) ∈
      M.refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history) := by
  obtain ⟨hq, hp, rowsBelow, data⟩ := (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history q A p D).1 below
  exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history) _ _ _ _).2
    ⟨run.cut_mem hq hbeta, run.cut_mem hp hbeta, rowsBelow, assignmentCut_mono data⟩

end RecursiveRefinementDataHistory
namespace RecursiveRefinementOrderHistory
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
include run

theorem lower_order {q A p D beta : ZFSet.{u}} (d : Fin 15 → ZFSet.{u})
    (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
    (below : ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈
      M.refinementHistoryOrder rows rowOrder T stages history) :
    ZFSet.pair (ZFSet.pair q (assignmentCut (refinementDataHistoryLevels stages history T) beta A))
      (ZFSet.pair p (assignmentCut (refinementDataHistoryLevels stages history T) beta D)) ∈ d 8 :=
  (run.order beta d entry).symm ▸ run.carriers.cut_order below (run.carriers.data.function.pair_source entry)

theorem restrict {earlier : ZFSet.{u}} (ordinal : ordinalSetProperty earlier)
    (subset : earlier ⊆ stages) :
    RecursiveRefinementOrderHistory M rows rowOrder T earlier (graphRestriction earlier history) := by
  refine ⟨run.carriers.restrict ordinal subset, ?_⟩
  intro beta d entry
  have packed := (pair_mem_graphRestriction.1 entry).1
  have hbeta := (pair_mem_graphRestriction.1 entry).2
  rw [graphRestriction_restrict (ordinal.1 beta hbeta)]
  exact run.order beta d packed

theorem append (ordinal : ordinalSetProperty stages) (d : Fin 15 → ZFSet.{u})
    (terms : d 6 = T) (literal : RefinementIndexLevelCode (d 0) stages)
    (lower : d 7 = M.refinementHistoryForcing rows T stages history)
    (lowerOrder : d 8 = M.refinementHistoryOrder rows rowOrder T stages history) :
    RecursiveRefinementOrderHistory M rows rowOrder T (insert stages stages)
      (insert (ZFSet.pair stages (refinementFormulaDataCode d)) history) := by
  refine ⟨run.carriers.append ordinal d terms literal lower, ?_⟩
  intro beta fields entry
  rcases ZFSet.mem_insert_iff.1 entry with equal | old
  · obtain ⟨rfl, code⟩ := ZFSet.pair_inj.1 equal
    have same := refinementFormulaDataCode_injective code
    rw [graphRestriction_insert_of_not_mem (ZFSet.mem_irrefl beta), run.carriers.data.function.restriction_eq]
    exact (congrFun same 8).trans lowerOrder
  · have hbeta := run.carriers.data.function.pair_source old
    have outside : stages ∉ beta := fun member =>
      ZFSet.mem_irrefl stages (ordinal.1 beta hbeta stages member)
    rw [graphRestriction_insert_of_not_mem outside]
    exact run.order beta fields old

end RecursiveRefinementOrderHistory





namespace FunctionGraphOn

theorem restriction_successor_entry {stages history alpha value : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (entry : ZFSet.pair alpha value ∈ history) :
    graphRestriction (Insert.insert alpha alpha) history =
      Insert.insert (ZFSet.pair alpha value) (graphRestriction alpha history) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨beta, hbeta, code, rfl, stored⟩ := mem_graphRestriction.1 member
    rcases ZFSet.mem_insert_iff.1 hbeta with equal | before
    · subst beta
      have same := function.unique stored entry
      exact ZFSet.mem_insert_iff.2 (Or.inl (congrArg (ZFSet.pair alpha) same))
    · exact ZFSet.mem_insert_of_mem _ (pair_mem_graphRestriction.2 ⟨stored, before⟩)
  · intro member
    rcases ZFSet.mem_insert_iff.1 member with equal | before
    · rw [equal]
      exact pair_mem_graphRestriction.2 ⟨entry, ZFSet.mem_insert alpha alpha⟩
    · obtain ⟨beta, hbeta, code, rfl, stored⟩ := mem_graphRestriction.1 before
      exact pair_mem_graphRestriction.2 ⟨stored, ZFSet.mem_insert_of_mem alpha hbeta⟩

end FunctionGraphOn

namespace RecursiveRefinementDataHistory
open SetFormula
variable {M : TransitiveGround.{u}} {rows T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M rows T stages history)
include run

theorem stored_successor_eq (ordinal : ordinalSetProperty stages)
    {alpha : ZFSet.{u}} (member : alpha ∈ stages) (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history) :
    let next := graphRestriction (insert alpha alpha) history
    M.refinementHistoryForcing rows T (insert alpha alpha) next =
      M.stageTwoConditions rows (refinementDataHistoryIndices (insert alpha alpha) next)
        (refinementDataHistoryLevels (insert alpha alpha) next T) alpha fields := by
  dsimp only
  rw [run.data.function.restriction_successor_entry stored]
  exact (run.restrict (ordinalSetProperty_member ordinal member) (ordinal.1 alpha member)).successor_eq
    (ordinalSetProperty_member ordinal member) fields (run.data.terms alpha fields stored)
    (run.data.literal alpha fields stored) (run.carrier alpha fields stored)

theorem stored_successor_insert_extension
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (ordinal : ordinalSetProperty stages) {alpha : ZFSet.{u}} (member : alpha ∈ stages)
    (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history)
    (hI : fields 0 ∈ M.sets) (hT : T ∈ M.sets)
    (rowOrder : ZFSet.{u}) (rowOrderLaw : PartialOrderCode rows rowOrder)
    {row A idx u w : ZFSet.{u}} (index : idx ∈ fields 0) (first : u ∈ T) (second : w ∈ T) :
    let next := graphRestriction (insert alpha alpha) history
    let levels := refinementDataHistoryLevels (insert alpha alpha) next T
    let P := M.refinementHistoryForcing rows T (insert alpha alpha) next
    ZFSet.pair row A ∈ P →
    stageOneRawSingle M fields idx u w (ZFSet.pair row (assignmentCut levels alpha A)) →
    (∀ v ∈ T, ∀ z ∈ T, stageOneAssignment idx v z ∈ A →
      stageOneRawCollision M fields idx v u z w (ZFSet.pair row (assignmentCut levels alpha A))) →
    (∀ v ∈ T, ∀ z ∈ T, stageOneAssignment idx v z ∈ A →
      stageOneRawCollision M fields idx u v w z (ZFSet.pair row (assignmentCut levels alpha A))) →
    stageOneRawCollision M fields idx u u w w (ZFSet.pair row (assignmentCut levels alpha A)) →
    ZFSet.pair row (insert (stageOneAssignment idx u w) A) ∈ P ∧
      assignmentCut levels alpha (insert (stageOneAssignment idx u w) A) =
        assignmentCut levels alpha A ∧
      ZFSet.pair (ZFSet.pair row (insert (stageOneAssignment idx u w) A)) (ZFSet.pair row A) ∈
        M.refinementHistoryOrder rows rowOrder T (insert alpha alpha) next := by
  dsimp only
  rw [run.data.function.restriction_successor_entry stored]
  exact (run.restrict (ordinalSetProperty_member ordinal member) (ordinal.1 alpha member)).successor_insert_extension
    pairing unions powers separation infinite (ordinalSetProperty_member ordinal member) fields
    (run.data.terms alpha fields stored) (run.data.literal alpha fields stored)
    (run.carrier alpha fields stored) hI hT rowOrder rowOrderLaw index first second

end RecursiveRefinementDataHistory
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable {row A B : ZFSet.{u}}
local notation "levels" => refinementDataHistoryLevels stages history T
include run

theorem binary_union_mem_of_candidates (ordinal : ordinalSetProperty stages)
    (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ C lower stronger, stageOneRawTests M d C lower →
        ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d C stronger)
    (first : ZFSet.pair row A ∈ M.refinementHistoryForcing rows T stages history)
    (second : ZFSet.pair row B ∈ M.refinementHistoryForcing rows T stages history)
    (rowSelf : ZFSet.pair row row ∈ rowOrder) (agreement : AssignmentIndexAgreement A B)
    (candidate : ZFSet.pair row (A ∪ B) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T)
    (candidates : ∀ gamma ∈ stages, ZFSet.pair row (assignmentCut levels gamma (A ∪ B)) ∈
      M.stageOneCandidateBound rows
        (refinementDataHistoryIndices gamma (graphRestriction gamma history)) T) :
    ZFSet.pair row (A ∪ B) ∈ M.refinementHistoryForcing rows T stages history := by
  have subsetA : A ⊆ A ∪ B := fun _ h => ZFSet.mem_union.2 (Or.inl h)
  have subsetB : B ⊆ A ∪ B := fun _ h => ZFSet.mem_union.2 (Or.inr h)
  have firstTests := ((M.mem_refinementHistoryForcing rows T stages history _).1 first).2
  have secondTests := ((M.mem_refinementHistoryForcing rows T stages history _).1 second).2
  have step (beta : ZFSet.{u}) (hbeta : beta ∈ stages) (d : Fin 15 → ZFSet.{u})
      (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
      (proved : ZFSet.pair row (assignmentCut levels beta (A ∪ B)) ∈
        M.refinementHistoryForcing rows T beta (graphRestriction beta history)) :
      stageOneRawTests M d (A ∪ B) (ZFSet.pair row (assignmentCut levels beta (A ∪ B))) := by
    have storedA := (forcingHistoryConditionCode_lookup_iff run.carriers.data.function).1 firstTests
      beta hbeta (refinementFormulaDataCode d) entry
    have checkedA := (stageTwoConditionCode_pair_iff M d _ beta row A).1
      ((packedSuccessorConditionCode_code_iff M _ beta d _).1 storedA)
    have storedB := (forcingHistoryConditionCode_lookup_iff run.carriers.data.function).1 secondTests
      beta hbeta (refinementFormulaDataCode d) entry
    have checkedB := (stageTwoConditionCode_pair_iff M d _ beta row B).1
      ((packedSuccessorConditionCode_code_iff M _ beta d _).1 storedB)
    have belowA : ZFSet.pair (ZFSet.pair row (assignmentCut levels beta (A ∪ B)))
        (ZFSet.pair row (assignmentCut levels beta A)) ∈ d 8 := by
      rw [run.order beta d entry]
      exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)
        _ _ _ _).2 ⟨proved, run.carriers.cut_mem first hbeta, rowSelf, assignmentCut_mono subsetA⟩
    have belowB : ZFSet.pair (ZFSet.pair row (assignmentCut levels beta (A ∪ B)))
        (ZFSet.pair row (assignmentCut levels beta B)) ∈ d 8 := by
      rw [run.order beta d entry]
      exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)
        _ _ _ _).2 ⟨proved, run.carriers.cut_mem second hbeta, rowSelf, assignmentCut_mono subsetB⟩
    exact stageOneRawTests_binary_union M d agreement
      (mono beta d entry A _ _ checkedA.2 belowA) (mono beta d entry B _ _ checkedB.2 belowB)
  have earlier : ∀ gamma ∈ stages, ZFSet.pair row (assignmentCut levels gamma (A ∪ B)) ∈
      M.refinementHistoryForcing rows T gamma (graphRestriction gamma history) := by
    intro gamma
    induction gamma using ZFSet.inductionOn with
    | h gamma ih =>
      intro hgamma
      apply (M.mem_refinementHistoryForcing rows T gamma (graphRestriction gamma history) _).2
      refine ⟨candidates gamma hgamma, ?_⟩
      intro beta hbeta
      have betaFull := ordinal.1 gamma hgamma beta hbeta
      have betaSubset := ordinal.2 gamma hgamma beta hbeta
      obtain ⟨data, entry⟩ := run.carriers.data.function.total betaFull
      obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
      have proved := ih beta hbeta betaFull
      have sameCut := run.carriers.data.prefix_cut (ordinal.1 gamma hgamma) betaSubset
        (assignmentCut levels gamma (A ∪ B))
      refine ⟨refinementFormulaDataCode d, pair_mem_graphRestriction.2 ⟨entry, hbeta⟩, ?_⟩
      apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
      apply (stageTwoConditionCode_pair_iff M d _ beta row _).2
      rw [sameCut, assignmentCut_nested betaSubset]
      refine ⟨(run.carriers.carrier beta d entry).symm ▸ proved, ?_⟩
      exact stageOneRawTests_transfer M d _ (step beta betaFull d entry proved)
        (fun _ _ _ _ _ _ member => assignmentCut_subset levels gamma (A ∪ B) member)
  apply (M.mem_refinementHistoryForcing rows T stages history _).2
  refine ⟨candidate, ?_⟩
  intro beta hbeta
  obtain ⟨data, entry⟩ := run.carriers.data.function.total hbeta
  obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
  refine ⟨refinementFormulaDataCode d, entry, ?_⟩
  apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
  apply (stageTwoConditionCode_pair_iff M d _ beta row _).2
  exact ⟨(run.carriers.carrier beta d entry).symm ▸ earlier beta hbeta,
    step beta hbeta d entry (earlier beta hbeta)⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory



namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
include run

theorem tests_at_valid_larger_cut
    {beta row sourceRow A largerA : ZFSet.{u}} (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair beta (refinementFormulaDataCode fields) ∈ history)
    (mono : ∀ C lower stronger, stageOneRawTests M fields C lower →
      ZFSet.pair stronger lower ∈ fields 8 → stageOneRawTests M fields C stronger)
    (source : ZFSet.pair sourceRow A ∈ M.refinementHistoryForcing rows T stages history)
    (rowBelow : ZFSet.pair row sourceRow ∈ rowOrder) (subset : A ⊆ largerA)
    (validCut : ZFSet.pair row
      (assignmentCut (refinementDataHistoryLevels stages history T) beta largerA) ∈
      M.refinementHistoryForcing rows T beta (graphRestriction beta history)) :
    let levels := refinementDataHistoryLevels stages history T
    let stronger := ZFSet.pair row (assignmentCut levels beta largerA)
    let old := ZFSet.pair sourceRow (assignmentCut levels beta A)
    ZFSet.pair stronger old ∈ fields 8 ∧ stageOneRawTests M fields A stronger := by
  have member := run.carriers.data.function.pair_source stored
  have originalTests := ((M.mem_refinementHistoryForcing rows T stages history _).1 source).2
  have storedTests := (forcingHistoryConditionCode_lookup_iff run.carriers.data.function).1 originalTests
    beta member (refinementFormulaDataCode fields) stored
  have checked := (stageTwoConditionCode_pair_iff M fields _ beta sourceRow A).1
    ((packedSuccessorConditionCode_code_iff M _ beta fields _).1 storedTests)
  have below : ZFSet.pair
      (ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages history T) beta largerA))
      (ZFSet.pair sourceRow (assignmentCut (refinementDataHistoryLevels stages history T) beta A)) ∈ fields 8 := by
    rw [run.order beta fields stored]
    exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)
      _ _ _ _).2 ⟨validCut, run.carriers.cut_mem source member, rowBelow, assignmentCut_mono subset⟩
  exact ⟨below, mono A _ _ checked.2 below⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory



namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
include run pairing unions powers separation infinite choice hStages hHistory hT

theorem binary_union_extension (ordinal : ordinalSetProperty stages)
    (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ C lower stronger, stageOneRawTests M d C lower →
        ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d C stronger)
    (rowOrderLaw : PartialOrderCode rows rowOrder) {row A B : ZFSet.{u}}
    (first : ZFSet.pair row A ∈ M.refinementHistoryForcing rows T stages history)
    (second : ZFSet.pair row B ∈ M.refinementHistoryForcing rows T stages history)
    (agreement : AssignmentIndexAgreement A B) :
    ZFSet.pair row (A ∪ B) ∈ M.refinementHistoryForcing rows T stages history ∧
      ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair row A) ∈
        M.refinementHistoryOrder rows rowOrder T stages history ∧
      ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair row B) ∈
        M.refinementHistoryOrder rows rowOrder T stages history := by
  have firstCandidate := ((M.mem_refinementHistoryForcing rows T stages history _).1 first).1
  have secondCandidate := ((M.mem_refinementHistoryForcing rows T stages history _).1 second).1
  obtain ⟨hrow, hA, subsetA, smallA⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 firstCandidate
  obtain ⟨_, hB, subsetB, smallB⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 secondCandidate
  have rowSelf := rowOrderLaw.refl row hrow
  have candidate : ZFSet.pair row (A ∪ B) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T := by
    apply (M.pair_mem_stageOneCandidateBound _ _ _ _ _).2
    refine ⟨hrow, M.binary_union_mem pairing unions hA hB, ?_,
      M.groundCountable_binary_union pairing unions powers separation infinite choice hA hB smallA smallB⟩
    intro z member
    exact (ZFSet.mem_union.1 member).elim (fun h => subsetA h) (fun h => subsetB h)
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT
  have member := run.binary_union_mem_of_candidates ordinal mono first second rowSelf agreement candidate
    (fun beta hbeta => M.refinementDataHistoryCandidate_cut separation run.carriers.data
      (ordinal.1 beta hbeta) hLevels (M.transitive hStages hbeta) (M.omega_mem separation infinite) candidate)
  refine ⟨member, ?_, ?_⟩
  · exact (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).2
      ⟨member, first, rowSelf, fun _ h => ZFSet.mem_union.2 (Or.inl h)⟩
  · exact (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).2
      ⟨member, second, rowSelf, fun _ h => ZFSet.mem_union.2 (Or.inr h)⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory

end OAI
