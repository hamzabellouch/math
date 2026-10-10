import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRawPreparedFamilyConditionPersistence
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRecursiveRefinementBinaryUnions

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization
universe u

structure StoredPreparationEnvironment (M : TransitiveGround.{u})
    (fields : Fin 15 → ZFSet.{u}) : Prop where
  order : PartialOrderCode (fields 7) (fields 8)
  ground : ∀ j, fields j ∈ M.sets
  names_valid : ∀ z ∈ fields 14, IsName (SetMembers.presentation (fields 7)) z
  visibility_valid : ∀ v V, ZFSet.pair v V ∈ fields 13 → v ∈ fields 10 →
    IsName (SetMembers.presentation (fields 7)) V

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
include run

theorem preparationCut_strengthens
    {alpha r p q : ZFSet.{u}} (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history)
    (stronger : r ∈ M.refinementHistoryForcing rows T stages history)
    (below : ZFSet.pair r p ∈ M.refinementHistoryOrder rows rowOrder T stages history)
    (selected : ZFSet.pair p q ∈ rowAssignmentCutGraph
      (M.refinementHistoryForcing rows T stages history) (fields 7)
      (refinementDataHistoryLevels stages history T) alpha) :
    ∃ rCut, rCut ∈ fields 7 ∧ q ∈ fields 7 ∧
      ZFSet.pair r rCut ∈ rowAssignmentCutGraph
        (M.refinementHistoryForcing rows T stages history) (fields 7)
        (refinementDataHistoryLevels stages history T) alpha ∧
      ZFSet.pair rCut q ∈ fields 8 := by
  obtain ⟨_, oldRow, oldA, equal⟩ := (mem_rowAssignmentCutGraph _ _ _ _ _).1 selected
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  have oldValid := ((pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).1 selected).2.1
  obtain ⟨newRow, _, newA, _, rfl⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape rows T stages history stronger)
  have member := run.carriers.data.function.pair_source stored
  have newValid := (run.carriers.carrier alpha fields stored).symm ▸
    run.carriers.cut_mem stronger member
  refine ⟨ZFSet.pair newRow
      (assignmentCut (refinementDataHistoryLevels stages history T) alpha newA),
    newValid, oldValid, ?_, run.lower_order fields stored below⟩
  exact (pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).2 ⟨stronger, newValid, rfl⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem storedPreparationFamily_cut_mono
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {rows rowOrder T stages history alpha r p q A meet C E k enumerations : ZFSet.{u}}
    (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
    (fields : Fin 15 → ZFSet.{u}) (environment : StoredPreparationEnvironment M fields)
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history)
    (hA : A ∈ M.sets)
    (stronger : r ∈ M.refinementHistoryForcing rows T stages history)
    (below : ZFSet.pair r p ∈ M.refinementHistoryOrder rows rowOrder T stages history)
    (selected : ZFSet.pair p q ∈ rowAssignmentCutGraph
      (M.refinementHistoryForcing rows T stages history) (fields 7)
      (refinementDataHistoryLevels stages history T) alpha)
    (code : PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
      meet (fields 14) (fields 13) (fields 9) ZFSet.omega
      (M.storedPreparationRequests A fields) C E k enumerations) :
    ∃ rCut, rCut ∈ fields 7 ∧
      ZFSet.pair r rCut ∈ rowAssignmentCutGraph
        (M.refinementHistoryForcing rows T stages history) (fields 7)
        (refinementDataHistoryLevels stages history T) alpha ∧
      ZFSet.pair rCut q ∈ fields 8 ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) rCut (fields 10) (fields 11)
        meet (fields 14) (fields 13) (fields 9) ZFSet.omega
        (M.storedPreparationRequests A fields) C E k enumerations := by
  obtain ⟨rCut, hrCut, hq, cut, lowerBelow⟩ :=
    run.preparationCut_strengthens fields stored stronger below selected
  have requestsGround := M.storedPreparationRequests_mem pairing unions powers separation
    hA fields environment.ground
  have requestsValid : ∀ z ∈ M.storedPreparationRequests A fields,
      IsName (SetMembers.presentation (fields 7)) z := by
    intro z hz
    rcases ZFSet.mem_union.1 hz with left | right
    · exact environment.names_valid z ((mem_relationImage _ _ _ _).1 left).1
    · exact environment.names_valid z ((mem_relationImage _ _ _ _).1 right).1
  refine ⟨rCut, hrCut, cut, lowerBelow, ?_⟩
  exact M.preparedCertificateFamilyCode_raw_condition_mono pairing unions powers separation collection
    (fields 7) (fields 8) (fields 10) (fields 11) meet (fields 14) (fields 13) (fields 9)
    ZFSet.omega (M.storedPreparationRequests A fields) C E k enumerations environment.order
    (environment.ground 7) (environment.ground 8) (environment.ground 13)
    environment.visibility_valid (environment.ground 14) environment.names_valid
    requestsGround requestsValid q rCut hq hrCut lowerBelow code

end PartitionPilot.Forcing.TransitiveGround

end OAI
