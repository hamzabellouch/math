import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCarrierSequences
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundPreparedWitnessSelections
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRecordedPreparationSupportInclusions

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {R : Type u} [PartialOrder R]

theorem fixedFairPreparationLimit_supportPrepared
    (c : Presentation R)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {T stages packed nodes E prepSelector : ZFSet.{u}}
    (run : RecursiveRefinementOrderHistory M c.carrier c.conditionOrder T stages packed)
    (environments : ∀ alpha (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed →
        StoredPreparationEnvironment M fields)
    (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (prepSelected : prepSelector ⊆ M.varyingPreparationRelation stages packed
      (M.refinementHistoryForcing c.carrier T stages packed)
      (M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed) nodes T) :
    let Q := M.refinementHistoryForcing c.carrier T stages packed
    let order := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
    let B := M.groundSmallSubsets
      (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
    let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
    let data := flatCarrierData c Q B shape
    ∀ (seq : Nat → SetMembers Q) (events : Nat → ZFSet.{u}),
      ZFSet.IsFunc ZFSet.omega E (familyCodeGraph natSetCode events) →
    ∀ limit : SetMembers Q,
      (∀ n, ZFSet.pair (SetMembers.raw limit) (SetMembers.raw (seq n)) ∈ order) →
      (∀ x ∈ SetMembers.raw (data limit),
        ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
          Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
          x ∈ SetMembers.raw (data (seq i)) ∧
          ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
          ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages packed T ∧
          (∀ k, Nat.pair i j ≤ k →
            x ∈ assignmentOnIndices (fields 0) T (SetMembers.raw (data (seq k)))) ∧
          ∃ y ∈ M.preparationWitnessBound nodes T Q, ∃ payload,
            y = ZFSet.pair (SetMembers.raw (seq (Nat.pair i j + 1))) payload ∧
            ZFSet.pair (ZFSet.pair alpha (SetMembers.raw (seq (Nat.pair i j)))) y ∈ prepSelector ∧
            events (Nat.pair i j + 1) = ZFSet.pair alpha y) →
      StoredSupportPreparedConditionCode M c.carrier T stages packed nodes (SetMembers.raw limit)
        (M.preparationUsedSupportUnion nodes E (familyCodeGraph natSetCode events)) := by
  let Q := M.refinementHistoryForcing c.carrier T stages packed
  let order := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let B := M.groundSmallSubsets
    (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
  let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
  let data := flatCarrierData c Q B shape
  dsimp only
  intro seq events eventFunction limit below visits limitRow limitA limitCode x hx
  have limitData : SetMembers.raw (data limit) = limitA :=
    (ZFSet.pair_inj.1 ((flatCarrier_coordinates c Q B shape limit).symm.trans limitCode)).2
  have inData : x ∈ SetMembers.raw (data limit) := limitData.symm ▸ hx
  obtain ⟨i, j, alpha, hAlpha, fields, _unpaired, _born, _early, stored, _level,
    retained, y, _hy, payload, yCode, selected, eventAt⟩ := visits x inData
  let n := Nat.pair i j
  have relationEntry := prepSelected selected
  rw [yCode] at relationEntry
  obtain ⟨_, _inputMember, bounded, other, otherStored, terms, nodeCarrier, meetCode, code⟩ :=
    (M.pair_mem_varyingPreparationRelation stages packed Q order nodes T alpha
      (SetMembers.raw (seq n)) (ZFSet.pair (SetMembers.raw (seq (n + 1))) payload)).1 relationEntry
  have same : other = fields :=
    refinementFormulaDataCode_injective (run.carriers.data.function.unique otherStored stored)
  subst other
  obtain ⟨sourceRow, sourceA, output, k, enumerations, q,
    inputCode, outputCode, _visitBelow, cut, family⟩ := code
  have sourceData : SetMembers.raw (data (seq n)) = sourceA :=
    (ZFSet.pair_inj.1 ((flatCarrier_coordinates c Q B shape (seq n)).symm.trans inputCode)).2
  obtain ⟨outputEq, payloadEq⟩ := ZFSet.pair_inj.1 outputCode
  subst output
  rw [payloadEq] at bounded
  obtain ⟨_, hkBound, heBound⟩ := (M.mem_preparationWitnessBound nodes T Q
    (SetMembers.raw (seq (n + 1))) k enumerations).1 bounded
  have hk := ((M.mem_groundRelations _ _ k).1 hkBound).1
  have hEnumerations := ((M.mem_groundRelations _ _ enumerations).1 heBound).1
  have hSourceA : sourceA ∈ M.sets := sourceData ▸
    ((M.mem_groundSmallSubsets _ _ _).1 (SetMembers.raw_mem (data (seq n)))).1
  have sourceMember : ZFSet.pair sourceRow sourceA ∈ Q := inputCode ▸ SetMembers.raw_mem (seq n)
  have sourceBelow := below n
  rw [limitCode, inputCode] at sourceBelow
  have sourceSubset := ((M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T
    stages packed limitRow limitA sourceRow sourceA).1 sourceBelow).2.2.2
  have sourceSelected : x ∈ assignmentOnIndices (fields 0) T sourceA :=
    sourceData ▸ retained n (Nat.le_refl n)
  have environment := environments alpha fields stored
  obtain ⟨rCut, hrCut, finalCut, _cutBelow, finalFamily⟩ :=
    M.storedPreparationFamily_cut_mono pairing unions powers separation collection run fields
      environment stored hSourceA (SetMembers.raw_mem limit) (below (n + 1)) cut family
  have recorded : ZFSet.pair (natSetCode (n + 1))
      (ZFSet.pair alpha (ZFSet.pair (SetMembers.raw (seq (n + 1)))
        (ZFSet.pair k enumerations))) ∈ familyCodeGraph natSetCode events := by
    apply (mem_familyCodeGraph natSetCode events _).2
    refine ⟨n + 1, ?_⟩
    rw [eventAt, yCode, payloadEq]
  have supportBound := M.recordedCertificateUsedSupports_subset separation hNodes hE
    eventFunction recorded
  exact ⟨alpha, hAlpha, fields, stored, terms, nodeCarrier, meetCode, environment,
    sourceRow, sourceA, hSourceA, sourceMember, sourceSubset, sourceSelected,
    k, hk, enumerations, hEnumerations, rCut, hrCut, finalCut, finalFamily, supportBound⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
