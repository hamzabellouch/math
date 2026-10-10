import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStoredPreparedFamilyActions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRetainedPreparationSelections
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundStoredPreparationFamilyPersistence
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundStoredVisitCertificates

namespace OAI


namespace PartitionPilot.Forcing
universe u

def StoredPreparedConditionCode (M : TransitiveGround.{u})
    (rows T stages history nodes p : ZFSet.{u}) : Prop :=
  let Q := M.refinementHistoryForcing rows T stages history
  ∀ row A, p = ZFSet.pair row A → ∀ x ∈ A,
    ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history ∧
      fields 6 = T ∧ fields 10 = nodes ∧
      MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
      StoredPreparationEnvironment M fields ∧
    ∃ sourceRow sourceA, sourceA ∈ M.sets ∧ ZFSet.pair sourceRow sourceA ∈ Q ∧
      sourceA ⊆ A ∧ x ∈ assignmentOnIndices (fields 0) T sourceA ∧
    ∃ k ∈ M.sets, ∃ enumerations ∈ M.sets, ∃ q ∈ fields 7,
      ZFSet.pair p q ∈ rowAssignmentCutGraph Q (fields 7)
        (refinementDataHistoryLevels stages history T) alpha ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
        (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
        ZFSet.omega (M.storedPreparationRequests sourceA fields)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) k enumerations





def StoredSupportPreparedConditionCode (M : TransitiveGround.{u})
    (rows T stages history nodes p S : ZFSet.{u}) : Prop :=
  let Q := M.refinementHistoryForcing rows T stages history
  ∀ row A, p = ZFSet.pair row A → ∀ x ∈ A,
    ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history ∧
      fields 6 = T ∧ fields 10 = nodes ∧
      MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
      StoredPreparationEnvironment M fields ∧
    ∃ sourceRow sourceA, sourceA ∈ M.sets ∧ ZFSet.pair sourceRow sourceA ∈ Q ∧
      sourceA ⊆ A ∧ x ∈ assignmentOnIndices (fields 0) T sourceA ∧
    ∃ k ∈ M.sets, ∃ enumerations ∈ M.sets, ∃ q ∈ fields 7,
      ZFSet.pair p q ∈ rowAssignmentCutGraph Q (fields 7)
        (refinementDataHistoryLevels stages history T) alpha ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
        (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
        ZFSet.omega (M.storedPreparationRequests sourceA fields)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) k enumerations ∧
      certificateUsedSupports nodes k ⊆ S

theorem StoredSupportPreparedConditionCode.forget
    {M : TransitiveGround.{u}} {rows T stages history nodes p S : ZFSet.{u}}
    (prepared : StoredSupportPreparedConditionCode M rows T stages history nodes p S) :
    StoredPreparedConditionCode M rows T stages history nodes p := by
  intro row A equal x member
  obtain ⟨alpha, hAlpha, fields, stored, terms, nodeCarrier, meet, environment,
    sourceRow, sourceA, hSourceA, source, subset, selected,
    k, hk, enumerations, he, q, hq, cut, family, _supportBound⟩ := prepared row A equal x member
  exact ⟨alpha, hAlpha, fields, stored, terms, nodeCarrier, meet, environment,
    sourceRow, sourceA, hSourceA, source, subset, selected,
    k, hk, enumerations, he, q, hq, cut, family⟩

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def preparedWitnessSelections (rows T stages packed nodes p A : ZFSet.{u}) : ZFSet.{u} :=
  let Q := M.refinementHistoryForcing rows T stages packed
  M.retainedPreparationSelections A (ZFSet.prod stages (M.preparationWitnessBound nodes T Q))
    (M.varyingPreparationRelation stages packed Q (ZFSet.prod Q Q) nodes T) p
    (refinementDataHistoryLevels stages packed T)

theorem exists_storedPreparedWitnessSelection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows T stages packed nodes row A : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hT : T ∈ M.sets) (hStages : stages ∈ M.sets)
    (hPacked : packed ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (data : RefinementDataHistory stages packed T)
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing rows T stages packed)
    (prepared : StoredPreparedConditionCode M rows T stages packed nodes (ZFSet.pair row A))
    (nameBounds : ∀ alpha (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed →
      fields 14 ⊆ M.groundRelations T (M.refinementHistoryForcing rows T stages packed)) :
    let Q := M.refinementHistoryForcing rows T stages packed
    let L := ZFSet.prod stages (M.preparationWitnessBound nodes T Q)
    ∃ selections ∈ M.sets, ZFSet.IsFunc A L selections ∧
      selections ⊆ M.preparedWitnessSelections rows T stages packed nodes (ZFSet.pair row A) A ∧
      relationImage A L selections ∈ M.sets ∧
      M.groundEmbeddable (relationImage A L selections) ZFSet.omega := by
  let Q := M.refinementHistoryForcing rows T stages packed
  let W := M.groundRelations T Q
  let L := ZFSet.prod stages (M.preparationWitnessBound nodes T Q)
  let R := M.varyingPreparationRelation stages packed Q (ZFSet.prod Q Q) nodes T
  let levels := refinementDataHistoryLevels stages packed T
  have omega := M.omega_mem separation infinite
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hStages hPacked omega
  have hp := M.transitive hQ condition
  have hA := M.pair_right hp
  have candidate := ((M.mem_refinementHistoryForcing rows T stages packed _).1 condition).1
  have smallA := ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate).2.2.2
  have hL := M.prod_mem pairing unions powers separation hStages
    (M.preparationWitnessBound_mem pairing unions powers separation hNodes hT hQ omega)
  have hR := M.varyingPreparationRelation_mem pairing unions powers separation hStages hPacked hQ
    (M.prod_mem pairing unions powers separation hQ hQ) hNodes hT omega
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hPacked hT
  apply M.exists_retainedPreparationSelection pairing unions powers separation infinite choice
    hA hL hR hp hLevels smallA
  intro x hx
  obtain ⟨alpha, ha, fields, stored, terms, nodeCarrier, meet, _environment,
      sourceRow, sourceA, _hSourceA, sourceCondition, sourceSubset, selected,
      k, hk, enumerations, he, q, _hq, cut, family⟩ := prepared row A rfl x hx
  have requestBound : M.storedPreparationRequests sourceA fields ⊆ W := by
    intro z hz
    apply nameBounds alpha fields stored
    rcases ZFSet.mem_union.1 hz with left | right
    · exact (mem_relationImage _ _ _ _).1 left |>.1
    · exact (mem_relationImage _ _ _ _).1 right |>.1
  have witness (r : ZFSet.{u}) (hr : r ∈ Q) :
      ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound nodes T Q :=
    M.preparationWitness_mem_of_local requestBound (fun _ h => h) hr hk he family.1 family.2.1
  have visit : ZFSet.pair (ZFSet.pair alpha (ZFSet.pair sourceRow sourceA))
      (ZFSet.pair (ZFSet.pair row A) (ZFSet.pair k enumerations)) ∈ R := by
    apply (M.pair_mem_varyingPreparationRelation stages packed Q (ZFSet.prod Q Q) nodes T
      alpha (ZFSet.pair sourceRow sourceA) (ZFSet.pair (ZFSet.pair row A) (ZFSet.pair k enumerations))).2
    exact ⟨ha, sourceCondition, witness _ condition, fields, stored, terms, nodeCarrier, meet,
      sourceRow, sourceA, ZFSet.pair row A, k, enumerations, q, rfl, rfl,
      ZFSet.pair_mem_prod.2 ⟨condition, sourceCondition⟩, cut, family⟩
  have inSource := (mem_assignmentOnIndices (fields 0) T sourceA x).1 selected
  have level : ZFSet.pair x alpha ∈ levels := by
    obtain ⟨idx, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments _ _ _).1 inSource.2
    exact data.coverage alpha ha fields stored idx hi u (terms.symm ▸ hu) w (terms.symm ▸ hw)
  let y := ZFSet.pair alpha (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))
  have hy : y ∈ L := ZFSet.pair_mem_prod.2 ⟨ha, witness _ sourceCondition⟩
  refine ⟨y, hy, (M.pair_mem_retainedPreparationSelections A L R (ZFSet.pair row A) levels x y).2 ?_⟩
  exact ⟨hx, hy, alpha, sourceRow, sourceA, ZFSet.pair k enumerations, rfl,
    visit, sourceSubset, inSource.1, level⟩

theorem preparedWitnessSelection_entry
    {rows T stages packed nodes p A x alpha sourceRow sourceA k enumerations : ZFSet.{u}}
    (data : RefinementDataHistory stages packed T)
    (entry : ZFSet.pair x (ZFSet.pair alpha
      (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))) ∈
      M.preparedWitnessSelections rows T stages packed nodes p A) :
    let Q := M.refinementHistoryForcing rows T stages packed
    alpha ∈ stages ∧ ZFSet.pair sourceRow sourceA ∈ Q ∧ sourceA ⊆ A ∧
      k ∈ M.sets ∧ enumerations ∈ M.sets ∧
    ∃ fields : Fin 15 → ZFSet.{u},
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
      fields 6 = T ∧ fields 10 = nodes ∧
      MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
      x ∈ assignmentOnIndices (fields 0) T sourceA ∧
    ∃ q ∈ fields 7,
      ZFSet.pair p q ∈ rowAssignmentCutGraph Q (fields 7)
        (refinementDataHistoryLevels stages packed T) alpha ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
        (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
        ZFSet.omega (M.storedPreparationRequests sourceA fields)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) k enumerations := by
  let Q := M.refinementHistoryForcing rows T stages packed
  obtain ⟨_, _, alpha', row', sourceA', tail, equal, visit, sourceSubset, inSource, level⟩ :=
    (M.pair_mem_retainedPreparationSelections _ _ _ _ _ _ _).1 entry
  obtain ⟨rfl, outputEq⟩ := ZFSet.pair_inj.1 equal
  obtain ⟨sourceEq, rfl⟩ := ZFSet.pair_inj.1 outputEq
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 sourceEq
  obtain ⟨ha, sourceCondition, bounded, fields, stored, terms, nodeCarrier, meet, _raw⟩ :=
    (M.pair_mem_varyingPreparationRelation stages packed Q (ZFSet.prod Q Q) nodes T
      alpha (ZFSet.pair sourceRow sourceA) (ZFSet.pair p (ZFSet.pair k enumerations))).1 visit
  obtain ⟨k', enums', q, value, hk, he, _hp, hq, _below, cut, family⟩ :=
    M.varyingPreparation_visit_certificates stages packed Q (ZFSet.prod Q Q) nodes T alpha
      sourceRow sourceA p (ZFSet.pair k enumerations) _ _ fields data.function.to_isFunc ha
      stored terms nodeCarrier meet visit
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 value
  refine ⟨ha, sourceCondition, sourceSubset, hk, he, fields, stored, terms, nodeCarrier,
    meet, ?_, q, hq, cut, family⟩
  apply (mem_assignmentOnIndices (fields 0) T sourceA x).2
  refine ⟨inSource, ?_⟩
  obtain ⟨I, indexEntry, shape⟩ := (pair_mem_refinementHistoryAssignmentLevels
    data.index_function data.index_literal T x alpha).1 level
  have actual := (refinementDataHistoryField_entry data.function fields stored 0 (fields 0)).2 rfl
  have same : I = fields 0 := data.index_function.unique indexEntry actual
  exact same ▸ shape

end PartitionPilot.Forcing.TransitiveGround

end OAI
