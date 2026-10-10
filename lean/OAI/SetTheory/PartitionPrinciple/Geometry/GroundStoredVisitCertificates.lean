import OAI.SetTheory.PartitionPrinciple.Definability.GroundVaryingPreparationRelations

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem varyingPreparationRelation_of_stored
    (stages packed Q upperOrder nodes T alpha p y meet : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u}) (hAlpha : alpha ∈ stages)
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed)
    (terms : fields 6 = T) (nodeCarrier : fields 10 = nodes)
    (meetCode : MeetOrderCode (fields 10) (fields 11) meet)
    (entry : ZFSet.pair p y ∈ M.storedPreparationRelation Q upperOrder nodes T
      (refinementDataHistoryLevels stages packed T) alpha meet fields) :
    ZFSet.pair (ZFSet.pair alpha p) y ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T := by
  obtain ⟨hp, hy, code⟩ := (M.pair_mem_storedPreparationRelation Q upperOrder nodes T
    (refinementDataHistoryLevels stages packed T) alpha meet fields p y).1 entry
  have equal := meetCode.eq_canonicalMeetGraph
  exact (M.pair_mem_varyingPreparationRelation stages packed Q upperOrder nodes T alpha p y).2
    ⟨hAlpha, hp, hy, fields, stored, terms, nodeCarrier, equal ▸ meetCode, equal ▸ code⟩

theorem varyingPreparationRelation_fiber_iff
    (stages packed Q upperOrder nodes T alpha p y meet dataBound : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u})
    (function : ZFSet.IsFunc stages dataBound packed) (hAlpha : alpha ∈ stages)
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed)
    (terms : fields 6 = T) (nodeCarrier : fields 10 = nodes)
    (meetCode : MeetOrderCode (fields 10) (fields 11) meet) :
    ZFSet.pair (ZFSet.pair alpha p) y ∈
        M.varyingPreparationRelation stages packed Q upperOrder nodes T ↔
      ZFSet.pair p y ∈ M.storedPreparationRelation Q upperOrder nodes T
        (refinementDataHistoryLevels stages packed T) alpha meet fields := by
  constructor
  · intro entry
    obtain ⟨_, hp, hy, other, otherStored, _terms, _nodes, _meet, code⟩ :=
      (M.pair_mem_varyingPreparationRelation stages packed Q upperOrder nodes T alpha p y).1 entry
    obtain ⟨_, _, unique⟩ := function.2 alpha hAlpha
    have same : other = fields := refinementFormulaDataCode_injective
      ((unique _ otherStored).trans (unique _ stored).symm)
    subst other
    exact (M.pair_mem_storedPreparationRelation Q upperOrder nodes T
      (refinementDataHistoryLevels stages packed T) alpha meet fields p y).2
      ⟨hp, hy, meetCode.eq_canonicalMeetGraph.symm ▸ code⟩
  · exact M.varyingPreparationRelation_of_stored stages packed Q upperOrder nodes T alpha p y meet
      fields hAlpha stored terms nodeCarrier meetCode





theorem varyingPreparation_visit_certificates
    (stages packed Q upperOrder nodes T alpha row A r payload meet dataBound : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u})
    (function : ZFSet.IsFunc stages dataBound packed) (hAlpha : alpha ∈ stages)
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed)
    (terms : fields 6 = T) (nodeCarrier : fields 10 = nodes)
    (meetCode : MeetOrderCode (fields 10) (fields 11) meet)
    (entry : ZFSet.pair (ZFSet.pair alpha (ZFSet.pair row A)) (ZFSet.pair r payload) ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T) :
    ∃ k enumerations q, payload = ZFSet.pair k enumerations ∧
      k ∈ M.sets ∧ enumerations ∈ M.sets ∧ r ∈ Q ∧ q ∈ fields 7 ∧
      ZFSet.pair r (ZFSet.pair row A) ∈ upperOrder ∧
      ZFSet.pair r q ∈ rowAssignmentCutGraph Q (fields 7)
        (refinementDataHistoryLevels stages packed T) alpha ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
        meet (fields 14) (fields 13) (fields 9) ZFSet.omega
        (M.storedPreparationRequests A fields)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) k enumerations := by
  have fixed := (M.varyingPreparationRelation_fiber_iff stages packed Q upperOrder nodes T
    alpha (ZFSet.pair row A) (ZFSet.pair r payload) meet dataBound fields function hAlpha
    stored terms nodeCarrier meetCode).1 entry
  obtain ⟨_, bounded, oldRow, oldA, output, k, enumerations, q, input, value, below, cut, family⟩ :=
    (M.pair_mem_storedPreparationRelation Q upperOrder nodes T
      (refinementDataHistoryLevels stages packed T) alpha meet fields
      (ZFSet.pair row A) (ZFSet.pair r payload)).1 fixed
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 input
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 value
  obtain ⟨hr, hk, he⟩ := (M.mem_preparationWitnessBound nodes T Q r k enumerations).1 bounded
  have hq := (ZFSet.pair_mem_prod.1
    ((mem_rowAssignmentCutGraph _ _ _ _ _).1 cut).1).2
  exact ⟨k, enumerations, q, rfl,
    ((M.mem_groundRelations _ _ k).1 hk).1,
    ((M.mem_groundRelations _ _ enumerations).1 he).1, hr, hq, below, cut, family⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
