import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStructuralForcingHistoryConstruction

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem structuralForcingTrace_birthLevelEnumerations
    (rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {stages history : ZFSet.{u}} (hRows : rows ∈ M.sets) (hG : G ∈ M.sets)
    (hNodes : nodes ∈ M.sets) (hOrder : nodeOrder ∈ M.sets) (hBasis : basis ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction
        basis T T2 level prior) stages history) :
    let packed := M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history
    let Q := M.refinementHistoryForcing rows T stages packed
    let levels := refinementDataHistoryLevels stages packed T
    Q ∈ M.sets ∧ M.groundRelations ZFSet.omega stages ∈ M.sets ∧
      M.birthLevelEnumerationRelation Q stages levels ∈ M.sets ∧
      ∃ selector ∈ M.sets, ZFSet.IsFunc Q (M.groundRelations ZFSet.omega stages) selector ∧
        selector ⊆ M.birthLevelEnumerationRelation Q stages levels ∧
        ∀ row A e, ZFSet.pair (ZFSet.pair row A) e ∈ selector →
          BirthLevelEnumerationCode ZFSet.omega stages A levels e := by
  have packed := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![G, nodes, nodeOrder, basis, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hNodes (Fin.cases hOrder (Fin.cases hBasis
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun i => Fin.elim0 i)))))))))
  have run := M.structuralForcingTrace_recursiveOrder rows rowOrder rowTop rowAction
    G nodes nodeOrder nodeAction basis T T2 ordinal trace
  have omega := M.omega_mem separation infinite
  exact ⟨M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hs packed omega,
    M.groundRelations_mem pairing unions powers separation omega hs,
    M.exists_refinementBirthLevelEnumerations pairing unions powers separation infinite choice
      hRows hT hs packed run.carriers.data⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
