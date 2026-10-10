import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStructuralHistoryTestUnions

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem refinementHistoryInitialIndexImage {K F : ZFSet.{u}}
    (function : FunctionGraphOn K F)
    (literal : ∀ beta I, ZFSet.pair beta I ∈ F → RefinementIndexLevelCode I beta)
    (alpha : ZFSet.{u}) :
    relationImage alpha (refinementHistoryIndices K F)
      (relationConverse (refinementHistoryIndices K F) K (refinementHistoryLevels K F)) =
        refinementHistoryIndices alpha F := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨_, beta, hb, entry⟩ := (mem_relationImage _ _ _ _).1 hx
    have level := ((pair_mem_relationConverse _ _ _ x beta).1 entry).2.2
    obtain ⟨I, stored, member⟩ := (pair_mem_refinementHistoryLevels function literal x beta).1 level
    exact (mem_refinementHistoryIndices _ _ _).2 ⟨beta, hb, I, stored, member⟩
  · intro hx
    obtain ⟨beta, hb, I, stored, member⟩ := (mem_refinementHistoryIndices _ _ _).1 hx
    have hBeta := function.pair_source stored
    have full := (mem_refinementHistoryIndices K F x).2 ⟨beta, hBeta, I, stored, member⟩
    exact (mem_relationImage _ _ _ _).2 ⟨full, beta, hb,
      (pair_mem_relationConverse _ _ _ x beta).2 ⟨full, hBeta,
        (pair_mem_refinementHistoryLevels function literal x beta).2 ⟨I, stored, member⟩⟩⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem refinementDataHistoryIndices_embeds
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (collection : CollectionSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K history T : ZFSet.{u}} (hK : K ∈ M.sets) (hHistory : history ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K) (valid : RefinementDataHistory K history T)
    (prefixes : ∀ alpha ∈ K,
      GroundBelow M (refinementDataHistoryIndices alpha (graphRestriction alpha history)) K) :
    M.groundEmbeddable (refinementDataHistoryIndices K history) K := by
  let F := refinementDataHistoryField K history 0
  let I := refinementHistoryIndices K F
  let levels := refinementHistoryLevels K F
  let e := relationConverse I K levels
  have hF : F ∈ M.sets := M.refinementDataHistoryField_mem pairing unions powers separation hK hHistory 0
  have hI : I ∈ M.sets := M.refinementHistoryIndices_mem unions separation hK hF
  have hLevels : levels ∈ M.sets := M.refinementHistoryLevels_mem pairing unions powers separation hK hF
  have he : e ∈ M.sets := M.relationConverse_mem pairing unions powers separation hI hK hLevels
  have cardinal : GroundCardinal M K := conditions.internal_cardinal pairing unions powers separation hK
  apply M.ordinalRelation_embeds pairing unions powers separation collection choice (e := e) hI hK he cardinal
  · intro x hx
    have function := refinementHistoryLevels_function (alpha := K) valid.index_literal
    obtain ⟨beta, entry, _⟩ := function.2 x hx
    have hBeta := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    exact ⟨beta, hBeta, (pair_mem_relationConverse I K levels x beta).2 ⟨hx, hBeta, entry⟩⟩
  · intro beta hBeta
    have successor := conditions.successor_mem pairing unions powers separation infinite hK hBeta
    have subset := conditions.1.1 (insert beta beta) successor
    have initial := prefixes (insert beta beta) successor
    change GroundBelow M (refinementHistoryIndices (insert beta beta)
      (refinementDataHistoryField (insert beta beta) (graphRestriction (insert beta beta) history) 0)) K at initial
    rw [refinementDataHistoryIndices_prefix subset (fun _ h => h)] at initial
    change GroundBelow M (relationImage (insert beta beta) (refinementHistoryIndices K F)
      (relationConverse (refinementHistoryIndices K F) K (refinementHistoryLevels K F))) K
    rw [refinementHistoryInitialIndexImage valid.index_function valid.index_literal]
    exact initial

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
