import OAI.SetTheory.PartitionPrinciple.Geometry.GroundInitialCompressionOrigin

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace GroundInaccessibleConditions
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}

theorem exists_rank_limit_above (conditions : GroundInaccessibleConditions M K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) {o : Ordinal.{u}} (bound : o < ZFSet.rank K) :
    ∃ L ∈ K, Order.IsSuccLimit (ZFSet.rank L) ∧ o < ZFSet.rank L := by
  have hBase : ordinalCode o ∈ K := by
    rw [ordinalSetProperty_eq_code_rank K conditions.1]
    exact (mem_ordinalCode_iff o (ZFSet.rank K)).2 bound
  obtain ⟨_, _, L, _, _, _, hL, limit, above⟩ := M.exists_groundCompressionStamps_below
    pairing unions powers separation collection infinite hK conditions hBase
  refine ⟨L, hL, limit, ?_⟩
  simpa only [rank_ordinalCode] using ZFSet.rank_lt_of_mem above

end GroundInaccessibleConditions

namespace GroundCompressionUnionData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T : ZFSet.{u}}
variable (data : GroundCompressionUnionData M initial I Sources Reps G m one T)

theorem carrier_rank_lt_inaccessible
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K P r μ : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (constant : RecursiveTemplateConstancy P r μ initial)
    (points : ZFSet.rank initial.D < ZFSet.rank K) (indices : ZFSet.rank initial.J < ZFSet.rank K)
    (templates : ZFSet.rank P < ZFSet.rank K) (tasks : ZFSet.rank I < ZFSet.rank K) :
    ZFSet.rank (data.fields 0) < ZFSet.rank K := by
  let b := max (ZFSet.rank initial.D) (max (ZFSet.rank initial.J) (max (ZFSet.rank P) (ZFSet.rank I)))
  have bound : b < ZFSet.rank K := max_lt points (max_lt indices (max_lt templates tasks))
  obtain ⟨L, hL, limit, above⟩ := conditions.exists_rank_limit_above
    pairing unions powers separation collection infinite hK bound
  have pointBound : ZFSet.rank initial.D ≤ b := le_max_left _ _
  have indexBound : ZFSet.rank initial.J ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have templateBound : ZFSet.rank P ≤ b :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have taskBound : ZFSet.rank I ≤ b :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  exact (data.carrier_rank_le constant limit (pointBound.trans_lt above) (indexBound.trans_lt above)
    (templateBound.trans_lt above) (taskBound.trans_lt above)).trans_lt (ZFSet.rank_lt_of_mem hL)

end GroundCompressionUnionData

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem initialCompressionUnion_rank_lt
    {P G r μ A Labels Sources Reps m one T K : ZFSet.{u}}
    (data : GroundCompressionUnionData M (M.initialCompressionData P G r μ A Labels)
      (M.groundEligibleTasks P G r μ A Labels) Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (points : ZFSet.rank P < ZFSet.rank K) (labels : ZFSet.rank Labels < ZFSet.rank K) :
    ZFSet.rank (data.fields 0) < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have tasks := M.groundEligibleTasks_rank_lt limit G r μ A points labels
  exact data.carrier_rank_lt_inaccessible pairing unions powers separation collection infinite hK conditions
    (M.initialCompressionData_template_constancy P G r μ A Labels) points tasks points tasks

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
