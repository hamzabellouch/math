import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainTransitionLaws

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}

namespace GroundMainStage
variable (stage : GroundMainStage M C D rD) {o : Ordinal.{u}}

theorem field_rank_lt (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank stage.carrier < o) (actors : ZFSet.rank stage.actors < o)
    (columns : ZFSet.rank C < o) (coordinates : ZFSet.rank D < o) :
    ∀ j, ZFSet.rank (stage.field j) < o := by
  have pp := rank_product_lt limit points points
  have gg := rank_product_lt limit actors actors
  have order := (ZFSet.rank_mono stage.meet.order.relation).trans_lt pp
  have meet := rank_functionGraph_lt limit stage.meet.operation pp points
  have mul := rank_functionGraph_lt limit stage.group_code.mul_function gg actors
  have inv := rank_functionGraph_lt limit stage.group_code.inv_function actors actors
  have one := (ZFSet.rank_lt_of_mem stage.group_code.identity_mem).trans actors
  have action := rank_functionGraph_lt limit stage.action_code.function
    (rank_product_lt limit actors points) points
  have bottom := (ZFSet.rank_lt_of_mem stage.bottom_mem).trans points
  have top := (ZFSet.rank_lt_of_mem stage.top_mem).trans points
  have height := rank_functionGraph_lt limit stage.height_code.function points
    (rank_product_lt limit columns coordinates)
  exact Fin.cases points (Fin.cases order (Fin.cases meet (Fin.cases actors (Fin.cases mul
    (Fin.cases inv (Fin.cases one (Fin.cases action (Fin.cases bottom (Fin.cases top
      (Fin.cases height (fun i => Fin.elim0 i)))))))))))

theorem code_rank_lt (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank stage.carrier < o) (actors : ZFSet.rank stage.actors < o)
    (columns : ZFSet.rank C < o) (coordinates : ZFSet.rank D < o) :
    ZFSet.rank stage.code < o :=
  rank_nonemptyTupleCode_lt limit 10 stage.field (stage.field_rank_lt limit points actors columns coordinates)

theorem code_rank_lt_inaccessible
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (points : ZFSet.rank stage.carrier < ZFSet.rank K) (actors : ZFSet.rank stage.actors < ZFSet.rank K)
    (columns : ZFSet.rank C < ZFSet.rank K) (coordinates : ZFSet.rank D < ZFSet.rank K) :
    ZFSet.rank stage.code < ZFSet.rank K :=
  stage.code_rank_lt (conditions.rank_isLimit pairing unions powers separation infinite hK)
    points actors columns coordinates

end GroundMainStage

namespace GroundMainTransition
variable {source target : GroundMainStage M C D rD}
variable (transition : GroundMainTransition source target) {o : Ordinal.{u}}

theorem graphs_rank_lt (limit : Order.IsSuccLimit o)
    (sourcePoints : ZFSet.rank source.carrier < o) (targetPoints : ZFSet.rank target.carrier < o)
    (sourceActors : ZFSet.rank source.actors < o) (targetActors : ZFSet.rank target.actors < o) :
    ZFSet.rank transition.points < o ∧ ZFSet.rank transition.actors < o :=
  ⟨rank_functionGraph_lt limit transition.point_embedding.injection.function sourcePoints targetPoints,
    rank_functionGraph_lt limit transition.group_embedding.injection.function sourceActors targetActors⟩

theorem code_rank_lt (limit : Order.IsSuccLimit o)
    (sourcePoints : ZFSet.rank source.carrier < o) (targetPoints : ZFSet.rank target.carrier < o)
    (sourceActors : ZFSet.rank source.actors < o) (targetActors : ZFSet.rank target.actors < o) :
    ZFSet.rank transition.code < o := by
  have bounds := transition.graphs_rank_lt limit sourcePoints targetPoints sourceActors targetActors
  exact rank_orderedPair_lt limit bounds.1 bounds.2

theorem code_rank_lt_inaccessible
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (sourcePoints : ZFSet.rank source.carrier < ZFSet.rank K)
    (targetPoints : ZFSet.rank target.carrier < ZFSet.rank K)
    (sourceActors : ZFSet.rank source.actors < ZFSet.rank K)
    (targetActors : ZFSet.rank target.actors < ZFSet.rank K) :
    ZFSet.rank transition.code < ZFSet.rank K :=
  transition.code_rank_lt (conditions.rank_isLimit pairing unions powers separation infinite hK)
    sourcePoints targetPoints sourceActors targetActors

end GroundMainTransition
end PartitionPilot.Forcing

end

end OAI
