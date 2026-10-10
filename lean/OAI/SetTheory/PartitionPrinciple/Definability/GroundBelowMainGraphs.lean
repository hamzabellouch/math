import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundTwoStageMainDiagram

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hK : K ∈ M.sets)
include pairing unions powers separation hK

namespace GroundMainStage
variable (stage : GroundMainStage M C D rD)

theorem height_below (points : GroundBelow M stage.carrier K) :
    GroundBelow M stage.height K :=
  points.functionGraph pairing unions powers separation stage.carrier_ground stage.height_ground hK
    stage.height_code.function

theorem inverse_below (actors : GroundBelow M stage.actors K) :
    GroundBelow M stage.inverse K :=
  actors.functionGraph pairing unions powers separation stage.actors_ground stage.inverse_ground hK
    stage.group_code.inv_function

theorem order_below (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (points : GroundBelow M stage.carrier K) : GroundBelow M stage.order K :=
  (GroundBelow.product pairing unions powers separation stage.carrier_ground stage.carrier_ground hK
    ordinal strong points points).restrict separation stage.order_ground hK stage.meet.order.relation

theorem meetGraph_below (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (points : GroundBelow M stage.carrier K) : GroundBelow M stage.meetGraph K :=
  (GroundBelow.product pairing unions powers separation stage.carrier_ground stage.carrier_ground hK
    ordinal strong points points).functionGraph pairing unions powers separation
      (M.prod_mem pairing unions powers separation stage.carrier_ground stage.carrier_ground)
      stage.meet_ground hK stage.meet.operation

theorem multiplication_below (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (actors : GroundBelow M stage.actors K) : GroundBelow M stage.multiplication K :=
  (GroundBelow.product pairing unions powers separation stage.actors_ground stage.actors_ground hK
    ordinal strong actors actors).functionGraph pairing unions powers separation
      (M.prod_mem pairing unions powers separation stage.actors_ground stage.actors_ground)
      stage.multiplication_ground hK stage.group_code.mul_function

theorem action_below (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (points : GroundBelow M stage.carrier K) (actors : GroundBelow M stage.actors K) :
    GroundBelow M stage.action K :=
  (GroundBelow.product pairing unions powers separation stage.actors_ground stage.carrier_ground hK
    ordinal strong actors points).functionGraph pairing unions powers separation
      (M.prod_mem pairing unions powers separation stage.actors_ground stage.carrier_ground)
      stage.action_ground hK stage.action_code.function

theorem graphs_below (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (points : GroundBelow M stage.carrier K) (actors : GroundBelow M stage.actors K) :
    GroundBelow M stage.order K ∧ GroundBelow M stage.meetGraph K ∧
      GroundBelow M stage.multiplication K ∧ GroundBelow M stage.inverse K ∧
        GroundBelow M stage.action K ∧ GroundBelow M stage.height K :=
  ⟨stage.order_below pairing unions powers separation hK ordinal strong points,
    stage.meetGraph_below pairing unions powers separation hK ordinal strong points,
    stage.multiplication_below pairing unions powers separation hK ordinal strong actors,
    stage.inverse_below pairing unions powers separation hK actors,
    stage.action_below pairing unions powers separation hK ordinal strong points actors,
    stage.height_below pairing unions powers separation hK points⟩

end GroundMainStage

namespace GroundChronologicalMainStage

theorem birth_below (stage : GroundChronologicalMainStage M C D rD)
    (points : GroundBelow M stage.stage.carrier K) : GroundBelow M stage.birth K :=
  points.functionGraph pairing unions powers separation stage.stage.carrier_ground stage.birth_ground hK
    stage.birth_function

end GroundChronologicalMainStage

namespace GroundMainTransition

theorem graphs_below {source target : GroundMainStage M C D rD}
    (transition : GroundMainTransition source target)
    (points : GroundBelow M source.carrier K) (actors : GroundBelow M source.actors K) :
    GroundBelow M transition.points K ∧ GroundBelow M transition.actors K :=
  ⟨points.functionGraph pairing unions powers separation source.carrier_ground transition.points_ground hK
      transition.point_embedding.injection.function,
    actors.functionGraph pairing unions powers separation source.actors_ground transition.actors_ground hK
      transition.group_embedding.injection.function⟩

end GroundMainTransition
end PartitionPilot.Forcing

end

end OAI
