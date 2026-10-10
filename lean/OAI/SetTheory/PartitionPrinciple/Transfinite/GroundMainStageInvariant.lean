import OAI.SetTheory.PartitionPrinciple.Definability.GroundBelowMainGraphs
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBelowExternalPoints
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainSuccessorProfilePreservation

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable {P G r μ A Labels K : ZFSet.{u}}
variable (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets)
variable (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets) (hK : K ∈ M.sets)
variable (meet : MeetOrderCode P r μ) (conditions : GroundInaccessibleConditions M K)
variable (smallP : GroundBelow M P K) (smallG : GroundBelow M G K) (smallLabels : GroundBelow M Labels K)
include pairing unions powers separation infinite choice hP hG hr hμ hA hLabels hK meet conditions smallP smallG smallLabels

theorem groundInitialExternalLetters_below :
    GroundBelow M (externalChildLetters (M.groundEligibleTasks P G r μ A Labels) P
      (externalRectangles P G r μ A)) K := by
  have hI := M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet
  have smallI := M.groundEligibleTasks_below pairing unions powers separation
    hP hG hr hμ hA hLabels hK meet conditions.1 conditions.2.2.2 smallP smallLabels
  have hRectangles := M.externalRectangles_mem pairing unions powers separation hP hG hr hμ hA
  have rectangles := M.externalRectangles_below pairing unions powers separation hK conditions
    hP hG hr hμ hA smallP smallG
  exact M.externalChildLetters_below pairing unions powers separation infinite choice hK conditions
    hI hP hRectangles smallI smallP rectangles

theorem groundInitialExternalGroup_below {m one : ZFSet.{u}}
    (hm : m ∈ M.sets) (hOne : one ∈ M.sets) :
    GroundBelow M (M.externalGroupCarrier G
      (externalChildLetters (M.groundEligibleTasks P G r μ A Labels) P (externalRectangles P G r μ A)) m one) K := by
  have hI := M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet
  have hRectangles := M.externalRectangles_mem pairing unions powers separation hP hG hr hμ hA
  have hLetters := M.externalChildLetters_mem pairing unions powers separation hI hP hRectangles
  have letters := M.groundInitialExternalLetters_below pairing unions powers separation infinite choice
    hP hG hr hμ hA hLabels hK meet conditions smallP smallG smallLabels
  exact M.externalGroupCarrier_below_of_carriers pairing unions powers separation infinite choice
    hK conditions hG hLetters hm hOne smallG letters

end TransitiveGround

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hLabels : Labels ∈ M.sets) (hK : K ∈ M.sets)
variable (conditions : GroundInaccessibleConditions M K)
variable (points : GroundBelow M source.stage.carrier K)
variable (labels : GroundBelow M Labels K)
local notation "completion" => certificate.compression.born.profiled.heighted.completion
include certificate pairing unions powers separation collection infinite choice hLabels hK conditions points labels

theorem compression_union_below : GroundBelow M ((completion).algebra.union.fields 0) K := by
  exact M.initialCompressionUnion_below certificate.origin (completion).algebra.union
    pairing unions powers separation collection infinite choice
    source.stage.carrier_ground source.stage.actors_ground source.stage.order_ground source.stage.meet_ground
    source.stage.action_ground hLabels certificate.sources_ground certificate.representatives_ground
    certificate.task_action_ground hK source.stage.meet conditions points labels

theorem target_below (actors : GroundBelow M source.stage.actors K) :
    GroundBelow M certificate.target.stage.carrier K ∧
      GroundBelow M certificate.target.stage.actors K := by
  have groupSmall := M.groundInitialExternalGroup_below pairing unions powers separation infinite choice
    source.stage.carrier_ground source.stage.actors_ground source.stage.order_ground source.stage.meet_ground
    source.stage.action_ground hLabels hK source.stage.meet conditions points actors labels
    source.stage.multiplication_ground source.stage.identity_ground
  have unionSmall := certificate.compression_union_below pairing unions powers separation collection infinite
    choice hLabels hK conditions points labels
  constructor
  · rw [certificate.target_fields.1]
    exact certificate.external.inputs.externalBoundedCarrier_below pairing unions powers separation infinite
      source.stage.carrier_ground source.stage.actors_ground hK choice conditions groupSmall unionSmall
  · rw [certificate.target_fields.2.2.2.1]
    exact groupSmall

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hK : K ∈ M.sets)
include certificate pairing unions powers separation hK

theorem transition_graphs_below (points : GroundBelow M source.stage.carrier K)
    (actors : GroundBelow M source.stage.actors K) :
    GroundBelow M certificate.transition.map.points K ∧
      GroundBelow M certificate.transition.map.actors K :=
  certificate.transition.map.graphs_below pairing unions powers separation hK points actors

theorem target_graphs_below
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hLabels : Labels ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (points : GroundBelow M source.stage.carrier K) (actors : GroundBelow M source.stage.actors K)
    (labels : GroundBelow M Labels K) :
    GroundBelow M certificate.target.stage.order K ∧
      GroundBelow M certificate.target.stage.meetGraph K ∧
        GroundBelow M certificate.target.stage.multiplication K ∧
          GroundBelow M certificate.target.stage.inverse K ∧
            GroundBelow M certificate.target.stage.action K ∧
              GroundBelow M certificate.target.stage.height K ∧
                GroundBelow M certificate.target.birth K := by
  obtain ⟨targetPoints, targetActors⟩ := certificate.target_below pairing unions powers separation
    collection infinite choice hLabels hK conditions points labels actors
  obtain ⟨order, meet, multiplication, inverse, action, height⟩ :=
    certificate.target.stage.graphs_below pairing unions powers separation hK
      conditions.1 conditions.2.2.2 targetPoints targetActors
  exact ⟨order, meet, multiplication, inverse, action, height,
    certificate.target.birth_below pairing unions powers separation hK targetPoints⟩

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}

theorem standard_bounds (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hLabels : Labels ∈ M.sets) (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (pointSize : GroundBelow M source.stage.carrier K)
    (actorSize : GroundBelow M source.stage.actors K) (labelSize : GroundBelow M Labels K)
    (pointRank : ZFSet.rank source.stage.carrier < ZFSet.rank K)
    (actorRank : ZFSet.rank source.stage.actors < ZFSet.rank K)
    (labelRank : ZFSet.rank Labels < ZFSet.rank K) (sourceTime : source.cutoff ∈ K)
    (columnRank : ZFSet.rank C < ZFSet.rank K) (coordinateRank : ZFSet.rank D < ZFSet.rank K) :
    GroundBelow M certificate.target.stage.carrier K ∧
      GroundBelow M certificate.target.stage.actors K ∧
        ZFSet.rank certificate.target.stage.carrier < ZFSet.rank K ∧
          ZFSet.rank certificate.target.stage.actors < ZFSet.rank K ∧
            ZFSet.rank certificate.target.stage.code < ZFSet.rank K ∧
              certificate.target.cutoff ∈ K ∧
                ZFSet.rank certificate.target.birth < ZFSet.rank K ∧
                  GroundBelow M certificate.transition.map.points K ∧
                    GroundBelow M certificate.transition.map.actors K ∧
                      ZFSet.rank certificate.transition.map.code < ZFSet.rank K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  have sizes := certificate.target_below pairing unions powers separation collection infinite choice
    hLabels hK conditions pointSize labelSize actorSize
  have ranks := certificate.target_rank_lt pairing unions powers separation collection infinite
    hK conditions pointRank labelRank actorRank
  have maps := certificate.transition_graphs_below pairing unions powers separation hK pointSize actorSize
  exact ⟨sizes.1, sizes.2, ranks.1, ranks.2,
    certificate.target_code_rank_lt pairing unions powers separation collection infinite
      hK conditions pointRank labelRank actorRank columnRank coordinateRank,
    certificate.target_cutoff_mem pairing unions powers separation infinite hK conditions sourceTime,
    certificate.target_birth_rank_lt pairing unions powers separation infinite hK conditions sourceTime ranks.1,
    maps.1, maps.2,
    certificate.transition_code_rank_lt pairing unions powers separation collection infinite
      hK conditions pointRank labelRank actorRank⟩

end GroundInitialMainSuccessorData

open SetFormula SetRealization
universe u

namespace GroundChronologicalMainStage
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}

structure Invariant (source : GroundChronologicalMainStage M C D rD) (K Labels : ZFSet.{u}) : Prop where
  points_small : GroundBelow M source.stage.carrier K
  actors_small : GroundBelow M source.stage.actors K
  labels_small : GroundBelow M Labels K
  points_rank : ZFSet.rank source.stage.carrier < ZFSet.rank K
  actors_rank : ZFSet.rank source.stage.actors < ZFSet.rank K
  labels_rank : ZFSet.rank Labels < ZFSet.rank K
  cutoff_mem : source.cutoff ∈ K
  columns_rank : ZFSet.rank C < ZFSet.rank K
  coordinates_rank : ZFSet.rank D < ZFSet.rank K

namespace Invariant
variable {source : GroundChronologicalMainStage M C D rD} {K Labels : ZFSet.{u}}
variable (invariant : source.Invariant K Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
include invariant pairing unions powers separation infinite hK conditions

theorem code_rank_lt : ZFSet.rank source.stage.code < ZFSet.rank K :=
  source.stage.code_rank_lt_inaccessible pairing unions powers separation infinite hK conditions
    invariant.points_rank invariant.actors_rank invariant.columns_rank invariant.coordinates_rank

theorem birth_rank_lt : ZFSet.rank source.birth < ZFSet.rank K :=
  rank_functionGraph_lt (conditions.rank_isLimit pairing unions powers separation infinite hK)
    source.birth_function invariant.points_rank
    (ZFSet.rank_lt_of_mem (conditions.successor_mem pairing unions powers separation infinite
      hK invariant.cutoff_mem))

end Invariant

end GroundChronologicalMainStage

namespace GroundInitialMainSuccessorData
variable {M : TransitiveGround.{u}} {C D rD K Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}

theorem target_invariant (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hLabels : Labels ∈ M.sets) (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (invariant : source.Invariant K Labels) : certificate.target.Invariant K Labels := by
  have bounds := certificate.standard_bounds pairing unions powers separation collection infinite choice
    hLabels hK standard invariant.points_small invariant.actors_small invariant.labels_small
    invariant.points_rank invariant.actors_rank invariant.labels_rank invariant.cutoff_mem
    invariant.columns_rank invariant.coordinates_rank
  exact ⟨bounds.1, bounds.2.1, invariant.labels_small, bounds.2.2.1, bounds.2.2.2.1,
    invariant.labels_rank, bounds.2.2.2.2.2.1, invariant.columns_rank, invariant.coordinates_rank⟩

end GroundInitialMainSuccessorData

end PartitionPilot.Forcing

end OAI
