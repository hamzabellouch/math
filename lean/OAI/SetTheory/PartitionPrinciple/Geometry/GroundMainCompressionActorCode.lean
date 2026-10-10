import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainSuccessorCompressionActors

namespace OAI

section

namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

noncomputable def compressionActorValues : Fin 13 → ZFSet.{u} :=
  Fin.cases (source.stage.compressionTasks Labels) (Fin.cases (source.stage.carrier) (Fin.cases (source.stage.actors) (Fin.cases (certificate.target.stage.carrier) (Fin.cases (certificate.target.stage.actors) (Fin.cases (certificate.target.stage.order) (Fin.cases (certificate.target.stage.action) (Fin.cases (certificate.transition.map.points) (Fin.cases (certificate.transition.map.actors) (Fin.cases (source.stage.compressionSources Labels) (Fin.cases (certificate.Reps) (Fin.cases (source.stage.top) (fun _ => certificate.compressionCapImages))))))))))))

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
include pairing unions powers separation infinite

theorem compressionActorValues_ground : ∀ j, certificate.compressionActorValues j ∈ M.sets :=
  Fin.cases (certificate.indices_ground) (Fin.cases (source.stage.carrier_ground) (Fin.cases (source.stage.actors_ground) (Fin.cases (certificate.target.stage.carrier_ground) (Fin.cases (certificate.target.stage.actors_ground) (Fin.cases (certificate.target.stage.order_ground) (Fin.cases (certificate.target.stage.action_ground) (Fin.cases (certificate.transition.map.points_ground) (Fin.cases (certificate.transition.map.actors_ground) (Fin.cases (certificate.sources_ground) (Fin.cases (certificate.representatives_ground) (Fin.cases (source.stage.top_ground) (fun _ => certificate.compressionCapImages_ground pairing unions powers separation infinite))))))))))))

theorem compressionActorFulfillment :
    CompressionActorFulfillmentCode (source.stage.compressionTasks Labels)
      source.stage.carrier source.stage.actors certificate.target.stage.carrier
      certificate.target.stage.actors certificate.target.stage.order certificate.target.stage.action
      certificate.transition.map.points certificate.transition.map.actors
      (source.stage.compressionSources Labels) certificate.Reps source.stage.top
      certificate.compressionCapImages := by
  intro i hi
  obtain ⟨k, hk, agreement, top⟩ :=
    certificate.exists_compression_actor pairing unions powers separation infinite hi
  refine ⟨k, hk, ?_, ?_⟩
  · intro s _ g _ g' _ s' _ hs hg actor point
    exact agreement s g g' s' hs hg actor point
  · intro top' _ v _ image
    exact top top' v image

theorem realize_compressionActorFulfillment :
    Realize M.sets
      (BoundedFormula.compressionActorFulfillmentFormula 0 1 2 3 4 5 6 7 8 9 10 11 12).toFormula
      certificate.compressionActorValues :=
  (BoundedFormula.realize_compressionActorFulfillmentFormula M 0 1 2 3 4 5 6 7 8 9 10 11 12
    certificate.compressionActorValues
    (certificate.compressionActorValues_ground pairing unions powers separation infinite)).2
    (certificate.compressionActorFulfillment pairing unions powers separation infinite)

end PartitionPilot.Forcing.GroundInitialMainSuccessorData

end

end OAI
