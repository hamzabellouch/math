import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRecursiveActions
import OAI.SetTheory.PartitionPrinciple.Forcing.OwnerBirthLayerTransport

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

structure GroundMainTransition {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
    (source target : GroundMainStage M C D rD) where
  points : ZFSet.{u}
  actors : ZFSet.{u}
  points_ground : points ∈ M.sets
  actors_ground : actors ∈ M.sets
  point_embedding : MeetEmbeddingCode source.carrier target.carrier source.order target.order
    source.meetGraph target.meetGraph points
  order_iff : ∀ x y x' y', ZFSet.pair x x' ∈ points → ZFSet.pair y y' ∈ points →
    (ZFSet.pair x' y' ∈ target.order ↔ ZFSet.pair x y ∈ source.order)
  group_embedding : GroupEmbeddingCode source.actors target.actors source.multiplication target.multiplication
    source.identity target.identity actors
  equivariant : ∀ g g' x y x' y', ZFSet.pair g g' ∈ actors →
    ZFSet.pair x x' ∈ points → ZFSet.pair y y' ∈ points →
    ZFSet.pair (ZFSet.pair g x) y ∈ source.action → ZFSet.pair (ZFSet.pair g' x') y' ∈ target.action
  bottom : ZFSet.pair source.bottom target.bottom ∈ points
  height : ∀ x y z, ZFSet.pair x y ∈ points →
    (ZFSet.pair y z ∈ target.height ↔ ZFSet.pair x z ∈ source.height)
  agreement : ∀ g h g' h' v v', ZFSet.pair g g' ∈ actors → ZFSet.pair h h' ∈ actors →
    ZFSet.pair v v' ∈ points → ActionAgreementBelow source.carrier source.order source.action g h v →
      ActionAgreementBelow target.carrier target.order target.action g' h' v'

end PartitionPilot.Forcing

end

end OAI
