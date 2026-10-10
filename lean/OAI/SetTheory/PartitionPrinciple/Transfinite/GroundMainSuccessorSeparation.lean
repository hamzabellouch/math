import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainSuccessorProfilePreservation

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P ∈ M.sets)
include data group action pairing unions powers separation infinite hG hP
local notation "letters" => externalChildLetters I P (externalRectangles P G r μ A)
local notation "Q" => completion.externalPointCarrier P r μ A
local notation "U" => completion.algebra.union.fields 0
local notation "e" => completion.externalOriginalEmbedding P r μ A

theorem externalBounded_separation_actor {W k : ZFSet.{u}} (hW : W ∈ P)
    (generator : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 1) W) (natSetCode 0)) k ∈
      M.externalChildGenerators G letters m one) :
    SeparationActorCode P r (completion.externalBoundedCarrier P r μ A)
      (completion.externalBoundedOrder P r μ A) (completion.externalBoundedMeet P r μ A)
      (completion.externalBoundedAction P r μ A) e W k := by
  let := group.toGroup
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP
  intro w _ imageW
  have hw : w ∈ Q := data.externalOriginal_image_mem group action pairing unions powers separation infinite hG hP imageW
  have copiedW := ((completion.externalOriginalEmbedding_entry_iff P r μ A W w).1 imageW).1
  have eqW := (data.external_identity_copy_value group action pairing unions powers separation infinite hG
    (SetMembers.ofMem W (data.original.subset hW)) w).1 (by simpa only [SetMembers.raw_ofMem] using copiedW)
  constructor
  · intro z _ lower
    have hz : z ∈ Q := fixedTopOrder_no_new_below geometry.meet.order hw lower
    have oldLower := (fixedTopOrder_old_iff hw).1 lower
    rw [eqW] at oldLower
    exact (fixedTopAction_old_iff hz).2 (data.separation_generator_fixes group action
      pairing unions powers separation infinite hG (SetMembers.ofMem W hW) k
      (by simpa only [SetMembers.raw_ofMem] using generator) z hz
      (by simpa only [SetMembers.raw_ofMem] using oldLower))
  · intro x hx y hy x' _ y' _ z _ wx wy imageX imageY acted
    have hx' : x' ∈ Q := data.externalOriginal_image_mem group action pairing unions powers separation infinite hG hP imageX
    have hy' : y' ∈ Q := data.externalOriginal_image_mem group action pairing unions powers separation infinite hG hP imageY
    have oldAct := (fixedTopAction_old_iff hx').1 acted
    have hz : z ∈ Q := (ZFSet.pair_mem_prod.1 (geometry.action.function.1 oldAct)).2
    have eqX := (data.external_identity_copy_value group action pairing unions powers separation infinite hG
      (SetMembers.ofMem x (data.original.subset hx)) x').1
      (by simpa only [SetMembers.raw_ofMem] using
        ((completion.externalOriginalEmbedding_entry_iff P r μ A x x').1 imageX).1)
    have eqY := (data.external_identity_copy_value group action pairing unions powers separation infinite hG
      (SetMembers.ofMem y (data.original.subset hy)) y').1
      (by simpa only [SetMembers.raw_ofMem] using
        ((completion.externalOriginalEmbedding_entry_iff P r μ A y y').1 imageY).1)
    have wx' := (data.original.order W hW x hx).2 wx
    have wy' := (data.original.order W hW y hy).2 wy
    rw [eqX] at oldAct
    have meetEntry := data.separation_generator_meet group action pairing unions powers separation infinite hG
      (SetMembers.ofMem W hW) (SetMembers.ofMem x (data.original.subset hx))
      (SetMembers.ofMem y (data.original.subset hy))
      (by simpa only [SetMembers.raw_ofMem] using wx')
      (by simpa only [SetMembers.raw_ofMem] using wy') k
      (by simpa only [SetMembers.raw_ofMem] using generator) z oldAct
    apply (fixedTopMeet_old_iff geometry.meet hz hy').2
    simpa only [SetMembers.raw_ofMem, eqY, eqW] using meetEntry

theorem externalBounded_separation_fulfillment :
    SeparationFulfillmentCode P r (completion.externalBoundedCarrier P r μ A)
      (completion.externalBoundedOrder P r μ A) (completion.externalBoundedMeet P r μ A)
      (M.externalGroupCarrier G letters m one) (completion.externalBoundedAction P r μ A) e := by
  intro W hW
  have letter := (separation_child_iff I P (externalRectangles P G r μ A) W (natSetCode 0)).2 ⟨hW, rfl⟩
  obtain ⟨k, entry, _⟩ := data.generators_injection.function.2 _ letter
  have hk := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 entry)).2
  exact ⟨k, hk, data.externalBounded_separation_actor group action
    pairing unions powers separation infinite hG hP hW entry⟩

end GroundExternalGeometryInputs

namespace GroundInitialMainSuccessorData
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

theorem separation_fulfillment
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) :
    SeparationFulfillmentCode source.stage.carrier source.stage.order certificate.target.stage.carrier
      certificate.target.stage.order certificate.target.stage.meetGraph certificate.target.stage.actors
      certificate.target.stage.action certificate.transition.map.points := by
  obtain ⟨points, order, meet, actors, _, _, _, action, _⟩ := certificate.target_fields
  rw [points, order, meet, actors, action, certificate.point_graph]
  exact certificate.external.inputs.externalBounded_separation_fulfillment
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground

end GroundInitialMainSuccessorData
end PartitionPilot.Forcing

end

end OAI
