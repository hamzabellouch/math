import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainTaskCapFulfillment

namespace OAI

section

namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
local notation "tasks" => source.stage.compressionTasks Labels
local notation "letters" => externalChildLetters tasks source.stage.carrier
  (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)
local notation "generators" => M.externalChildGenerators source.stage.actors letters source.stage.multiplication source.stage.identity
include certificate pairing unions powers separation infinite

theorem compression_generator_full_agreement {i a g k g' a' : ZFSet.{u}} (hi : i ∈ tasks)
    (sourceEntry : ZFSet.pair i a ∈ source.stage.compressionSources Labels)
    (representative : ZFSet.pair i g ∈ certificate.Reps)
    (generator : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) i) (natSetCode 0)) k ∈ generators)
    (actor : ZFSet.pair g g' ∈ certificate.transition.map.actors)
    (image : ZFSet.pair a a' ∈ certificate.transition.map.points) :
    ActionAgreementBelow certificate.target.stage.carrier certificate.target.stage.order
      certificate.target.stage.action k g' a' := by
  rw [certificate.point_graph] at image
  rw [certificate.actor_graph] at actor
  rw [certificate.target_fields.1, certificate.target_fields.2.1,
    certificate.target_fields.2.2.2.2.2.2.2.1]
  exact certificate.external.inputs.bounded_compression_generator_agreement source.stage.group_code
    source.stage.action_code pairing unions powers separation infinite source.stage.actors_ground source.stage.carrier_ground
    (SetMembers.ofMem i hi) (by simpa only [SetMembers.raw_ofMem] using sourceEntry)
    (by simpa only [SetMembers.raw_ofMem] using representative)
    (by simpa only [SetMembers.raw_ofMem] using generator) actor image

theorem compression_generator_cap_iff {i k τ' v : ZFSet.{u}} (hi : i ∈ tasks)
    (generator : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) i) (natSetCode 0)) k ∈ generators)
    (imageTop : ZFSet.pair source.stage.top τ' ∈ certificate.transition.map.points) :
    ZFSet.pair (ZFSet.pair k τ') v ∈ certificate.target.stage.action ↔
      ZFSet.pair i v ∈ certificate.compressionCapImages := by
  rw [certificate.point_graph] at imageTop
  rw [certificate.target_fields.2.2.2.2.2.2.2.1]
  simpa only [SetMembers.raw_ofMem, compressionCapImages] using certificate.external.inputs.bounded_compression_generator_top_iff
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground (SetMembers.ofMem i hi)
    (by simpa only [SetMembers.raw_ofMem] using generator) imageTop

theorem exists_compression_actor {i : ZFSet.{u}} (hi : i ∈ tasks) :
    ∃ k ∈ certificate.target.stage.actors,
      (∀ a g g' a', ZFSet.pair i a ∈ source.stage.compressionSources Labels →
        ZFSet.pair i g ∈ certificate.Reps → ZFSet.pair g g' ∈ certificate.transition.map.actors →
        ZFSet.pair a a' ∈ certificate.transition.map.points →
        ActionAgreementBelow certificate.target.stage.carrier certificate.target.stage.order
          certificate.target.stage.action k g' a') ∧
      ∀ τ' v, ZFSet.pair source.stage.top τ' ∈ certificate.transition.map.points →
        (ZFSet.pair (ZFSet.pair k τ') v ∈ certificate.target.stage.action ↔
          ZFSet.pair i v ∈ certificate.compressionCapImages) := by
  have letter := (compression_child_iff tasks source.stage.carrier
    (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)
    i (natSetCode 0)).2 ⟨hi, rfl⟩
  obtain ⟨k, generator, _⟩ := certificate.external.inputs.generators_injection.function.2 _ letter
  have hk := (ZFSet.pair_mem_prod.1 (certificate.external.inputs.generators_injection.function.1 generator)).2
  refine ⟨k, certificate.target_fields.2.2.2.1.symm ▸ hk, ?_, ?_⟩
  · intro a g g' a' sourceEntry representative actor image
    exact certificate.compression_generator_full_agreement pairing unions powers separation infinite hi
      sourceEntry representative generator actor image
  · intro τ' v image
    exact certificate.compression_generator_cap_iff pairing unions powers separation infinite hi generator image

end PartitionPilot.Forcing.GroundInitialMainSuccessorData

end

end OAI
