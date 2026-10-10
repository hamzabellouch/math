import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalFulfillmentConstruction

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]

structure FinalSupportFulfillment
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (level : GroundMainCandidateLevel M K) (i₀ : I) extends run.FinalFulfillment level i₀ where
  insertion : ∀ c ∈ (run.finalGeometry i₀).carrier, ∀ e ∈ (run.finalGeometry i₀).carrier,
    ∀ d ∈ (run.finalGeometry i₀).carrier, ∀ F ∈ M.sets,
    MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F →
    ZFSet.pair c e ∈ (run.finalGeometry i₀).order →
    ZFSet.pair e c ∉ (run.finalGeometry i₀).order →
    ZFSet.pair c d ∈ (run.finalGeometry i₀).order →
    (∀ x ∈ F, ZFSet.pair e x ∈ (run.finalGeometry i₀).order) →
    ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
      FinalInsertionFamiliesCode Labels (run.finalGeometry i₀).carrier (run.finalGeometry i₀).actors
        (run.finalGeometry i₀).order (run.finalGeometry i₀).meetGraph (run.finalGeometry i₀).action
        c e d F caps actors

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
include fulfilled

theorem tested_filter_generators
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {F e : ZFSet.{u}} (hF : F ∈ M.sets)
    (filter : MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F)
    (he : e ∈ (run.finalGeometry i₀).carrier) :
    let geometry := run.finalGeometry i₀
    let tested := testedMeetFilter F geometry.order e
    tested ∈ M.sets ∧ MeetFilterCode geometry.carrier geometry.order geometry.meetGraph tested ∧
    (∀ x ∈ tested, ZFSet.pair e x ∈ geometry.order) ∧
    ∃ B ∈ M.sets, M.groundEmbeddable B ZFSet.omega ∧ B.Nonempty ∧ B ⊆ tested ∧
      (∀ x ∈ tested, ∃ b ∈ B, ZFSet.pair b x ∈ geometry.order) ∧
      M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph B = tested := by
  let geometry := run.finalGeometry i₀
  let tested := testedMeetFilter F geometry.order e
  have ground : tested ∈ M.sets := M.testedMeetFilter_mem pairing separation hF
    geometry.order_ground (M.transitive geometry.carrier_ground he)
  have testedFilter : MeetFilterCode geometry.carrier geometry.order geometry.meetGraph tested :=
    testedMeetFilter_filter geometry.meet filter he fulfilled.directed
  obtain ⟨B, hB, f, hf, injective, contained, coinitial⟩ :=
    fulfilled.chronology.exists_extension_basis i₀ (N := M) (fun _ hx => hx)
      pairing unions powers separation infinite choice smallD irreflexive ground testedFilter
  have nonempty : B.Nonempty := by
    obtain ⟨x, hx⟩ := testedFilter.nonempty
    obtain ⟨b, hb, _⟩ := coinitial x hx
    exact ⟨b, hb⟩
  have inNodes : B ⊆ geometry.carrier := fun _ hb => testedFilter.subset (contained hb)
  have generatedFilter := M.generatedMeetFilter_filter pairing unions separation infinite
    geometry.carrier_ground geometry.meet inNodes nonempty
  have generators := M.generatedMeetFilter_contains pairing unions separation infinite
    geometry.carrier_ground geometry.meet inNodes
  refine ⟨ground, testedFilter, fun x hx => (mem_testedMeetFilter F geometry.order e x).1 hx |>.2,
    B, hB, ⟨f, hf, injective⟩, nonempty, contained, coinitial, ?_⟩
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    exact M.generatedMeetFilter_least pairing unions separation infinite geometry.carrier_ground
      geometry.meet inNodes testedFilter contained hx
  · intro hx
    obtain ⟨b, hb, bx⟩ := coinitial x hx
    exact generatedFilter.upward b (generators hb) x (testedFilter.subset hx) bx

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundMainFinalSupport
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ data : GroundMainOrdinalConstructionData M K C pairing unions powers separation,
      ∃ ordinalC : ordinalSetProperty C,
        letI := ordinalMainIndexPreorder ordinalC
        ∃ run : GroundMainPrefix M K C C (rationalCarrier data.seed.fractionCode)
            (rationalLtGraph data.seed.fractionCode) pairing unions powers separation (SetMembers C),
          run.indices = C ∧ run.PreservesOldProfiles ∧
          MainPrefixHistoryUnionCode data.history run.code ∧
          MainPrefixHistoryExtends data.history run.code ∧
          (∀ q, MainPrefixHistoryUnionCode data.history q → q = run.code) ∧
          GroundBelow M run.indices K ∧ ZFSet.rank run.code < ZFSet.rank K ∧
          ∃ i₀ : SetMembers C, run.key i₀ = ∅ ∧
            ∃ fulfilled : run.FinalSupportFulfillment data.level i₀,
              let geometry := run.finalGeometry i₀
              let inclusions := run.finalInclusions i₀
              geometry.code ∈ M.sets ∧ ZFSet.rank geometry.code < ZFSet.rank K ∧
              GroundBelow M geometry.carrier K ∧ GroundBelow M geometry.actors K ∧
              inclusions.pointFamily ∈ M.sets ∧ inclusions.actorFamily ∈ M.sets ∧
              ZFSet.rank inclusions.pointFamily < ZFSet.rank K ∧
              ZFSet.rank inclusions.actorFamily < ZFSet.rank K ∧
              fulfilled.chronology.serial.code ∈ M.sets ∧
              ∀ N : TransitiveGround.{u}, M.sets ⊆ N.sets →
                Realize N.sets SetFormula.pairing Fin.elim0 →
                Realize N.sets SetFormula.union Fin.elim0 →
                Realize N.sets powerSet Fin.elim0 → SeparationSchema N.sets →
                Realize N.sets infinity Fin.elim0 → Realize N.sets SetFormula.choice Fin.elim0 →
                ∀ F ∈ N.sets, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F →
                  ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
                    ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ geometry.order := by
  dsimp only
  obtain ⟨data, ordinalC, run, indices, profiles, terminal, extension, unique, small, rank,
    i₀, zero, fulfilled, codeGround, codeRank, pointSmall, actorSmall, pointMaps,
    actorMaps, pointRank, actorRank, chronologyGround, basis⟩ :=
    M.exists_groundMainFinalFulfillment pairing unions powers separation collection infinite choice hK standard
  let := ordinalMainIndexPreorder ordinalC
  let support : run.FinalSupportFulfillment data.level i₀ := {
    toFinalFulfillment := fulfilled
    insertion := fun c hc e he d hd F hF filter lower strict bound above =>
      fulfilled.chronology.final_insertion_of_trace i₀ collection infinite choice data.trace
        (fun old next entry => (data.steps_entries old next entry).2)
        (fun source target z entry => (data.successors_entries source target z entry).2.2)
        indices extension profiles
        (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
        ⟨data.seed.coordinateInjection, data.seed.injection_ground, data.seed.injection_code⟩
        data.seed.dense.irrefl hc he hd hF filter lower strict bound above }
  exact ⟨data, ordinalC, run, indices, profiles, terminal, extension, unique, small, rank,
    i₀, zero, support, codeGround, codeRank, pointSmall, actorSmall, pointMaps,
    actorMaps, pointRank, actorRank, chronologyGround, basis⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
