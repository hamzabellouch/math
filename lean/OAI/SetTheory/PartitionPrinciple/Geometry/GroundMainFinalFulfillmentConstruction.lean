import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainOrdinalConstructionData
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixFinalDirectedness
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixFinalInsertion

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]

structure FinalFulfillment
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (level : GroundMainCandidateLevel M K) (i₀ : I) where
  chronology : run.FinalChronology level
  countable_localization : ∀ X ∈ M.sets, X ⊆ (run.finalGeometry i₀).carrier →
    M.groundEmbeddable X ZFSet.omega →
    (∃ j, ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
      ZFSet.pair y x ∈ (run.finalInclusions i₀).pointMap j) ∧
    ∃ b ∈ (run.finalGeometry i₀).carrier,
      ∀ x ∈ X, ZFSet.pair x b ∈ (run.finalGeometry i₀).order
  growth : ∀ x ∈ (run.finalGeometry i₀).carrier, ∃ y ∈ (run.finalGeometry i₀).carrier,
    ZFSet.pair x y ∈ (run.finalGeometry i₀).order ∧
      ¬ ZFSet.pair y x ∈ (run.finalGeometry i₀).order
  directed : ∀ x ∈ (run.finalGeometry i₀).carrier, ∀ y ∈ (run.finalGeometry i₀).carrier,
    ∃ z ∈ (run.finalGeometry i₀).carrier, ZFSet.pair x z ∈ (run.finalGeometry i₀).order ∧
      ZFSet.pair y z ∈ (run.finalGeometry i₀).order
  separates : ∀ W ∈ (run.finalGeometry i₀).carrier, ∀ d ∈ (run.finalGeometry i₀).carrier,
    ∀ x ∈ (run.finalGeometry i₀).carrier,
    ZFSet.pair W d ∈ (run.finalGeometry i₀).order →
    ZFSet.pair W x ∈ (run.finalGeometry i₀).order →
    ∃ k ∈ (run.finalGeometry i₀).actors,
      (∀ z ∈ (run.finalGeometry i₀).carrier, ZFSet.pair z W ∈ (run.finalGeometry i₀).order →
        ZFSet.pair (ZFSet.pair k z) z ∈ (run.finalGeometry i₀).action) ∧
      ∃ y ∈ (run.finalGeometry i₀).carrier,
        ZFSet.pair (ZFSet.pair k d) y ∈ (run.finalGeometry i₀).action ∧
        ZFSet.pair (ZFSet.pair y x) W ∈ (run.finalGeometry i₀).meetGraph
  rectangles : ∀ c b d g h X,
    ExternalRectangleCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).actors
      (run.finalGeometry i₀).order (run.finalGeometry i₀).meetGraph (run.finalGeometry i₀).action
      c b d g h → X ∈ (run.finalGeometry i₀).carrier →
    (∀ y ∈ (run.finalGeometry i₀).carrier,
      ZFSet.pair (ZFSet.pair g d) y ∈ (run.finalGeometry i₀).action →
      ZFSet.pair y X ∈ (run.finalGeometry i₀).order) →
    (∀ y ∈ (run.finalGeometry i₀).carrier,
      ZFSet.pair (ZFSet.pair h d) y ∈ (run.finalGeometry i₀).action →
      ZFSet.pair y X ∈ (run.finalGeometry i₀).order) →
    ∃ k ∈ (run.finalGeometry i₀).actors, ∃ l ∈ (run.finalGeometry i₀).actors,
      RectangleAtBoundCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
        (run.finalGeometry i₀).meetGraph (run.finalGeometry i₀).action c b d g h X k l

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainOrdinalConstructionData
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K C : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable (data : GroundMainOrdinalConstructionData M K C pairing unions powers separation)

theorem exists_rankedTerminal
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (columns : C = M.groundOmegaOne pairing unions powers separation collection infinite) :
    ∃ ordinalC : ordinalSetProperty C,
      letI := ordinalMainIndexPreorder ordinalC
      ∃ run : GroundMainPrefix M K C C (rationalCarrier data.seed.fractionCode)
          (rationalLtGraph data.seed.fractionCode) pairing unions powers separation (SetMembers C),
        run.indices = C ∧ run.PreservesOldProfiles ∧
        MainPrefixHistoryUnionCode data.history run.code ∧
        MainPrefixHistoryExtends data.history run.code ∧
        (∀ q, MainPrefixHistoryUnionCode data.history q → q = run.code) ∧
        GroundBelow M run.indices K ∧ ZFSet.rank run.code < ZFSet.rank K ∧
        run.code ∈ data.level.preservedMainPrefixes C C (rationalCarrier data.seed.fractionCode)
          (rationalLtGraph data.seed.fractionCode) ∧
        ∃ i₀ : SetMembers C, run.key i₀ = ∅ := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have hC : C ∈ M.sets := columns.symm ▸ spec.1
  have ordinal : ordinalSetProperty C := columns.symm ▸ spec.2.1
  have candidates : ∀ q ∈ data.domain, PreservedMainPrefixCode M K C C
      (rationalCarrier data.seed.fractionCode) (rationalLtGraph data.seed.fractionCode) q := by
    intro q member
    rw [data.domain_eq] at member
    exact (data.level.mem_preservedMainPrefixes.1 (data.level.mem_recursionPrefixes.1 member).1).2
  obtain ⟨ordinalC, run, indices, profiles, terminal, extension, unique⟩ :=
    data.trace.exists_groundTerminalPrefix pairing unions powers separation hC ordinal data.history_ground candidates
  let := ordinalMainIndexPreorder ordinalC
  obtain ⟨small, _, rank, candidate⟩ :=
    data.trace.groundOmegaOne_terminalCode_ranked_candidate pairing unions powers separation collection infinite
      hK standard columns data.history_ground data.level data.domain_eq terminal
  have zero : ∅ ∈ C := by
    rw [columns]
    exact (spec.2.2.1 ∅).2
      ⟨M.empty_mem ⟨_, spec.1⟩, ordinalSetProperty_empty,
        M.empty_groundEmbeddable ZFSet.omega ⟨_, spec.1⟩⟩
  have zeroIndex : ∅ ∈ run.indices := indices.symm ▸ zero
  obtain ⟨i₀, key⟩ := ZFSet.mem_range.1 zeroIndex
  exact ⟨ordinalC, run, indices, profiles, terminal, extension, unique,
    indices.symm ▸ small, rank, candidate, i₀, key⟩

end PartitionPilot.Forcing.GroundMainOrdinalConstructionData



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundMainFinalGeometry
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
            let geometry := run.finalGeometry i₀
            let inclusions := run.finalInclusions i₀
            geometry.code ∈ M.sets ∧ ZFSet.rank geometry.code < ZFSet.rank K ∧
            GroundBelow M geometry.carrier K ∧ GroundBelow M geometry.actors K ∧
            inclusions.pointFamily ∈ M.sets ∧ inclusions.actorFamily ∈ M.sets ∧
            ZFSet.rank inclusions.pointFamily < ZFSet.rank K ∧
            ZFSet.rank inclusions.actorFamily < ZFSet.rank K ∧
            (∀ X ∈ M.sets, X ⊆ geometry.carrier → M.groundEmbeddable X ZFSet.omega →
              (∃ j, ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
                ZFSet.pair y x ∈ inclusions.pointMap j) ∧
              ∃ b ∈ geometry.carrier, ∀ x ∈ X, ZFSet.pair x b ∈ geometry.order) ∧
            ∀ x ∈ geometry.carrier, ∃ y ∈ geometry.carrier,
              ZFSet.pair x y ∈ geometry.order ∧ ¬ ZFSet.pair y x ∈ geometry.order := by
  dsimp only
  obtain ⟨data⟩ := M.exists_groundMainOrdinalData pairing unions powers separation
    collection infinite choice hK standard
  obtain ⟨ordinalC, run, indices, profiles, terminal, extension, unique, small, rank, _, i₀, zero⟩ :=
    data.exists_rankedTerminal collection infinite hK standard rfl
  let := ordinalMainIndexPreorder ordinalC
  have limit := (standard.to_conditions pairing unions powers separation hK).rank_isLimit
    pairing unions powers separation infinite hK
  have sizes := run.finalGeometry_below i₀ choice hK standard small
  have maps := run.finalInclusions_rank_lt i₀ limit rank
  refine ⟨data, ordinalC, run, indices, profiles, terminal, extension, unique, small, rank,
    i₀, zero, (run.finalGeometry i₀).code_ground pairing,
    run.finalGeometry_code_rank_lt i₀ limit rank, sizes.1, sizes.2,
    (run.finalInclusions i₀).pointFamily_ground, (run.finalInclusions i₀).actorFamily_ground,
    maps.1, maps.2.1, ?_, ?_⟩
  · intro X hX subset countable
    have localized := run.exists_countablePointLocalization collection infinite choice indices hX subset countable
    obtain ⟨_, b, _, hb, _, bound⟩ :=
      run.exists_countablePointUpperBound collection infinite choice indices hX subset countable
    exact ⟨localized, b, hb, bound⟩
  · intro x member
    exact run.limitPoints_strict_extension_of_trace collection infinite data.trace
      (fun old next entry => (data.steps_entries old next entry).2)
      (fun source target z entry => (data.successors_entries source target z entry).2.2)
      indices extension member

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundMainFinalFulfillment
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
            ∃ fulfilled : run.FinalFulfillment data.level i₀,
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
    i₀, zero, codeGround, codeRank, pointSmall, actorSmall, pointMaps, actorMaps,
    pointRank, actorRank, localized, growth⟩ :=
    M.exists_groundMainFinalGeometry pairing unions powers separation collection infinite choice hK standard
  let := ordinalMainIndexPreorder ordinalC
  obtain ⟨chronology⟩ := run.exists_finalChronology collection infinite choice hK standard
    small rank data.level
  have chosen := fun old next entry => (data.steps_entries old next entry).2
  have tasks := fun source target z entry => (data.successors_entries source target z entry).2.2
  let fulfilled : run.FinalFulfillment data.level i₀ := {
    chronology := chronology
    countable_localization := localized
    growth := growth
    directed := fun _ hx _ hy => run.limitPoints_directed hx hy
    separates := fun _ hW _ hd _ hx wd wx =>
      run.limitPoints_separation_of_trace collection infinite data.trace chosen tasks
        indices extension hW hd hx wd wx
    rectangles := fun _ _ _ _ _ _ rectangle hX firstUpper secondUpper =>
      run.final_rectangle_at_bound_of_trace collection infinite data.trace chosen tasks
        indices extension rectangle hX firstUpper secondUpper }
  refine ⟨data, ordinalC, run, indices, profiles, terminal, extension, unique, small, rank,
    i₀, zero, fulfilled, codeGround, codeRank, pointSmall, actorSmall, pointMaps,
    actorMaps, pointRank, actorRank, chronology.code_ground, ?_⟩
  intro N includes pairingN unionsN powersN separationN infiniteN choiceN F hF filter
  exact chronology.exists_extension_basis i₀ includes pairingN unionsN powersN separationN infiniteN
    choiceN ⟨data.seed.coordinateInjection, data.seed.injection_ground, data.seed.injection_code⟩
    data.seed.dense.irrefl hF filter

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
