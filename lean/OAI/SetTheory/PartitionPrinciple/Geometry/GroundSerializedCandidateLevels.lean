import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialMainSeedSuccessorSerialization

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

structure GroundMainCandidateLevel (M : TransitiveGround.{u}) (K : ZFSet.{u}) where
  trace : ZFSet.{u}
  trace_ground : trace ∈ M.sets
  carrier : ZFSet.{u}
  carrier_ground : carrier ∈ M.sets
  hierarchy : GroundCumulativeHierarchyCode M (insert K K) trace
  entry : ZFSet.pair K carrier ∈ trace
  membership : ∀ x, x ∈ carrier ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank K

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundMainCandidateLevel
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {K : ZFSet.{u}}
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) :
    Nonempty (GroundMainCandidateLevel M K) := by
  obtain ⟨H, hH, V, hV, hierarchy, entry, membership, _, _⟩ :=
    M.exists_groundCumulativeLevel pairing unions powers separation collection hK ordinal
  exact ⟨⟨H, hH, V, hV, hierarchy, entry, membership⟩⟩

end TransitiveGround

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
include pairing unions powers separation

include infinite hK conditions in
theorem stage_mem {C D rD Labels : ZFSet.{u}}
    (source : GroundChronologicalMainStage M C D rD) (invariant : source.Invariant K Labels) :
    source.stage.code ∈ level.carrier :=
  (level.membership _).2 ⟨source.stage.code_mem pairing,
    invariant.code_rank_lt pairing unions powers separation infinite hK conditions⟩

include infinite hK conditions in
theorem birth_mem {C D rD Labels : ZFSet.{u}}
    (source : GroundChronologicalMainStage M C D rD) (invariant : source.Invariant K Labels) :
    source.birth ∈ level.carrier :=
  (level.membership _).2 ⟨source.birth_ground,
    invariant.birth_rank_lt pairing unions powers separation infinite hK conditions⟩

include infinite hK conditions in
theorem transition_mem {C D rD Labels : ZFSet.{u}}
    {source target : GroundChronologicalMainStage M C D rD}
    (transition : GroundMainTransition source.stage target.stage)
    (first : source.Invariant K Labels) (second : target.Invariant K Labels) :
    transition.code ∈ level.carrier :=
  (level.membership _).2 ⟨transition.code_mem pairing,
    transition.code_rank_lt_inaccessible pairing unions powers separation infinite hK conditions
      first.points_rank second.points_rank first.actors_rank second.actors_rank⟩

theorem relationSpace_ground {I : ZFSet.{u}} (hI : I ∈ M.sets) :
    M.groundRelations I level.carrier ∈ M.sets :=
  M.groundRelations_mem pairing unions powers separation hI level.carrier_ground

end GroundMainCandidateLevel






namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

noncomputable def validStages (C D rD : ZFSet.{u}) : ZFSet.{u} :=
  M.mainStageCandidates level.carrier C D rD

theorem validStages_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {C D rD : ZFSet.{u}} (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    level.validStages C D rD ∈ M.sets :=
  M.mainStageCandidates_mem pairing unions powers separation infinite level.carrier_ground hC hD hrD

theorem invariant_mem_validStages
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    {C D rD Labels : ZFSet.{u}} (source : GroundChronologicalMainStage M C D rD)
    (invariant : source.Invariant K Labels) : source.stage.code ∈ level.validStages C D rD :=
  M.mainStage_code_mem_candidates source.stage
    (level.stage_mem pairing unions powers separation infinite hK conditions source invariant)

theorem validStageFamily_rank_lt
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    {I C D rD f : ZFSet.{u}} (hI : I ∈ K) (hf : f ∈ M.sets)
    (function : ZFSet.IsFunc I (level.validStages C D rD) f) :
    ZFSet.rank f < ZFSet.rank K := by
  apply conditions.functionGraphOn_rank_lt pairing unions powers separation collection infinite
    hK hI hf ⟨level.validStages C D rD, function⟩
  intro i _ v entry
  have hv := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  have inLevel := ((M.mem_mainStageCandidates level.carrier C D rD v).1 hv).1
  exact ((level.membership v).1 inLevel).2

end GroundMainCandidateLevel

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundMainSeedCandidates
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ level : GroundMainCandidateLevel M K, ∃ seed : GroundInitialMainSeedData M K C,
      ∃ certificate : GroundInitialMainSuccessorData M C (rationalCarrier seed.fractionCode)
          (rationalLtGraph seed.fractionCode) seed.source C,
        certificate.target.Invariant K C ∧
          level.validStages C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) ∈ M.sets ∧
          seed.source.stage.code ∈ level.validStages C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) ∧
          certificate.target.stage.code ∈ level.validStages C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) ∧
          seed.source.birth ∈ level.carrier ∧ certificate.target.birth ∈ level.carrier ∧
          certificate.transition.map.code ∈ level.carrier := by
  dsimp only
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨level⟩ := M.exists_groundMainCandidateLevel pairing unions powers separation collection hK conditions.1
  obtain ⟨seed, certificate, invariant, _⟩ := M.exists_groundInitialMainSeedSuccessor
    pairing unions powers separation collection infinite choice hK standard
  exact ⟨level, seed, certificate, invariant,
    level.validStages_ground pairing unions powers separation infinite seed.source.stage.columns_ground
      seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground,
    level.invariant_mem_validStages pairing unions powers separation infinite hK conditions seed.source seed.invariant,
    level.invariant_mem_validStages pairing unions powers separation infinite hK conditions certificate.target invariant,
    level.birth_mem pairing unions powers separation infinite hK conditions seed.source seed.invariant,
    level.birth_mem pairing unions powers separation infinite hK conditions certificate.target invariant,
    level.transition_mem pairing unions powers separation infinite hK conditions certificate.transition.map seed.invariant invariant⟩

end TransitiveGround





namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

noncomputable def validChronologies (C D rD : ZFSet.{u}) : ZFSet.{u} :=
  M.serializedChronologyCandidates level.carrier C D rD

theorem validChronologies_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {C D rD : ZFSet.{u}} (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    level.validChronologies C D rD ∈ M.sets :=
  M.serializedChronologyCandidates_mem pairing unions powers separation infinite
    level.carrier_ground hC hD hrD

theorem ranked_mem_validChronologies
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {T C D rD : ZFSet.{u}} (serial : GroundSerializedChronology M T C D rD)
    (rank : ZFSet.rank serial.code < ZFSet.rank K) :
    serial.code ∈ level.validChronologies C D rD :=
  M.serializedChronology_code_mem_candidates serial
    ((level.membership _).2 ⟨serial.code_ground pairing, rank⟩)

theorem validChronologyFamily_rank_lt
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    {I C D rD f : ZFSet.{u}} (hI : I ∈ K) (hf : f ∈ M.sets)
    (function : ZFSet.IsFunc I (level.validChronologies C D rD) f) :
    ZFSet.rank f < ZFSet.rank K := by
  apply conditions.functionGraphOn_rank_lt pairing unions powers separation collection infinite
    hK hI hf ⟨level.validChronologies C D rD, function⟩
  intro i _ v entry
  have member := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  have inLevel := ((M.mem_serializedChronologyCandidates level.carrier C D rD v).1 member).1
  exact ((level.membership v).1 inLevel).2

end GroundMainCandidateLevel

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundInitialChronologyCandidates
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ level : GroundMainCandidateLevel M K, ∃ seed : GroundInitialMainSeedData M K C,
      ∃ serial : GroundSerializedChronology M (insert (∅ : ZFSet.{u}) ∅)
          C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode),
        level.validChronologies C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) ∈ M.sets ∧
          serial.code ∈ level.validChronologies C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) ∧
          serial.fields.graph = seed.source.stage.initialChronologyGraph ∧
          serial.toHistory.space ∅ = seed.source.stage.carrier ∧
          serial.toHistory.order ∅ = seed.source.stage.order ∧
          serial.toHistory.meetGraph ∅ = seed.source.stage.meetGraph ∧
          serial.toHistory.birth ∅ = seed.source.birth ∧
          serial.toHistory.height ∅ = seed.source.stage.height := by
  dsimp only
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨level⟩ := M.exists_groundMainCandidateLevel pairing unions powers separation collection hK conditions.1
  obtain ⟨seed⟩ := M.exists_groundInitialMainSeed pairing unions powers separation infinite collection hK conditions
  obtain ⟨injection, _, injected, hInjection, _, rank, fields, values⟩ :=
    seed.exists_rankedInitialSerialization pairing unions powers separation infinite hK conditions
  let serial := seed.source.stage.initialSerializedChronology pairing unions powers separation hInjection injected
  exact ⟨level, seed, serial,
    level.validChronologies_ground pairing unions powers separation infinite seed.source.stage.columns_ground
      seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground,
    level.ranked_mem_validChronologies pairing serial rank, fields, values⟩

end TransitiveGround
end PartitionPilot.Forcing

end OAI
