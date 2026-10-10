import OAI.SetTheory.PartitionPrinciple.Definability.ExternalStarCarrierRanks
import OAI.SetTheory.PartitionPrinciple.Definability.GroundMainCodeRanks
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalMainTransition
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalRawPriorLayers
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCompressionCarrierRankBounds

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundChronologicalMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (source : GroundChronologicalMainStage M C D rD)
variable {initial : RecursiveStateData.{u}} {I Sources Reps T Targets Separators Filters lo hi : ZFSet.{u}}
variable (compression : GroundChronologicalCompression M initial I Sources Reps source.stage.actors
  source.stage.multiplication source.stage.identity T source.stage.top source.stage.carrier C D rD
  source.stage.height Targets Separators Filters source.cutoff source.birth
  (insert source.cutoff source.cutoff) source.history)
variable {births : GroundExternalBirthData M initial I Sources Reps source.stage.actors
  source.stage.multiplication source.stage.identity T source.stage.top source.stage.carrier source.stage.order
  source.stage.meetGraph source.stage.action compression.born.births.limit compression.born.births.birth
  compression.born.profiled.heighted.completion}
variable {heights : GroundExternalHeightData M initial I Sources Reps source.stage.actors
  source.stage.multiplication source.stage.identity T source.stage.top source.stage.carrier source.stage.order
  source.stage.meetGraph source.stage.action C D rD lo hi compression.born.profiled.heighted.heights.height
  compression.born.profiled.heighted.completion}
variable (external : GroundChronologicalExternal M initial I Sources Reps source.stage.actors
  source.stage.multiplication source.stage.inverse source.stage.identity T source.stage.top source.stage.carrier
  source.stage.order source.stage.meetGraph source.stage.action compression.born.births.limit compression.born.births.birth
  C D rD lo hi compression.born.profiled.heighted.heights.height
  (insert compression.born.births.limit compression.born.births.limit)
  compression.born.profiled.heighted.completion births heights compression.history)
variable (origin : GroundCompressionOrigin M initial source.stage.carrier source.stage.order source.stage.meetGraph
  source.stage.action source.stage.top I Sources Reps source.stage.actors source.stage.multiplication
  source.stage.inverse source.stage.identity T Filters)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets) (hT : T ∈ M.sets)
variable (initialDomain : initial.D = source.stage.carrier) (initialOrder : initial.rD = source.stage.order)
variable (boundedHeights : GroundBoundedExternalHeightData M initial I Sources Reps source.stage.actors
  source.stage.multiplication source.stage.identity T source.stage.top source.stage.carrier source.stage.order
  source.stage.meetGraph source.stage.action C D rD lo hi compression.born.profiled.heighted.heights.height
  compression.born.profiled.heighted.completion heights)
variable (boundedBirths : GroundBoundedExternalBirthData M initial I Sources Reps source.stage.actors
  source.stage.multiplication source.stage.identity T source.stage.top source.stage.carrier source.stage.order
  source.stage.meetGraph source.stage.action compression.born.births.limit compression.born.births.birth
  compression.born.profiled.heighted.completion births)
variable {b' : ZFSet.{u}} (image : ZFSet.pair source.stage.bottom b' ∈
  compression.born.profiled.heighted.completion.externalOriginalEmbedding
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action)

include compression in
theorem external_cutoff_strict : source.cutoff ∈ births.limit :=
  births.times.ordinal.1 compression.born.births.limit births.times.base_mem_limit
    source.cutoff compression.born.births.times.base_mem_limit

noncomputable def externalTransition :
    GroundChronologicalMainTransition source
      (external.toMainStage origin source.stage.group_code source.stage.action_code pairing unions powers separation
        infinite hI hSources hReps source.stage.actors_ground hT source.stage.carrier_ground
        initialDomain initialOrder boundedHeights source.stage.columns_ground source.stage.coordinates_ground
        source.stage.coordinate_order_ground source.stage.least image) where
  map := source.stage.externalTransition external.inputs origin pairing unions powers separation infinite
    hI hSources hReps hT initialDomain initialOrder compression.born.profiled.heighted.heights heights boundedHeights image
  cutoff_le := Or.inr (source.external_cutoff_strict compression)
  birth := by
    intro x y t entry
    rw [external.toMainStage_birth]
    exact births.bounded_preserves_original compression.born.births boundedBirths initialDomain entry
  history_prefix := by
    intro s before
    have first : s ∈ compression.born.births.limit := by
      rcases before with rfl | before
      · exact compression.born.births.times.base_mem_limit
      · exact compression.born.births.times.ordinal.1 source.cutoff
          compression.born.births.times.base_mem_limit s before
    have final : s ∈ births.limit := births.times.ordinal.1 compression.born.births.limit
      births.times.base_mem_limit s first
    have a := compression.old_values s before.symm
    have b := external.old_values s (Or.inl first)
    have c := external.bounded_old_values s final
    exact ⟨c.1.trans (b.1.trans a.1), c.2.1.trans (b.2.1.trans a.2.1),
      c.2.2.1.trans (b.2.2.1.trans a.2.2.1), c.2.2.2.1.trans (b.2.2.2.1.trans a.2.2.2.1),
      c.2.2.2.2.trans (b.2.2.2.2.trans a.2.2.2.2)⟩

theorem externalTransition_graphs :
    let transition := source.externalTransition compression external origin pairing unions powers separation infinite
      hI hSources hReps hT initialDomain initialOrder boundedHeights boundedBirths image
    transition.map.points = compression.born.profiled.heighted.completion.externalOriginalEmbedding
      source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action ∧
    transition.map.actors = M.externalOldInclusion source.stage.actors
      (externalChildLetters I source.stage.carrier
        (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph
          source.stage.action)) source.stage.multiplication source.stage.identity := ⟨rfl, rfl⟩

end GroundChronologicalMainStage

section
universe u

structure GroundInitialMainSuccessorData (M : TransitiveGround.{u}) (C D rD : ZFSet.{u})
    (source : GroundChronologicalMainStage M C D rD) (Labels : ZFSet.{u}) where
  indices_ground : (source.stage.compressionTasks Labels) ∈ M.sets
  sources_ground : (source.stage.compressionSources Labels) ∈ M.sets
  filters_ground : (source.stage.compressionFilters Labels) ∈ M.sets
  task_action_ground : (source.stage.compressionTaskAction Labels) ∈ M.sets
  Reps : ZFSet.{u}
  representatives_ground : Reps ∈ M.sets
  origin : GroundCompressionOrigin M (source.stage.compressionInitial Labels)
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action source.stage.top
    (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.inverse source.stage.identity (source.stage.compressionTaskAction Labels) (source.stage.compressionFilters Labels)
  compression : GroundChronologicalCompression M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier C D rD source.stage.height (source.stage.compressionTargets Labels) (source.stage.compressionSeparators Labels) (source.stage.compressionFilters Labels)
    source.cutoff source.birth (insert source.cutoff source.cutoff) source.history
  geometry : GroundExternalGeometryData M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action compression.born.profiled.heighted.completion
  boundedGeometry : GroundExternalBoundedGeometryData M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action compression.born.profiled.heighted.completion
  lo : ZFSet.{u}
  hi : ZFSet.{u}
  lo_mem : lo ∈ D
  hi_mem : hi ∈ D
  interval : ZFSet.pair lo hi ∈ rD
  heights : GroundExternalHeightData M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action C D rD lo hi
    compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion
  boundedHeights : GroundBoundedExternalHeightData M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action C D rD lo hi
    compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion heights
  births : GroundExternalBirthData M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action
    compression.born.births.limit compression.born.births.birth compression.born.profiled.heighted.completion
  boundedBirths : GroundBoundedExternalBirthData M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action
    compression.born.births.limit compression.born.births.birth compression.born.profiled.heighted.completion births
  external : GroundChronologicalExternal M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.inverse source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action compression.born.births.limit compression.born.births.birth
    C D rD lo hi compression.born.profiled.heighted.heights.height (insert compression.born.births.limit compression.born.births.limit)
    compression.born.profiled.heighted.completion births heights compression.history
  bottomImage : ZFSet.{u}
  bottom_ground : bottomImage ∈ M.sets
  bottom_entry : ZFSet.pair source.stage.bottom bottomImage ∈
    compression.born.profiled.heighted.completion.externalOriginalEmbedding source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action
  target : GroundChronologicalMainStage M C D rD
  transition : GroundChronologicalMainTransition source target
  cutoff_strict : source.cutoff ∈ target.cutoff
  target_cutoff : target.cutoff = births.limit
  target_history : HEq target.history external.bounded_history
  target_fields :
    target.stage.carrier = compression.born.profiled.heighted.completion.externalBoundedCarrier source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action ∧
    target.stage.order = compression.born.profiled.heighted.completion.externalBoundedOrder source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action ∧
    target.stage.meetGraph = compression.born.profiled.heighted.completion.externalBoundedMeet source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action ∧
    target.stage.actors = M.externalGroupCarrier source.stage.actors (externalChildLetters (source.stage.compressionTasks Labels) source.stage.carrier (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)) source.stage.multiplication source.stage.identity ∧
    target.stage.multiplication = M.externalGroupMultiplication source.stage.actors (externalChildLetters (source.stage.compressionTasks Labels) source.stage.carrier (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)) source.stage.multiplication source.stage.identity ∧
    target.stage.inverse = M.externalGroupInverse source.stage.actors (externalChildLetters (source.stage.compressionTasks Labels) source.stage.carrier (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)) source.stage.multiplication source.stage.inverse source.stage.identity ∧
    target.stage.identity = M.externalGroupIdentity source.stage.actors (externalChildLetters (source.stage.compressionTasks Labels) source.stage.carrier (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)) source.stage.multiplication source.stage.identity ∧
    target.stage.action = compression.born.profiled.heighted.completion.externalBoundedAction source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action ∧
    target.stage.bottom = bottomImage ∧
    target.stage.top = compression.born.profiled.heighted.completion.externalPointCarrier source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action ∧
    target.stage.height = heights.boundedHeight
  target_birth : target.birth = births.boundedBirth
  point_graph : transition.map.points = compression.born.profiled.heighted.completion.externalOriginalEmbedding
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action
  actor_graph : transition.map.actors = M.externalOldInclusion source.stage.actors
    (externalChildLetters (source.stage.compressionTasks Labels) source.stage.carrier (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)) source.stage.multiplication source.stage.identity
  strict_new_top : ∀ x y, ZFSet.pair x y ∈ transition.map.points →
    ZFSet.pair y target.stage.top ∈ target.stage.order ∧
      ZFSet.pair target.stage.top y ∉ target.stage.order

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)

include choice in
theorem exists_groundInitialMainSuccessor {D rD Labels c : ZFSet.{u}}
    (source : GroundChronologicalMainStage M
      (M.groundOmegaOne pairing unions powers separation collection infinite) D rD)
    (hLabels : Labels ∈ M.sets) (hc : c ∈ M.sets)
    (dense : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c) :
    Nonempty (GroundInitialMainSuccessorData M
      (M.groundOmegaOne pairing unions powers separation collection infinite) D rD source Labels) := by
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, _data, geometry,
      boundedGeometry, lo, hlo, hi, hhi, gap, heights, boundedHeights, births, boundedBirths,
      ⟨external⟩⟩ :=
    M.exists_groundInitialExternalChronology pairing unions powers separation collection infinite choice
      source.stage.carrier_ground source.stage.actors_ground source.stage.order_ground source.stage.meet_ground
      source.stage.action_ground hLabels source.stage.multiplication_ground source.stage.inverse_ground
      source.stage.group_code source.stage.action_code source.stage.meet source.stage.top_mem source.stage.greatest
      source.stage.coordinates_ground source.stage.coordinate_order_ground hc source.stage.height_ground
      source.stage.height_code dense above coordinateInjection source.stage.height_range_countable
      source.cutoff_ground source.history (ordinalSetProperty_succ source.cutoff_ordinal)
      (ZFSet.mem_insert _ _) source.carrier_eq source.order_eq source.meet_eq rfl source.height_eq
  obtain ⟨b', hb', image, _bottom⟩ :=
    external.inputs.exists_externalOriginal_bottom origin source.stage.group_code source.stage.action_code
      pairing unions powers separation infinite hI hSources hReps source.stage.actors_ground hT
      source.stage.carrier_ground rfl rfl source.stage.bottom_mem source.stage.least
  let target := external.toMainStage origin source.stage.group_code source.stage.action_code
    pairing unions powers separation infinite hI hSources hReps source.stage.actors_ground hT
    source.stage.carrier_ground rfl rfl boundedHeights source.stage.columns_ground
    source.stage.coordinates_ground source.stage.coordinate_order_ground source.stage.least image
  let transition := source.externalTransition compression external origin pairing unions powers separation infinite
    hI hSources hReps hT rfl rfl boundedHeights boundedBirths image
  refine ⟨{
    indices_ground := hI
    sources_ground := hSources
    filters_ground := hFilters
    task_action_ground := hT
    Reps := Reps
    representatives_ground := hReps
    origin := origin
    compression := compression
    geometry := geometry
    boundedGeometry := boundedGeometry
    lo := lo
    hi := hi
    lo_mem := hlo
    hi_mem := hhi
    interval := gap
    heights := heights
    boundedHeights := boundedHeights
    births := births
    boundedBirths := boundedBirths
    external := external
    bottomImage := b'
    bottom_ground := hb'
    bottom_entry := image
    target := target
    transition := transition
    cutoff_strict := source.external_cutoff_strict compression
    target_cutoff := rfl
    target_history := HEq.rfl
    target_fields := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    target_birth := external.toMainStage_birth origin source.stage.group_code source.stage.action_code
      pairing unions powers separation infinite hI hSources hReps source.stage.actors_ground hT
      source.stage.carrier_ground rfl rfl boundedHeights source.stage.columns_ground
      source.stage.coordinates_ground source.stage.coordinate_order_ground source.stage.least image
    point_graph := rfl
    actor_graph := rfl
    strict_new_top := ?_ }⟩
  intro x y entry
  exact external.inputs.externalOriginal_top_strict source.stage.group_code source.stage.action_code
    pairing unions powers separation infinite source.stage.actors_ground source.stage.carrier_ground entry

end TransitiveGround

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
local notation "completion" => certificate.compression.born.profiled.heighted.completion

theorem target_rank_lt_of_components {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (omega : ZFSet.rank ZFSet.omega < o)
    (indices : ZFSet.rank (source.stage.compressionTasks Labels) < o)
    (points : ZFSet.rank source.stage.carrier < o)
    (actors : ZFSet.rank source.stage.actors < o)
    (completed : ZFSet.rank ((completion).algebra.union.fields 0) < o) :
    ZFSet.rank certificate.target.stage.carrier < o ∧
      ZFSet.rank certificate.target.stage.actors < o := by
  constructor
  · rw [certificate.target_fields.1]
    exact (completion).externalBoundedCarrier_rank_lt limit source.stage.order source.stage.meetGraph
      source.stage.action omega indices points actors completed
  · rw [certificate.target_fields.2.2.2.1]
    exact M.externalRequestGroup_rank_lt limit source.stage.order source.stage.meetGraph
      source.stage.action source.stage.multiplication source.stage.identity omega indices points actors

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (points : ZFSet.rank source.stage.carrier < ZFSet.rank K)
variable (labels : ZFSet.rank Labels < ZFSet.rank K)
include certificate pairing unions powers separation collection infinite hK conditions points labels

theorem compression_union_rank_lt :
    ZFSet.rank ((completion).algebra.union.fields 0) < ZFSet.rank K :=
  M.initialCompressionUnion_rank_lt (completion).algebra.union
    pairing unions powers separation collection infinite hK conditions points labels

theorem target_rank_lt (actors : ZFSet.rank source.stage.actors < ZFSet.rank K) :
    ZFSet.rank certificate.target.stage.carrier < ZFSet.rank K ∧
      ZFSet.rank certificate.target.stage.actors < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have tasks := M.groundEligibleTasks_rank_lt limit source.stage.actors source.stage.order
    source.stage.meetGraph source.stage.action points labels
  exact certificate.target_rank_lt_of_components limit (ZFSet.rank_lt_of_mem conditions.2.1)
    tasks points actors
    (certificate.compression_union_rank_lt pairing unions powers separation collection infinite
      hK conditions points labels)

theorem target_code_rank_lt (actors : ZFSet.rank source.stage.actors < ZFSet.rank K)
    (columns : ZFSet.rank C < ZFSet.rank K) (coordinates : ZFSet.rank D < ZFSet.rank K) :
    ZFSet.rank certificate.target.stage.code < ZFSet.rank K := by
  have target := certificate.target_rank_lt pairing unions powers separation collection infinite
    hK conditions points labels actors
  exact certificate.target.stage.code_rank_lt
    (conditions.rank_isLimit pairing unions powers separation infinite hK)
    target.1 target.2 columns coordinates

theorem target_code_rank_lt_omegaOne (actors : ZFSet.rank source.stage.actors < ZFSet.rank K)
    (actualColumns : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (coordinates : ZFSet.rank D < ZFSet.rank K) :
    ZFSet.rank certificate.target.stage.code < ZFSet.rank K := by
  have columns : ZFSet.rank C < ZFSet.rank K := by
    rw [actualColumns]
    exact ZFSet.rank_lt_of_mem
      (conditions.groundOmegaOne_mem pairing unions powers separation collection infinite hK)
  exact certificate.target_code_rank_lt pairing unions powers separation collection infinite
    hK conditions points labels actors columns coordinates

theorem transition_code_rank_lt (actors : ZFSet.rank source.stage.actors < ZFSet.rank K) :
    ZFSet.rank certificate.transition.map.code < ZFSet.rank K := by
  have target := certificate.target_rank_lt pairing unions powers separation collection infinite
    hK conditions points labels actors
  exact certificate.transition.map.code_rank_lt
    (conditions.rank_isLimit pairing unions powers separation infinite hK)
    points target.1 actors target.2

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (sourceTime : source.cutoff ∈ K)
include certificate pairing unions powers separation infinite hK conditions sourceTime

theorem compression_limit_mem : certificate.compression.born.births.limit ∈ K :=
  conditions.compressionStamp_limit_mem pairing unions powers separation infinite hK
    certificate.compression.born.births.times sourceTime certificate.compression.born.births.stamps_ground

theorem external_limit_mem : certificate.births.limit ∈ K :=
  conditions.compressionStamp_limit_mem pairing unions powers separation infinite hK
    certificate.births.times
    (certificate.compression_limit_mem pairing unions powers separation infinite hK conditions sourceTime)
    certificate.births.stamps_ground

theorem target_cutoff_mem : certificate.target.cutoff ∈ K := by
  rw [certificate.target_cutoff]
  exact certificate.external_limit_mem pairing unions powers separation infinite hK conditions sourceTime

theorem target_time_domain_mem : insert certificate.target.cutoff certificate.target.cutoff ∈ K :=
  conditions.successor_mem pairing unions powers separation infinite hK
    (certificate.target_cutoff_mem pairing unions powers separation infinite hK conditions sourceTime)

theorem target_birth_rank_lt
    (points : ZFSet.rank certificate.target.stage.carrier < ZFSet.rank K) :
    ZFSet.rank certificate.target.birth < ZFSet.rank K :=
  rank_functionGraph_lt (conditions.rank_isLimit pairing unions powers separation infinite hK)
    certificate.target.birth_function points
    (ZFSet.rank_lt_of_mem
      (certificate.target_time_domain_mem pairing unions powers separation infinite hK conditions sourceTime))

end GroundInitialMainSuccessorData

section
universe u

namespace GroundCompressionBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T base old : ZFSet.{u}}
variable {union : GroundCompressionUnionData M initial I Sources Reps G m one T}

theorem prior_entry (births : GroundCompressionBirthData M initial I Sources Reps G m one T union base old)
    {x t : ZFSet.{u}} (before : t = base ∨ t ∈ base) (entry : ZFSet.pair x t ∈ births.birth) :
    x ∈ initial.D ∧ ZFSet.pair x t ∈ old := by
  rcases (births.extension.entries x t).1 entry with original | ⟨n, _, _, equal⟩
  · exact ⟨(ZFSet.pair_mem_prod.1 (births.initial_function.1 original)).1, original⟩
  · have absurd := compressionStamp_old_mem before.symm n
    rw [← equal] at absurd
    exact (ZFSet.mem_irrefl t absurd).elim

end GroundCompressionBirthData

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 base old : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (compressionBirths : GroundCompressionBirthData M initial I Sources Reps G m one T
  completion.algebra.union base old)
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 compressionBirths.limit compressionBirths.birth completion)

theorem originalFiber_image (initialDomain : initial.D = P0) {y t : ZFSet.{u}}
    (before : t = base ∨ t ∈ base) (entry : ZFSet.pair y t ∈ births.birth) :
    ∃ x ∈ P0, ZFSet.pair x y ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0 := by
  have earlier : t ∈ compressionBirths.limit := before.elim
    (fun equal => equal.symm ▸ compressionBirths.times.base_mem_limit)
    (fun member => compressionBirths.times.ordinal.1 base compressionBirths.times.base_mem_limit t member)
  obtain ⟨x, _, copied⟩ := births.priorFiber_image (Or.inl earlier) entry
  have original := compressionBirths.prior_entry before ((births.preserves_seed x y t copied).1 entry)
  have hx : x ∈ P0 := initialDomain ▸ original.1
  exact ⟨x, hx, (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 x y).2 ⟨copied, hx⟩⟩

theorem boundedOriginalFiber_image (initialDomain : initial.D = P0) {y t : ZFSet.{u}}
    (before : t = base ∨ t ∈ base) (entry : ZFSet.pair y t ∈ births.boundedBirth) :
    ∃ x ∈ P0, ZFSet.pair x y ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0 := by
  have earlier : t ∈ compressionBirths.limit := before.elim
    (fun equal => equal.symm ▸ compressionBirths.times.base_mem_limit)
    (fun member => compressionBirths.times.ordinal.1 base compressionBirths.times.base_mem_limit t member)
  have final : t ∈ births.limit := births.times.ordinal.1 compressionBirths.limit
    births.times.base_mem_limit t earlier
  exact births.originalFiber_image compressionBirths initialDomain before
    ((fixedTopBirth_earlier_iff final).1 entry)

end GroundExternalBirthData

namespace GroundInitialMainSuccessorData
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

theorem oldBirthFiberCoverage : OldBirthFiberCoverageCode source.stage.carrier
    certificate.transition.map.points certificate.target.birth source.cutoff := by
  intro y t entry before
  rw [certificate.target_birth] at entry
  rw [certificate.point_graph]
  exact certificate.births.boundedOriginalFiber_image certificate.compression.born.births rfl before entry

theorem coversOldBirths : certificate.transition.CoversOldBirths :=
  certificate.oldBirthFiberCoverage

end GroundInitialMainSuccessorData
end

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

theorem capProfile_preserved
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {c e K F c' e' K' : ZFSet.{u}}
    (profile : CodedCapProfile source.stage.carrier source.stage.order source.stage.meetGraph c e K F)
    (imageC : ZFSet.pair c c' ∈ certificate.transition.map.points)
    (imageE : ZFSet.pair e e' ∈ certificate.transition.map.points)
    (imageK : ZFSet.pair K K' ∈ certificate.transition.map.points) :
    CodedCapProfile certificate.target.stage.carrier certificate.target.stage.order
      certificate.target.stage.meetGraph c' e' K'
      (relationImage F certificate.target.stage.carrier certificate.transition.map.points) := by
  have inherited := certificate.origin.union_input_capProfile
    certificate.compression.born.profiled.heighted.completion.algebra.union
    pairing unions powers separation certificate.indices_ground certificate.sources_ground
    certificate.representatives_ground source.stage.actors_ground certificate.task_action_ground profile
  obtain ⟨points, order, meet, _⟩ := certificate.target_fields
  rw [points, order, meet, certificate.point_graph]
  rw [certificate.point_graph] at imageC imageE imageK
  exact certificate.external.inputs.externalBounded_original_capProfile
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground inherited profile.filter_subset imageC imageE imageK

end GroundInitialMainSuccessorData

end PartitionPilot.Forcing

end OAI
