import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialExternalChronology

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace GroundCompressionBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T base old : ZFSet.{u}}
variable {union : GroundCompressionUnionData M initial I Sources Reps G m one T}

theorem original_entry_iff (births : GroundCompressionBirthData M initial I Sources Reps G m one T union base old)
    {x t : ZFSet.{u}} (hx : x ∈ initial.D) :
    ZFSet.pair x t ∈ births.birth ↔ ZFSet.pair x t ∈ old := by
  have restriction : ZFSet.pair x t ∈ births.birth ↔
      ZFSet.pair x t ∈ graphRestriction initial.D births.birth := by
    rw [pair_mem_graphRestriction]
    exact ⟨fun entry => ⟨entry, hx⟩, And.left⟩
  exact restriction.trans (congrArg (fun f => ZFSet.pair x t ∈ f) births.original).to_iff

end GroundCompressionBirthData

namespace GroundExternalHeightData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi original : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (compressionHeights : GroundCompressionHeightData M initial I Sources Reps G m one T
  completion.algebra.union P0 C D rD original)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi compressionHeights.height completion)

theorem preserves_original {x y z : ZFSet.{u}}
    (image : ZFSet.pair x y ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0) :
    ZFSet.pair y z ∈ heights.height ↔ ZFSet.pair x z ∈ original := by
  obtain ⟨copied, hx⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 x y).1 image
  exact (heights.preserves_seed x y z copied).trans (compressionHeights.original_entries x hx z)

theorem bounded_preserves_original
    (bounded : GroundBoundedExternalHeightData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 C D rD lo hi compressionHeights.height completion heights)
    {x y z : ZFSet.{u}}
    (image : ZFSet.pair x y ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0) :
    ZFSet.pair y z ∈ heights.boundedHeight ↔ ZFSet.pair x z ∈ original := by
  obtain ⟨copied, hx⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 x y).1 image
  exact (bounded.preserves_seed x y z copied).trans (compressionHeights.original_entries x hx z)

end GroundExternalHeightData

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 base old : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (compressionBirths : GroundCompressionBirthData M initial I Sources Reps G m one T
  completion.algebra.union base old)
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 compressionBirths.limit compressionBirths.birth completion)

theorem preserves_original (initialDomain : initial.D = P0) {x y t : ZFSet.{u}}
    (image : ZFSet.pair x y ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0) :
    ZFSet.pair y t ∈ births.birth ↔ ZFSet.pair x t ∈ old := by
  obtain ⟨copied, hx⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 x y).1 image
  rw [← initialDomain] at hx
  exact (births.preserves_seed x y t copied).trans (compressionBirths.original_entry_iff hx)

theorem bounded_preserves_original
    (bounded : GroundBoundedExternalBirthData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 compressionBirths.limit compressionBirths.birth completion births)
    (initialDomain : initial.D = P0) {x y t : ZFSet.{u}}
    (image : ZFSet.pair x y ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0) :
    ZFSet.pair y t ∈ births.boundedBirth ↔ ZFSet.pair x t ∈ old := by
  obtain ⟨copied, hx⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 x y).1 image
  rw [← initialDomain] at hx
  exact (bounded.preserves_seed x y t copied).trans (compressionBirths.original_entry_iff hx)

end GroundExternalBirthData
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (source : GroundMainStage M C D rD)
variable {initial : RecursiveStateData.{u}} {I Sources Reps T Filters lo hi : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps source.actors
  source.multiplication source.identity T source.top}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps source.actors
  source.multiplication source.inverse source.identity T source.top source.carrier source.order
  source.meetGraph source.action completion)
variable (origin : GroundCompressionOrigin M initial source.carrier source.order source.meetGraph source.action
  source.top I Sources Reps source.actors source.multiplication source.inverse source.identity T Filters)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets) (hT : T ∈ M.sets)
variable (initialDomain : initial.D = source.carrier) (initialOrder : initial.rD = source.order)
variable (compressionHeights : GroundCompressionHeightData M initial I Sources Reps source.actors
  source.multiplication source.identity T completion.algebra.union source.carrier C D rD source.height)
variable (heights : GroundExternalHeightData M initial I Sources Reps source.actors source.multiplication
  source.identity T source.top source.carrier source.order source.meetGraph source.action
  C D rD lo hi compressionHeights.height completion)
variable (boundedHeights : GroundBoundedExternalHeightData M initial I Sources Reps source.actors
  source.multiplication source.identity T source.top source.carrier source.order source.meetGraph source.action
  C D rD lo hi compressionHeights.height completion heights)
variable {b' : ZFSet.{u}} (image : ZFSet.pair source.bottom b' ∈
  completion.externalOriginalEmbedding source.carrier source.order source.meetGraph source.action)

noncomputable def externalTransition :
    GroundMainTransition source
      (data.externalMainStage origin source.group_code source.action_code pairing unions powers separation infinite
        hI hSources hReps source.actors_ground hT source.carrier_ground initialDomain initialOrder
        heights boundedHeights source.columns_ground source.coordinates_ground source.coordinate_order_ground
        source.least image) where
  points := completion.externalOriginalEmbedding source.carrier source.order source.meetGraph source.action
  actors := M.externalOldInclusion source.actors
    (externalChildLetters I source.carrier
      (externalRectangles source.carrier source.actors source.order source.meetGraph source.action))
    source.multiplication source.identity
  points_ground := data.externalOriginalEmbedding_mem source.group_code source.action_code
    pairing unions powers separation infinite source.actors_ground source.carrier_ground
  actors_ground := data.old_inclusion_ground
  point_embedding := data.externalOriginalEmbedding_code source.group_code source.action_code
    pairing unions powers separation infinite source.actors_ground source.carrier_ground
  order_iff := fun _ _ _ _ first second => data.externalOriginalEmbedding_order_iff
    source.group_code source.action_code pairing unions powers separation infinite
    source.actors_ground source.carrier_ground first second
  group_embedding := M.externalOldInclusion_groupEmbedding pairing unions powers separation infinite
    source.group_code source.actors_ground data.words.letters_ground
  equivariant := fun _ _ _ _ _ _ actor first second acted => data.externalOriginalEmbedding_equivariant
    source.group_code source.action_code pairing unions powers separation infinite
    source.actors_ground source.carrier_ground actor first second acted
  bottom := image
  height := fun _ _ _ entry => heights.bounded_preserves_original compressionHeights boundedHeights entry
  agreement := fun _ _ _ _ _ _ first second point agree => data.externalOriginalEmbedding_agreement
    source.group_code source.action_code pairing unions powers separation infinite
    source.actors_ground source.carrier_ground first second point agree

theorem externalTransition_graphs :
    let transition := source.externalTransition data origin pairing unions powers separation infinite
      hI hSources hReps hT initialDomain initialOrder compressionHeights heights boundedHeights image
    transition.points = completion.externalOriginalEmbedding source.carrier source.order source.meetGraph source.action ∧
    transition.actors = M.externalOldInclusion source.actors
      (externalChildLetters I source.carrier
        (externalRectangles source.carrier source.actors source.order source.meetGraph source.action))
      source.multiplication source.identity := ⟨rfl, rfl⟩

end PartitionPilot.Forcing.GroundMainStage

end

end OAI
