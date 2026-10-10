import OAI.SetTheory.PartitionPrinciple.Geometry.GroundInitialExternalHeights

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "C" => M.groundOmegaOne pairing unions powers separation collection infinite

include choice in
theorem exists_groundInitialExternalBirths
    {P G r μ A Labels m inv one τ D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hm : m ∈ M.sets) (hInv : inv ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
    (hBase : base ∈ M.sets) (prior : GroundChronologicalHistory M T0 C D rD)
    (ordinal : ordinalSetProperty T0) (baseMember : base ∈ T0)
    (priorSpace : prior.space base = P) (priorOrder : prior.order base = r)
    (priorMeet : prior.meetGraph base = μ) (priorBirth : prior.birth base = old)
    (priorHeight : prior.height base = original) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ _origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
          P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ compression : GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior,
          GroundExternalGeometryInputs M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m inv one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalBoundedGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
          ∃ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD ∧
            ∃ heights : GroundExternalHeightData M (M.initialCompressionData P G r μ A Labels)
              I Sources Reps G m one T τ P r μ A C D rD lo hi
              compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion,
              GroundBoundedExternalHeightData M (M.initialCompressionData P G r μ A Labels)
                I Sources Reps G m one T τ P r μ A C D rD lo hi
                compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion heights ∧
              ∃ births : GroundExternalBirthData M (M.initialCompressionData P G r μ A Labels)
                I Sources Reps G m one T τ P r μ A compression.born.births.limit compression.born.births.birth
                compression.born.profiled.heighted.completion,
                GroundBoundedExternalBirthData M (M.initialCompressionData P G r μ A Labels)
                  I Sources Reps G m one T τ P r μ A compression.born.births.limit compression.born.births.birth
                  compression.born.profiled.heighted.completion births := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data, geometry,
      boundedGeometry, lo, hlo, hi, hhi, gap, heights, boundedHeights⟩ :=
    M.exists_groundInitialExternalHeights pairing unions powers separation collection infinite choice
      hP hG hr hμ hA hLabels hm hInv group action meet hτ top hD hrD hc hOriginal
      originalCode target above coordinateInjection originalSmall hBase prior ordinal baseMember
      priorSpace priorOrder priorMeet priorBirth priorHeight
  obtain ⟨births⟩ := data.exists_externalBirths group action pairing unions powers separation collection infinite
    hG hP compression.born.births
  exact ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data, geometry,
    boundedGeometry, lo, hlo, hi, hhi, gap, heights, boundedHeights, births,
    births.boundedData pairing unions geometry⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
