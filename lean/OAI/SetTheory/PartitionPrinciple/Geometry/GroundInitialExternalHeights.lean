import OAI.SetTheory.PartitionPrinciple.Definability.GroundBoundedExternalBirths

namespace OAI

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
include pairing unions powers separation collection infinite choice

theorem exists_externalColumns {K : ZFSet.{u}} (hK : K ∈ M.sets)
    (subset : K ⊆ C) (small : M.groundEmbeddable K ZFSet.omega) :
    Nonempty (GroundExternalColumnData M C K) := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have omega := M.omega_mem separation infinite
  obtain ⟨base, hBase, above⟩ := M.groundOmegaOne_countable_bound
    pairing unions powers separation collection infinite choice hK subset small
  obtain ⟨sequence, hSequence, _, _, _, stamps⟩ := M.exists_groundCompressionStamps
    pairing unions separation collection infinite (M.transitive spec.1 hBase) ((spec.2.2.1 base).1 hBase).2.1
  have valueMember (n : Nat) : compressionStamp base n ∈ C := by
    induction n with
    | zero => exact M.groundOmegaOne_successor pairing unions powers separation collection infinite hBase
    | succ n ih => exact M.groundOmegaOne_successor pairing unions powers separation collection infinite ih
  have function : ZFSet.IsFunc ZFSet.omega C sequence := by
    refine ⟨?_, stamps.function.2⟩
    intro z hz
    obtain ⟨n, hn, a, _, rfl⟩ := ZFSet.mem_prod.1 (stamps.function.1 hz)
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, (stamps.entries n a).1 hz ▸ valueMember n⟩
  have injection := successorColumnGraph_injection function stamps.entries
  have rangeGround := M.relationImage_mem separation omega spec.1 hSequence
  have inverseGround := M.relationConverse_mem pairing unions powers separation omega spec.1 hSequence
  have rangeSmall : M.groundEmbeddable (relationImage ZFSet.omega C sequence) ZFSet.omega :=
    ⟨relationConverse ZFSet.omega C sequence, inverseGround, injection.converse_image⟩
  obtain ⟨cap, hCap, bounded⟩ := M.groundOmegaOne_countable_bound
    pairing unions powers separation collection infinite choice rangeGround
    (fun _ hz => ((mem_relationImage _ _ _ _).1 hz).1) rangeSmall
  refine ⟨⟨base, sequence, cap, hSequence,
    ⟨function, stamps.entries, hBase, hCap, above, ?_⟩,
    rangeGround, inverseGround, injection.converse_image⟩⟩
  intro n
  exact bounded _ ((mem_relationImage _ _ _ _).2
    ⟨valueMember n, natSetCode n, natSetCode_mem_omega n, (stamps.entries n _).2 rfl⟩)

theorem exists_externalHeightColumns {P D old : ZFSet.{u}}
    (hP : P ∈ M.sets) (hD : D ∈ M.sets) (hOld : old ∈ M.sets)
    (small : M.groundEmbeddable (relationImage P (ZFSet.prod C D) old) ZFSet.omega) :
    Nonempty (GroundExternalColumnData M C (heightColumns P C D old)) := by
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  exact M.exists_externalColumns pairing unions powers separation collection infinite choice
    (M.heightColumns_mem pairing unions powers separation hP hC hD hOld)
    (fun _ hz => ((mem_relationImage _ _ _ _).1 hz).1)
    (M.heightColumns_countable pairing unions powers separation infinite choice hP hC hD hOld small)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 C D rD lo hi original : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
variable (ordinal : ordinalSetProperty C)
variable (heights : GroundCompressionHeightData M initial I Sources Reps G m one T completion.algebra.union P0 C D rD original)
variable (localHeights : GroundExternalLocalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi completion)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "old" => completion.externalSeedHeight P0 r0 μ0 A0 C D heights.height
local notation "V" => M.externalStarVertices G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0))
  (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)) m one
variable (columns : GroundExternalColumnData M C
  (heightColumns (completion.externalSeedCarrier P0 r0 μ0 A0) C D
    (completion.externalSeedHeight P0 r0 μ0 A0 C D heights.height)))
include data group oldAction pairing unions powers separation infinite choice hG hP0 hC hD ordinal heights localHeights columns

theorem externalHeightData_of_families (coordinateSmall : M.groundEmbeddable D ZFSet.omega) :
    Nonempty (GroundExternalHeightData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 C D rD lo hi heights.height completion) := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have seed := data.externalSeedHeights_spec group oldAction pairing unions powers separation infinite hG hP0 heights hC hD
  have owner := data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0
  have depth := data.externalStarDepth_ground_function group oldAction pairing unions powers separation infinite hG
  have vertices := (data.externalStarCarriers_ground pairing unions powers separation hG).1
  have coordGround := data.externalTileCoordinates_ground group oldAction pairing unions powers separation infinite hG localHeights hP0 hD
  have coordPartial := data.externalTileCoordinates_partial group oldAction pairing unions powers separation infinite hG localHeights hP0
  have coordTotal := data.externalTileCoordinates_owner_total group oldAction pairing unions powers separation infinite hG localHeights
  have coordStrict := data.externalTileCoordinates_raw_strict group oldAction pairing unions powers separation infinite hG localHeights
  have seedCode := seed.2.2.1
  have subset : P ⊆ B := fun _ hx => ((mem_relationImage _ _ _ _).1 hx).1
  have heightGround : localHeights.externalHeightGraph C heights.height columns.sequence ∈ M.sets :=
    M.externalOwnerHeightGraph_mem pairing unions powers separation seed.1 geometry.carrier_ground vertices hC hD
      seed.2.1 owner.1 depth.1 columns.sequence_ground coordGround (M.omega_mem separation infinite)
  have strict : StrictLexHeightCode B C D (completion.externalPointOrder P0 r0 μ0 A0)
      (localHeights.externalHeightGraph C heights.height columns.sequence) rD := by
    apply externalOwnerHeightGraph_strictLex subset seedCode owner.2 depth.2 columns.code coordPartial coordTotal
    · intro x hx fresh y hy
      exact data.externalSeedCarrier_no_new_below group oldAction pairing unions powers separation infinite hG hx fresh hy
    · intro x _ _ y _ _ v w n m first second firstDepth secondDepth lower
      exact (data.externalStarOwner_order group oldAction pairing unions powers separation infinite hG
        lower first second firstDepth secondDepth).1
    · intro x _ _ y _ _ v w n first second firstDepth secondDepth lower
      exact (data.externalStarOwner_order group oldAction pairing unions powers separation infinite hG
        lower first second firstDepth secondDepth).2 rfl
    · exact coordStrict
  have rangeSmall := M.externalOwnerHeightGraph_range_small pairing unions powers separation infinite choice
    seed.1 geometry.carrier_ground hC hD seed.2.1 columns.sequence_ground heightGround seedCode.function
    seed.2.2.2.2 ⟨_, columns.inverse_ground, columns.inverse_code⟩ coordinateSmall
  refine ⟨{
    localHeights := localHeights
    columns := columns
    height_ground := heightGround
    code := strict
    range_ground := rangeSmall.1
    range_countable := rangeSmall.2
    preserves_seed := ?_
    below_cap := ?_ }⟩
  · intro x y z copied
    have embedding := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
    have bounds := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 copied)
    have hy : y ∈ P := (mem_relationImage _ _ _ _).2 ⟨bounds.2, x, bounds.1, copied⟩
    exact (externalOwnerHeightGraph_old hy).trans (pushedHeightGraph_entry embedding.injection heights.code.function copied)
  · intro x a d entry
    rcases (pair_mem_externalOwnerHeightGraph _ _ _ _ _ _ _ _ _ _ _ _).1 entry with retained | fresh
    · have below := columns.code.old_below (mem_heightColumns_of_entry seedCode.function retained) 0
      exact ordinal.2 columns.cap columns.code.cap_mem (compressionStamp columns.base 0)
        (columns.code.cap_bound 0) a below
    · obtain ⟨_, _, _, _, n, hn, a', _, d', _, equal, _, _, column, _⟩ := fresh
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
      exact (columns.code.entries n a).1 column ▸ columns.code.cap_bound n

end PartitionPilot.Forcing.GroundExternalGeometryInputs

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 D rD lo hi original c : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (heights : GroundCompressionHeightData M initial I Sources Reps G m one T
  completion.algebra.union P0 (M.groundOmegaOne pairing unions powers separation collection infinite) D rD original)
variable (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
variable (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
variable (hlo : lo ∈ D) (hhi : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD)
include data group oldAction pairing unions powers separation collection infinite choice hG hP0
  heights target injection hD hrD hc hlo hhi gap

theorem exists_externalHeight :
    Nonempty (GroundExternalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0
      (M.groundOmegaOne pairing unions powers separation collection infinite) D rD lo hi
      heights.height completion) := by
  have omegaOne := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  obtain ⟨localHeights⟩ := data.exists_localHeightFamily group oldAction pairing unions powers
    separation collection infinite hG hP0 heights omegaOne.2.1 target.toStrictLinearOrderCode
    omegaOne.1 hD hrD target injection hD hrD hc hlo hhi gap choice
  have seed := data.externalSeedHeights_spec group oldAction pairing unions powers separation infinite
    hG hP0 heights omegaOne.1 hD
  obtain ⟨columns⟩ := M.exists_externalHeightColumns pairing unions powers separation collection infinite
    choice seed.1 hD seed.2.1 seed.2.2.2.2
  exact data.externalHeightData_of_families group oldAction pairing unions powers separation infinite
    choice hG hP0 omegaOne.1 hD omegaOne.2.1 heights localHeights columns ⟨c, hc, injection⟩

end PartitionPilot.Forcing.GroundExternalGeometryInputs

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
theorem exists_groundInitialExternalHeights
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
                compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion heights := by
  have omegaOne := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  obtain ⟨z, originalEntry, _⟩ := originalCode.function.2 τ hτ
  have hz := (ZFSet.pair_mem_prod.1 (originalCode.function.1 originalEntry)).2
  obtain ⟨a, _, lo, hlo, rfl⟩ := ZFSet.mem_prod.1 hz
  obtain ⟨hi, hhi, gap⟩ := above lo hlo
  dsimp only
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data, geometry, bounded⟩ :=
    M.exists_groundInitialExternalBoundedGeometry pairing unions powers separation collection infinite choice
      hP hG hr hμ hA hLabels hm hInv group action meet hτ top omegaOne.1 hD hrD hc hOriginal
      originalCode omegaOne.2.1 target above coordinateInjection originalSmall hBase prior ordinal baseMember
      priorSpace priorOrder priorMeet priorBirth priorHeight
  obtain ⟨heights⟩ := data.exists_externalHeight group action pairing unions powers separation collection infinite choice
    hG hP compression.born.profiled.heighted.heights target coordinateInjection hD hrD hc hlo hhi gap
  exact ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data, geometry, bounded,
    lo, hlo, hi, hhi, gap, heights,
    heights.boundedData pairing unions powers separation infinite geometry omegaOne.1 hD hlo⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
