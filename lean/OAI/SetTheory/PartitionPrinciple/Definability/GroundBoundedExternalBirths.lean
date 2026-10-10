import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFixedTopStep
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundProfiledExternalRequests
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundExternalBirthLayers

namespace OAI

namespace PartitionPilot.Forcing

section
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalBoundedCarrier (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  fixedTopCarrier (completion.externalPointCarrier P r μ A)

noncomputable def externalBoundedOrder (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  fixedTopOrder (completion.externalPointCarrier P r μ A) (completion.externalPointOrder P r μ A)

noncomputable def externalBoundedMeet (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  fixedTopMeet (completion.externalPointCarrier P r μ A) (completion.externalPointOrder P r μ A)

noncomputable def externalBoundedAction (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  fixedTopAction (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.externalPointCarrier P r μ A) (completion.externalPointAction P r μ A)

end GroundCompressionCompletion

structure GroundExternalBoundedGeometryData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P r μ A : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) : Prop where
  carrier_ground : completion.externalBoundedCarrier P r μ A ∈ M.sets
  order_ground : completion.externalBoundedOrder P r μ A ∈ M.sets
  meet_ground : completion.externalBoundedMeet P r μ A ∈ M.sets
  action_ground : completion.externalBoundedAction P r μ A ∈ M.sets
  meet : MeetOrderCode (completion.externalBoundedCarrier P r μ A)
    (completion.externalBoundedOrder P r μ A) (completion.externalBoundedMeet P r μ A)
  action : PosetActionCode
    (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.externalBoundedCarrier P r μ A)
    (M.externalGroupMultiplication G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.externalBoundedOrder P r μ A) (completion.externalBoundedAction P r μ A)
  copies_ground : ∀ w ∈ M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one,
    completion.externalCopyGraph P r μ A w ∈ M.sets
  copies : ∀ w ∈ M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one,
    IdealEmbeddingCode (completion.algebra.union.fields 0) (completion.externalBoundedCarrier P r μ A)
      (completion.algebra.union.fields 1) (completion.externalBoundedOrder P r μ A)
      (completion.algebra.union.fields 2) (completion.externalBoundedMeet P r μ A)
      (completion.externalCopyGraph P r μ A w)
  top_mem : completion.externalPointCarrier P r μ A ∈ completion.externalBoundedCarrier P r μ A
  greatest : ∀ x ∈ completion.externalBoundedCarrier P r μ A,
    ZFSet.pair x (completion.externalPointCarrier P r μ A) ∈ completion.externalBoundedOrder P r μ A
  strict_top : ∀ x ∈ completion.externalPointCarrier P r μ A,
    ZFSet.pair (completion.externalPointCarrier P r μ A) x ∉ completion.externalBoundedOrder P r μ A
  fixes_top : ∀ g ∈ M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one,
    ZFSet.pair (ZFSet.pair g (completion.externalPointCarrier P r μ A))
      (completion.externalPointCarrier P r μ A) ∈ completion.externalBoundedAction P r μ A

end

namespace GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P0 ∈ M.sets)
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "copyGraph" => completion.externalCopyGraph P0 r0 μ0 A0 (M.externalGroupIdentity G letters m one)
include data group oldAction pairing unions powers separation infinite hG hP

theorem externalBoundedGeometryData :
    GroundExternalBoundedGeometryData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 completion := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  exact ⟨M.fixedTopCarrier_mem pairing unions geometry.carrier_ground,
    M.fixedTopOrder_mem pairing unions powers separation geometry.carrier_ground geometry.order_ground,
    M.fixedTopMeet_mem pairing unions powers separation geometry.carrier_ground geometry.order_ground,
    M.fixedTopAction_mem pairing unions powers separation data.group.carrier_mem
      geometry.carrier_ground geometry.action_ground,
    fixedTopMeet_code geometry.meet, geometry.action.fixedTop geometry.meet.order data.group.group_code.identity_mem,
    geometry.copies_ground,
    fun _ hw => (data.externalCopy_ideal group oldAction pairing unions powers separation infinite hG hw).fixedTop geometry.meet,
    fixedTopCarrier_top _, fun _ hx => fixedTopOrder_greatest hx,
    fun _ hx => (fixedTopOrder_strict_top geometry.meet.order hx).2,
    fun _ hg => fixedTopAction_fixes_top hg⟩

theorem externalBoundedCopy_bottom {w b b' : ZFSet.{u}}
    (hw : w ∈ M.externalGroupCarrier G letters m one)
    (least : ∀ x ∈ completion.algebra.union.fields 0, ZFSet.pair b x ∈ completion.algebra.union.fields 1)
    (image : ZFSet.pair b b' ∈ completion.externalCopyGraph P0 r0 μ0 A0 w) :
    ∀ y ∈ completion.externalBoundedCarrier P0 r0 μ0 A0,
      ZFSet.pair b' y ∈ completion.externalBoundedOrder P0 r0 μ0 A0 := by
  have geometry := data.externalBoundedGeometryData group oldAction pairing unions powers separation infinite hG hP
  exact (geometry.copies w hw).preserves_bottom geometry.meet least image

theorem externalBoundedOriginal_agreement {g h g' h' v v' : ZFSet.{u}}
    (firstActor : ZFSet.pair g g' ∈ M.externalOldInclusion G letters m one)
    (secondActor : ZFSet.pair h h' ∈ M.externalOldInclusion G letters m one)
    (hv : v ∈ P0) (image : ZFSet.pair v v' ∈ copyGraph)
    (agree : ActionAgreementBelow P0 r0 A0 g h v) :
    ActionAgreementBelow (completion.externalBoundedCarrier P0 r0 μ0 A0)
      (completion.externalBoundedOrder P0 r0 μ0 A0) (completion.externalBoundedAction P0 r0 μ0 A0) g' h' v' := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have oldAgree := data.externalOriginal_agreement group oldAction pairing unions powers separation infinite hG hP
    firstActor secondActor hv image agree
  have hv' := (ZFSet.pair_mem_prod.1
    ((geometry.copies _ data.group.group_code.identity_mem).injection.function.1 image)).2
  exact oldAgree.fixedTop geometry.meet.order geometry.action hv'

end GroundExternalGeometryInputs

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialExternalBoundedGeometry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ C D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hm : m ∈ M.sets) (hInv : inv ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
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
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data⟩ :=
    M.exists_groundInitialExternalGeometryInputs pairing unions powers separation collection infinite choice
      hP hG hr hμ hA hLabels hm hInv group action meet hτ top hC hD hrD hc hOriginal
      originalCode columns target above coordinateInjection originalSmall hBase prior ordinal baseMember
      priorSpace priorOrder priorMeet priorBirth priorHeight
  exact ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data,
    data.externalGeometryData group action pairing unions powers separation infinite hG hP,
    data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP⟩

end TransitiveGround

namespace GroundProfiledCompression
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 C D rD original Targets Separators Filters : ZFSet.{u}}
variable (profiled : GroundProfiledCompression M initial I Sources Reps G m one T τ P0 C D rD original
  Targets Separators Filters)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0
  profiled.heighted.completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "Q" => profiled.heighted.completion.externalPointCarrier P0 r0 μ0 A0
local notation "identityCopy" => profiled.heighted.completion.externalCopyGraph P0 r0 μ0 A0
  (M.externalGroupIdentity G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one)

local notation "boundedQ" => profiled.heighted.completion.externalBoundedCarrier P0 r0 μ0 A0

include profiled data group oldAction pairing unions powers separation infinite hG in
theorem external_bounded_generator_profile (hP0 : P0 ∈ M.sets) (hFilters : Filters ∈ M.sets)
    (i : SetMembers I) {c v F c' v' τ' : ZFSet.{u}}
    (target : ZFSet.pair (SetMembers.raw i) c ∈ Targets)
    (separator : ZFSet.pair (SetMembers.raw i) v ∈ Separators)
    (filter : ZFSet.pair (SetMembers.raw i) F ∈ Filters)
    (imageC : ZFSet.pair c c' ∈ identityCopy) (imageV : ZFSet.pair v v' ∈ identityCopy)
    (imageTop : ZFSet.pair τ τ' ∈ identityCopy) :
    relationImage F boundedQ identityCopy = relationImage F Q identityCopy ∧
      relationImage F boundedQ identityCopy ∈ M.sets ∧
      ∀ k, ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0)) k ∈
        M.externalChildGenerators G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one →
        ∀ K', ZFSet.pair (ZFSet.pair k τ') K' ∈ profiled.heighted.completion.externalBoundedAction P0 r0 μ0 A0 →
          CodedCapProfile boundedQ (profiled.heighted.completion.externalBoundedOrder P0 r0 μ0 A0)
            (profiled.heighted.completion.externalBoundedMeet P0 r0 μ0 A0)
            c' v' K' (relationImage F boundedQ identityCopy) := by
  let := group.toGroup
  have geometry := data.externalBoundedGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have oldCopy := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have equal : relationImage F boundedQ identityCopy = relationImage F Q identityCopy := by
    apply ZFSet.ext
    intro z
    rw [mem_relationImage, mem_relationImage]
    constructor
    · rintro ⟨_, x, hx, entry⟩
      exact ⟨(ZFSet.pair_mem_prod.1 (oldCopy.injection.function.1 entry)).2, x, hx, entry⟩
    · rintro ⟨hz, witnesses⟩
      exact ⟨fixedTopCarrier_old hz, witnesses⟩
  have hPair := M.transitive hFilters filter
  have hF := M.transitive (M.transitive hPair (ZFSet.mem_pair.2 (Or.inr rfl)))
    (ZFSet.mem_pair.2 (Or.inr rfl))
  refine ⟨equal, M.relationImage_mem separation hF geometry.carrier_ground
    (geometry.copies_ground _ data.group.group_code.identity_mem), ?_⟩
  intro k gen K' acted
  have hTop := (ZFSet.pair_mem_prod.1 (oldCopy.injection.function.1 imageTop)).2
  have oldAct := (fixedTopAction_old_iff hTop).1 acted
  have topEq := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG
    (SetMembers.ofMem τ profiled.heighted.completion.top_mem) τ').1
      (by simpa only [SetMembers.raw_ofMem] using imageTop)
  rw [topEq] at oldAct
  have value := (data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inl i) ⟨()⟩ k gen _ K').1 oldAct
  rw [profiled.heighted.completion.external_compression_top group oldAction data.original] at value
  have capEntry := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG
    (profiled.heighted.completion.externalCap i) K').2 value
  have profile := profiled.profiles (SetMembers.raw i) c v
    (SetMembers.raw (profiled.heighted.completion.externalCap i)) F
    (profiled.heighted.completion.externalCap_entry i) target separator filter
  exact (geometry.copies _ data.group.group_code.identity_mem).capProfile
    profiled.heighted.completion.algebra.union.meet geometry.meet
    profiled.heighted.completion.top_mem profiled.heighted.completion.top profile imageC imageV capEntry

end GroundProfiledCompression

open SetFormula
universe u
namespace GroundExternalHeightData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)

noncomputable def boundedHeight : ZFSet.{u} :=
  fixedTopHeightGraph (completion.externalPointCarrier P0 r0 μ0 A0) heights.height heights.columns.cap lo

theorem attained_columns_below : ∀ a ∈ heightColumns (completion.externalPointCarrier P0 r0 μ0 A0) C D heights.height,
    a ∈ heights.columns.cap := by
  intro a ha
  obtain ⟨_, value, member, projection⟩ := (mem_relationImage _ _ _ _).1 ha
  obtain ⟨b, _, q, _, equal⟩ := (mem_productFirst C D _).1 projection
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  obtain ⟨_, x, _, entry⟩ := (mem_relationImage _ _ _ _).1 member
  exact heights.below_cap x a q entry

end GroundExternalHeightData

structure GroundBoundedExternalHeightData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
    (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed completion) : Prop where
  height_ground : heights.boundedHeight ∈ M.sets
  code : StrictLexHeightCode (completion.externalBoundedCarrier P0 r0 μ0 A0) C D
    (completion.externalBoundedOrder P0 r0 μ0 A0) heights.boundedHeight rD
  old_entries : ∀ x ∈ completion.externalPointCarrier P0 r0 μ0 A0, ∀ y,
    ZFSet.pair x y ∈ heights.boundedHeight ↔ ZFSet.pair x y ∈ heights.height
  top_entries : ∀ y, ZFSet.pair (completion.externalPointCarrier P0 r0 μ0 A0) y ∈ heights.boundedHeight ↔
    y = ZFSet.pair heights.columns.cap lo
  range_eq : relationImage (completion.externalBoundedCarrier P0 r0 μ0 A0) (ZFSet.prod C D) heights.boundedHeight =
    insert (ZFSet.pair heights.columns.cap lo)
      (relationImage (completion.externalPointCarrier P0 r0 μ0 A0) (ZFSet.prod C D) heights.height)
  range_ground : relationImage (completion.externalBoundedCarrier P0 r0 μ0 A0) (ZFSet.prod C D) heights.boundedHeight ∈ M.sets
  range_countable : M.groundEmbeddable
    (relationImage (completion.externalBoundedCarrier P0 r0 μ0 A0) (ZFSet.prod C D) heights.boundedHeight) ZFSet.omega
  preserves_seed : ∀ x y z, ZFSet.pair x y ∈ completion.externalIdentityCopyGraph P0 r0 μ0 A0 →
    (ZFSet.pair y z ∈ heights.boundedHeight ↔ ZFSet.pair x z ∈ seed)
  weak_bound : ∀ x y, ZFSet.pair x y ∈ heights.boundedHeight →
    y = ZFSet.pair heights.columns.cap lo ∨ ZFSet.pair y (ZFSet.pair heights.columns.cap lo) ∈ lexHeightOrder C D rD

namespace GroundExternalHeightData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)

theorem boundedData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (geometry : GroundExternalGeometryData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 completion)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hlo : lo ∈ D) :
    GroundBoundedExternalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed completion heights := by
  have hCap := M.transitive hC heights.columns.code.cap_mem
  have hLo := M.transitive hD hlo
  have capPoint := M.orderedPair_mem pairing hCap hLo
  have range : relationImage (completion.externalBoundedCarrier P0 r0 μ0 A0) (ZFSet.prod C D) heights.boundedHeight =
      insert (ZFSet.pair heights.columns.cap lo)
        (relationImage (completion.externalPointCarrier P0 r0 μ0 A0) (ZFSet.prod C D) heights.height) :=
    fixedTopHeightGraph_range heights.code.function heights.columns.code.cap_mem hlo
  refine ⟨M.fixedTopHeightGraph_mem pairing unions geometry.carrier_ground heights.height_ground hCap hLo,
    fixedTopHeightGraph_strict heights.code geometry.meet.order heights.columns.code.cap_mem hlo heights.attained_columns_below,
    fun _ hx _ => fixedTopHeightGraph_old_iff hx,
    fun _ => fixedTopHeightGraph_top_iff heights.code.function,
    range, ?_, ?_, ?_, ?_⟩
  · rw [range]
    exact M.insert_mem pairing unions capPoint heights.range_ground
  · rw [range]
    exact M.groundEmbeddable_insert pairing unions powers separation infinite heights.range_ground capPoint heights.range_countable
  · intro x y z copied
    have raw := copied
    dsimp only [GroundCompressionCompletion.externalIdentityCopyGraph,
      GroundCompressionCompletion.externalCopyGraph, flatCopyEmbeddingGraph] at raw
    have hy : y ∈ completion.externalPointCarrier P0 r0 μ0 A0 :=
      (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 raw).1).2
    exact (fixedTopHeightGraph_old_iff hy).trans (heights.preserves_seed x y z copied)
  · intro x y entry
    exact fixedTopHeightGraph_bound heights.code.function heights.columns.code.cap_mem hlo heights.attained_columns_below entry

end GroundExternalHeightData

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)

noncomputable def boundedBirth : ZFSet.{u} :=
  fixedTopBirth (completion.externalPointCarrier P0 r0 μ0 A0) births.birth births.limit

end GroundExternalBirthData

structure GroundBoundedExternalBirthData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
    (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 oldTimes oldBirth completion) : Prop where
  times_ground : insert births.limit births.limit ∈ M.sets
  birth_ground : births.boundedBirth ∈ M.sets
  function : ZFSet.IsFunc (completion.externalBoundedCarrier P0 r0 μ0 A0)
    (insert births.limit births.limit) births.boundedBirth
  old_meet : OldMeetCode (completion.externalBoundedOrder P0 r0 μ0 A0)
    (completion.externalBoundedMeet P0 r0 μ0 A0) births.boundedBirth
  old_entries : ∀ x ∈ completion.externalPointCarrier P0 r0 μ0 A0, ∀ t,
    ZFSet.pair x t ∈ births.boundedBirth ↔ ZFSet.pair x t ∈ births.birth
  top_entries : ∀ t, ZFSet.pair (completion.externalPointCarrier P0 r0 μ0 A0) t ∈ births.boundedBirth ↔
    t = births.limit
  new_fiber : ∀ x, ZFSet.pair x births.limit ∈ births.boundedBirth ↔
    x = completion.externalPointCarrier P0 r0 μ0 A0
  birth_bound : ∀ x t, ZFSet.pair x t ∈ births.boundedBirth → t ∈ births.limit ∨ t = births.limit
  preserves_seed : ∀ x y t, ZFSet.pair x y ∈ completion.externalIdentityCopyGraph P0 r0 μ0 A0 →
    (ZFSet.pair y t ∈ births.boundedBirth ↔ ZFSet.pair x t ∈ oldBirth)
  new_fiber_ground : ({completion.externalPointCarrier P0 r0 μ0 A0} : ZFSet.{u}) ∈ M.sets
  new_fiber_countable : M.groundEmbeddable {completion.externalPointCarrier P0 r0 μ0 A0} ZFSet.omega

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)

theorem boundedData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (geometry : GroundExternalGeometryData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 completion) :
    GroundBoundedExternalBirthData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 oldTimes oldBirth completion births := by
  have earlier : ∀ x t, ZFSet.pair x t ∈ births.birth → t ∈ births.limit :=
    fun _ _ entry => (ZFSet.pair_mem_prod.1 (births.function.1 entry)).2
  have retarget := isFunc_retarget_of_entries (C := insert births.limit births.limit) births.function
    (fun x t entry => ZFSet.mem_insert_iff.2 (Or.inr (earlier x t entry)))
  have single := M.fixedTopBirth_singleton_small pairing geometry.carrier_ground
  refine ⟨M.insert_mem pairing unions births.limit_ground births.limit_ground,
    M.fixedTopBirth_mem pairing unions geometry.carrier_ground births.birth_ground births.limit_ground,
    fixedTopBirth_function retarget (ZFSet.mem_insert_iff.2 (Or.inl rfl)),
    fixedTopBirth_oldMeet geometry.meet births.function earlier births.old_meet,
    fun _ hx _ => fixedTopBirth_old_iff hx, fun _ => fixedTopBirth_top_iff births.function,
    fun _ => fixedTopBirth_new_time_iff earlier,
    fun x t entry => (fixedTopBirth_bound earlier x t entry).symm, ?_, single.1, single.2⟩
  intro x y t copied
  have raw := copied
  dsimp only [GroundCompressionCompletion.externalIdentityCopyGraph,
    GroundCompressionCompletion.externalCopyGraph, flatCopyEmbeddingGraph] at raw
  have hy : y ∈ completion.externalPointCarrier P0 r0 μ0 A0 :=
    (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 raw).1).2
  exact (fixedTopBirth_old_iff hy).trans (births.preserves_seed x y t copied)

noncomputable def bounded_incoming_layer
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (geometry : GroundExternalGeometryData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 completion)
    (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (completion.externalBoundedCarrier P0 r0 μ0 A0)
      (completion.externalBoundedOrder P0 r0 μ0 A0) (completion.externalBoundedMeet P0 r0 μ0 A0)
      births.boundedBirth births.limit :=
  M.fixedTopBirth_incoming_layer pairing geometry.carrier_ground
    (fun _ _ entry => (ZFSet.pair_mem_prod.1 (births.function.1 entry)).2)

end GroundExternalBirthData

end PartitionPilot.Forcing

end OAI
