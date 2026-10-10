import OAI.SetTheory.PartitionPrinciple.Definability.TaskCapFamilyCodes
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundIdentityInsertionTasks
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainSuccessorProfilePreservation

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def boundedCapImages (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose I (completion.algebra.union.fields 0) (completion.externalBoundedCarrier P r μ A)
    (completion.algebra.caps τ) (completion.externalCopyGraph P r μ A
      (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one))

end GroundCompressionCompletion

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
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalBoundedCarrier P r μ A
local notation "copyGraph" => completion.externalCopyGraph P r μ A
  (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one)

theorem boundedCapImages_ground (hI : I ∈ M.sets) :
    completion.boundedCapImages P r μ A ∈ M.sets := by
  have geometry := data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP
  exact M.relationCompose_mem pairing unions powers separation hI (completion.algebra.union.ground 0)
    geometry.carrier_ground completion.caps_ground
    (geometry.copies_ground _ data.group.group_code.identity_mem)

theorem boundedCapImages_function :
    ZFSet.IsFunc I Q (completion.boundedCapImages P r μ A) := by
  have geometry := data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP
  exact relationCompose_function_of_subset completion.caps_function
    (geometry.copies _ data.group.group_code.identity_mem).injection.function (fun _ h => h)

theorem boundedCapImages_entry_iff {i k' : ZFSet.{u}} :
    ZFSet.pair i k' ∈ completion.boundedCapImages P r μ A ↔
      ∃ k, ZFSet.pair i k ∈ completion.algebra.caps τ ∧ ZFSet.pair k k' ∈ copyGraph := by
  have geometry := data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP
  rw [GroundCompressionCompletion.boundedCapImages, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, k, _, cap, image⟩
    exact ⟨k, cap, image⟩
  · rintro ⟨k, cap, image⟩
    have bounds := ZFSet.pair_mem_prod.1 (completion.caps_function.1 cap)
    have target := ZFSet.pair_mem_prod.1
      ((geometry.copies _ data.group.group_code.identity_mem).injection.function.1 image)
    exact ⟨bounds.1, target.2, k, bounds.2, cap, image⟩

end GroundExternalGeometryInputs
end

namespace GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P m one r A)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P ∈ M.sets)
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P r μ A
local notation "letters" => externalChildLetters I P (externalRectangles P G r μ A)
local notation "generators" => M.externalChildGenerators G letters m one
local notation "oldActors" => M.externalOldInclusion G letters m one
local notation "copyGraph" => completion.externalCopyGraph P r μ A (M.externalGroupIdentity G letters m one)
local notation "e" => completion.externalOriginalEmbedding P r μ A
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "root" => Compression.RecursiveMaps.TileRequests.Family.copy
  (completion.externalFamily group oldAction data.original)
  (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet) 1
local notation "newAction" => completion.externalPointAction P r μ A
local notation "newOrder" => completion.externalPointOrder P r μ A
include data group oldAction pairing unions powers separation infinite hG hP

theorem bounded_compression_generator_agreement (i : SetMembers I) {a g k g' a' : ZFSet.{u}}
    (source : ZFSet.pair (SetMembers.raw i) a ∈ Sources)
    (representative : ZFSet.pair (SetMembers.raw i) g ∈ Reps)
    (generator : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0)) k ∈ generators)
    (actor : ZFSet.pair g g' ∈ oldActors) (image : ZFSet.pair a a' ∈ e) :
    ActionAgreementBelow (completion.externalBoundedCarrier P r μ A)
      (completion.externalBoundedOrder P r μ A) (completion.externalBoundedAction P r μ A) k g' a' := by
  let := group.toGroup
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have ideal := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have imageA := ((completion.externalOriginalEmbedding_entry_iff P r μ A a a').1 image).1
  have ha' := (ZFSet.pair_mem_prod.1 (ideal.injection.function.1 imageA)).2
  have hg := (ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 actor)).1
  have agree : ActionAgreementBelow Q newOrder newAction k g' a' := by
    intro x' hx' z _ lower
    obtain ⟨x, hx, below, imageX⟩ := ideal.ideal _ _ _ imageA hx' lower
    obtain ⟨y, acted, _⟩ := completion.algebra.union.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨hg, hx⟩)
    have hy := (ZFSet.pair_mem_prod.1 (completion.algebra.union.action.function.1 acted)).2
    let xu := SetMembers.ofMem x hx
    let yu := SetMembers.ofMem y hy
    have eqX := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG xu x').1
      (by simpa only [xu, SetMembers.raw_ofMem] using imageX)
    have imageY := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG yu
      ((q).encode ((root).toFun yu))).2 rfl
    have first := data.compression_generator_agreement group oldAction pairing unions powers separation infinite hG
      i source representative xu yu
      (by simpa only [xu, SetMembers.raw_ofMem] using below)
      (by simpa only [xu, yu, SetMembers.raw_ofMem] using acted) k generator
    rw [← eqX] at first
    have second := data.externalIdentityCopy_equivariant group oldAction pairing unions powers separation infinite hG
      actor imageX imageY (by simpa only [yu, SetMembers.raw_ofMem] using acted)
    have function : FunctionGraphOn (ZFSet.prod (M.externalGroupCarrier G letters m one) Q) newAction :=
      ⟨Q, geometry.action.function⟩
    exact ⟨fun entry => (function.unique entry first).symm ▸ second,
      fun entry => (function.unique entry second).symm ▸ first⟩
  exact agree.fixedTop geometry.meet.order geometry.action ha'

theorem bounded_compression_generator_top_iff (i : SetMembers I) {k τ' v : ZFSet.{u}}
    (generator : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0)) k ∈ generators)
    (imageTop : ZFSet.pair τ τ' ∈ e) :
    ZFSet.pair (ZFSet.pair k τ') v ∈ completion.externalBoundedAction P r μ A ↔
      ZFSet.pair (SetMembers.raw i) v ∈ completion.boundedCapImages P r μ A := by
  let := group.toGroup
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have ideal := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have copiedTop := ((completion.externalOriginalEmbedding_entry_iff P r μ A τ τ').1 imageTop).1
  have hτ' := (ZFSet.pair_mem_prod.1 (ideal.injection.function.1 copiedTop)).2
  have eqTop := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG
    (SetMembers.ofMem τ completion.top_mem) τ').1
      (by simpa only [SetMembers.raw_ofMem] using copiedTop)
  have canonical := data.compression_generator_top group oldAction pairing unions powers separation infinite hG i k generator
  rw [← eqTop] at canonical
  have imageCap := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG
    (completion.externalCap i) _).2 rfl
  have cap := (data.boundedCapImages_entry_iff group oldAction pairing unions powers separation infinite hG hP).2
    ⟨_, completion.externalCap_entry i, imageCap⟩
  have actionFunction : FunctionGraphOn (ZFSet.prod (M.externalGroupCarrier G letters m one) Q) newAction :=
    ⟨Q, geometry.action.function⟩
  have capFunction : FunctionGraphOn I (completion.boundedCapImages P r μ A) :=
    ⟨_, data.boundedCapImages_function group oldAction pairing unions powers separation infinite hG hP⟩
  change ZFSet.pair (ZFSet.pair k τ') v ∈ fixedTopAction (M.externalGroupCarrier G letters m one) Q newAction ↔ _
  rw [fixedTopAction_old_iff hτ']
  exact ⟨fun entry => (actionFunction.unique entry canonical).symm ▸ cap,
    fun entry => (capFunction.unique entry cap).symm ▸ canonical⟩

end GroundExternalGeometryInputs

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

noncomputable def compressionCapImages : ZFSet.{u} :=
  certificate.compression.born.profiled.heighted.completion.boundedCapImages
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
include pairing unions powers separation infinite

theorem compressionCapImages_ground : certificate.compressionCapImages ∈ M.sets :=
  certificate.external.inputs.boundedCapImages_ground source.stage.group_code source.stage.action_code
    pairing unions powers separation infinite source.stage.actors_ground source.stage.carrier_ground
    certificate.indices_ground

theorem compressionCapImages_function :
    ZFSet.IsFunc (source.stage.compressionTasks Labels) certificate.target.stage.carrier
      certificate.compressionCapImages := by
  rw [certificate.target_fields.1]
  exact certificate.external.inputs.boundedCapImages_function source.stage.group_code source.stage.action_code
    pairing unions powers separation infinite source.stage.actors_ground source.stage.carrier_ground

theorem compressionCapImages_profile {i c v F K' c' v' : ZFSet.{u}}
    (cap : ZFSet.pair i K' ∈ certificate.compressionCapImages)
    (target : ZFSet.pair i c ∈ source.stage.compressionTargets Labels)
    (separator : ZFSet.pair i v ∈ source.stage.compressionSeparators Labels)
    (filter : ZFSet.pair i F ∈ source.stage.compressionFilters Labels)
    (imageC : ZFSet.pair c c' ∈ certificate.transition.map.points)
    (imageV : ZFSet.pair v v' ∈ certificate.transition.map.points) :
    CodedCapProfile certificate.target.stage.carrier certificate.target.stage.order
      certificate.target.stage.meetGraph c' v' K'
      (relationImage F certificate.target.stage.carrier certificate.transition.map.points) := by
  let completion := certificate.compression.born.profiled.heighted.completion
  have geometry := certificate.external.inputs.externalBoundedGeometryData
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground
  obtain ⟨K, oldCap, capCopy⟩ := (certificate.external.inputs.boundedCapImages_entry_iff
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground).1 cap
  have profile := certificate.compression.born.profiled.profiles i c v K F oldCap target separator filter
  have filterBound := (ZFSet.mem_sep.1 (show ZFSet.pair i F ∈ literalTaskFieldGraph
    (source.stage.compressionTasks Labels) source.stage.carrier
    (M.groundRelations source.stage.carrier source.stage.carrier)
    (M.groundMeetFilters source.stage.carrier source.stage.order source.stage.meetGraph) Labels 4 from filter)).1
  have hF : F ∈ M.groundMeetFilters source.stage.carrier source.stage.order source.stage.meetGraph :=
    (ZFSet.pair_mem_prod.1 filterBound).2
  have subset := ((M.mem_groundMeetFilters _ _ _ F).1 hF).2.subset
  obtain ⟨carrierEq, orderEq, meetEq, _⟩ := certificate.target_fields
  rw [carrierEq, orderEq, meetEq, certificate.point_graph]
  rw [certificate.point_graph] at imageC imageV
  rw [completion.externalOriginal_filterImage_eq source.stage.carrier source.stage.order
    source.stage.meetGraph source.stage.action _ subset]
  exact (geometry.copies _ certificate.external.inputs.group.group_code.identity_mem).capProfile
    completion.algebra.union.meet geometry.meet completion.top_mem completion.top profile
    ((completion.externalOriginalEmbedding_entry_iff _ _ _ _ c c').1 imageC).1
    ((completion.externalOriginalEmbedding_entry_iff _ _ _ _ v v').1 imageV).1 capCopy

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

theorem compressionCapImages_common_target_meet
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hLabels : Labels ∈ M.sets)
    {i j c K' L' c' : ZFSet.{u}}
    (capI : ZFSet.pair i K' ∈ certificate.compressionCapImages)
    (capJ : ZFSet.pair j L' ∈ certificate.compressionCapImages)
    (targetI : ZFSet.pair i c ∈ source.stage.compressionTargets Labels)
    (targetJ : ZFSet.pair j c ∈ source.stage.compressionTargets Labels)
    (different : i ≠ j) (imageC : ZFSet.pair c c' ∈ certificate.transition.map.points) :
    ZFSet.pair (ZFSet.pair K' L') c' ∈ certificate.target.stage.meetGraph := by
  let completion := certificate.compression.born.profiled.heighted.completion
  have geometry := certificate.external.inputs.externalBoundedGeometryData
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground
  obtain ⟨K, oldI, copyI⟩ := (certificate.external.inputs.boundedCapImages_entry_iff
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground).1 capI
  obtain ⟨L, oldJ, copyJ⟩ := (certificate.external.inputs.boundedCapImages_entry_iff
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground).1 capJ
  have hi := (ZFSet.pair_mem_prod.1 (completion.caps_function.1 oldI)).1
  have hj := (ZFSet.pair_mem_prod.1 (completion.caps_function.1 oldJ)).1
  obtain ⟨_, _, _, _, fields⟩ := M.groundEligibleTaskFields pairing unions powers separation
    source.stage.carrier_ground source.stage.actors_ground source.stage.order_ground
    source.stage.meet_ground source.stage.action_ground hLabels source.stage.meet
  obtain ⟨v, sepI, _⟩ := (fields 3).2.2 i hi
  obtain ⟨w, sepJ, _⟩ := (fields 3).2.2 j hj
  obtain ⟨F, filterI, _⟩ := (fields 4).2.2 i hi
  obtain ⟨H, filterJ, _⟩ := (fields 4).2.2 j hj
  have first := certificate.compression.born.profiled.profiles i c v K F oldI targetI sepI filterI
  have second := certificate.compression.born.profiled.profiles j c w L H oldJ targetJ sepJ filterJ
  have inherited := certificate.origin.union_caps_common_target_meet completion.algebra
    pairing unions powers separation source.stage.carrier_ground source.stage.actors_ground
    source.stage.order_ground source.stage.meet_ground source.stage.action_ground hLabels
    rfl rfl oldI oldJ targetI targetJ different first.cap_not_below_target second.cap_not_below_target
  rw [certificate.point_graph] at imageC
  rw [certificate.target_fields.2.2.1]
  exact (geometry.copies _ certificate.external.inputs.group.group_code.identity_mem).map_meet
    K L c K' L' c' inherited copyI copyJ
    ((completion.externalOriginalEmbedding_entry_iff _ _ _ _ c c').1 imageC).1

local notation "P" => source.stage.carrier
local notation "r" => source.stage.order
local notation "I" => source.stage.compressionTasks Labels
local notation "Q" => certificate.target.stage.carrier

noncomputable def insertionCapImages (c e F : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose Labels I Q (identityInsertionTaskGraph Labels I P r c e F)
    certificate.compressionCapImages

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
include pairing unions powers separation infinite

theorem insertionCapImages_ground {c e F : ZFSet.{u}} (hLabels : Labels ∈ M.sets)
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets) :
    certificate.insertionCapImages c e F ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation hLabels certificate.indices_ground
    certificate.target.stage.carrier_ground
    (M.identityInsertionTaskGraph_mem pairing unions powers separation hLabels certificate.indices_ground
      source.stage.carrier_ground source.stage.order_ground hc he hF)
    (certificate.compressionCapImages_ground pairing unions powers separation infinite)

theorem insertionCapImages_entry_iff {c e F label K : ZFSet.{u}} :
    ZFSet.pair label K ∈ certificate.insertionCapImages c e F ↔
      label ∈ Labels ∧ ZFSet.pair (identityInsertionTask P r c e F label) K ∈ certificate.compressionCapImages := by
  rw [insertionCapImages, pair_mem_relationCompose]
  constructor
  · rintro ⟨hlabel, _, task, _, entry, cap⟩
    have equal := ((pair_mem_identityInsertionTaskGraph Labels I P r c e F label task).1 entry).2.2
    exact ⟨hlabel, equal ▸ cap⟩
  · rintro ⟨hlabel, cap⟩
    have bounds := ZFSet.pair_mem_prod.1
      ((certificate.compressionCapImages_function pairing unions powers separation infinite).1 cap)
    exact ⟨hlabel, bounds.2, _, bounds.1,
      (pair_mem_identityInsertionTaskGraph Labels I P r c e F _ _).2 ⟨hlabel, bounds.1, rfl⟩, cap⟩

variable {c e F : ZFSet.{u}}

theorem insertionCapImages_function
    (hc : c ∈ source.stage.carrier) (he : e ∈ source.stage.carrier) (hF : F ∈ M.sets)
    (filter : MeetFilterCode source.stage.carrier source.stage.order source.stage.meetGraph F)
    (lower : ZFSet.pair c e ∈ source.stage.order) (strict : ZFSet.pair e c ∉ source.stage.order)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ source.stage.order) :
    ZFSet.IsFunc Labels Q (certificate.insertionCapImages c e F) := by
  have tasks := M.identityInsertionTaskGraph_injection pairing unions powers separation (Labels := Labels)
    source.stage.carrier_ground source.stage.order_ground hF source.stage.action_code
    source.stage.group_code.identity_mem hc he filter lower strict above
  exact relationCompose_function_of_subset tasks.function
    (certificate.compressionCapImages_function pairing unions powers separation infinite) (fun _ h => h)

theorem insertionCapImages_profile
    (hc : c ∈ source.stage.carrier) (he : e ∈ source.stage.carrier) (hF : F ∈ M.sets)
    (filter : MeetFilterCode source.stage.carrier source.stage.order source.stage.meetGraph F)
    (lower : ZFSet.pair c e ∈ source.stage.order) (strict : ZFSet.pair e c ∉ source.stage.order)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ source.stage.order) {label K c' e' : ZFSet.{u}}
    (cap : ZFSet.pair label K ∈ certificate.insertionCapImages c e F)
    (imageC : ZFSet.pair c c' ∈ certificate.transition.map.points)
    (imageE : ZFSet.pair e e' ∈ certificate.transition.map.points) :
    CodedCapProfile Q certificate.target.stage.order certificate.target.stage.meetGraph c' e' K
      (relationImage F Q certificate.transition.map.points) := by
  obtain ⟨hlabel, entry⟩ := (certificate.insertionCapImages_entry_iff
    pairing unions powers separation infinite).1 cap
  have fields := M.identityInsertionTask_fields pairing unions powers separation
    source.stage.carrier_ground source.stage.order_ground hF source.stage.action_code
    source.stage.group_code.identity_mem hc he filter lower strict above hlabel
  exact certificate.compressionCapImages_profile pairing unions powers separation infinite entry
    (fields 1) (fields 3) (fields 4) imageC imageE

theorem insertionCapImages_meet
    (hc : c ∈ source.stage.carrier) (he : e ∈ source.stage.carrier) (hF : F ∈ M.sets)
    (filter : MeetFilterCode source.stage.carrier source.stage.order source.stage.meetGraph F)
    (lower : ZFSet.pair c e ∈ source.stage.order) (strict : ZFSet.pair e c ∉ source.stage.order)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ source.stage.order) (hLabels : Labels ∈ M.sets) {first second K L c' : ZFSet.{u}}
    (firstCap : ZFSet.pair first K ∈ certificate.insertionCapImages c e F)
    (secondCap : ZFSet.pair second L ∈ certificate.insertionCapImages c e F)
    (different : first ≠ second) (imageC : ZFSet.pair c c' ∈ certificate.transition.map.points) :
    ZFSet.pair (ZFSet.pair K L) c' ∈ certificate.target.stage.meetGraph := by
  obtain ⟨hfirst, firstEntry⟩ := (certificate.insertionCapImages_entry_iff
    pairing unions powers separation infinite).1 firstCap
  obtain ⟨hsecond, secondEntry⟩ := (certificate.insertionCapImages_entry_iff
    pairing unions powers separation infinite).1 secondCap
  have fieldsFirst := M.identityInsertionTask_fields pairing unions powers separation
    source.stage.carrier_ground source.stage.order_ground hF source.stage.action_code
    source.stage.group_code.identity_mem hc he filter lower strict above hfirst
  have fieldsSecond := M.identityInsertionTask_fields pairing unions powers separation
    source.stage.carrier_ground source.stage.order_ground hF source.stage.action_code
    source.stage.group_code.identity_mem hc he filter lower strict above hsecond
  exact certificate.compressionCapImages_common_target_meet pairing unions powers separation infinite hLabels
    firstEntry secondEntry (fieldsFirst 1) (fieldsSecond 1)
    (fun equal => different (identityInsertionTask_injective P r c e F equal)) imageC

theorem insertionCapImages_injection
    (hc : c ∈ source.stage.carrier) (he : e ∈ source.stage.carrier) (hF : F ∈ M.sets)
    (filter : MeetFilterCode source.stage.carrier source.stage.order source.stage.meetGraph F)
    (lower : ZFSet.pair c e ∈ source.stage.order) (strict : ZFSet.pair e c ∉ source.stage.order)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ source.stage.order) (hLabels : Labels ∈ M.sets) :
    InjectionCode Labels Q (certificate.insertionCapImages c e F) := by
  refine ⟨certificate.insertionCapImages_function pairing unions powers separation infinite
    hc he hF filter lower strict above, ?_⟩
  intro first second K firstCap secondCap
  by_cases equal : first = second
  · exact equal
  · obtain ⟨c', imageC, _⟩ := certificate.transition.map.point_embedding.injection.function.2 c hc
    obtain ⟨e', imageE, _⟩ := certificate.transition.map.point_embedding.injection.function.2 e he
    have profile := certificate.insertionCapImages_profile pairing unions powers separation infinite
      hc he hF filter lower strict above firstCap imageC imageE
    have meet := certificate.insertionCapImages_meet pairing unions powers separation infinite
      hc he hF filter lower strict above hLabels firstCap secondCap equal imageC
    exact (profile.cap_not_below_target
      (certificate.target.stage.meet.greatest K K c' K profile.cap_mem meet
        (certificate.target.stage.meet.order.refl K profile.cap_mem)
        (certificate.target.stage.meet.order.refl K profile.cap_mem))).elim

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

noncomputable def taskCapValues : Fin 11 → ZFSet.{u} :=
  Fin.cases (source.stage.compressionTasks Labels) (Fin.cases source.stage.carrier
    (Fin.cases certificate.target.stage.carrier (Fin.cases certificate.target.stage.order
      (Fin.cases certificate.target.stage.meetGraph (Fin.cases certificate.transition.map.points
        (Fin.cases (source.stage.compressionTargets Labels)
          (Fin.cases (source.stage.compressionSeparators Labels)
            (Fin.cases (source.stage.compressionFilters Labels)
              (Fin.cases (M.groundPower source.stage.carrier)
                (fun _ => certificate.compressionCapImages))))))))))

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hLabels : Labels ∈ M.sets)
include pairing unions powers separation infinite hLabels

theorem taskCapValues_ground : ∀ j, certificate.taskCapValues j ∈ M.sets := by
  obtain ⟨_, _, _, _, fields⟩ := M.groundEligibleTaskFields pairing unions powers separation
    source.stage.carrier_ground source.stage.actors_ground source.stage.order_ground
    source.stage.meet_ground source.stage.action_ground hLabels source.stage.meet
  exact Fin.cases certificate.indices_ground (Fin.cases source.stage.carrier_ground
    (Fin.cases certificate.target.stage.carrier_ground (Fin.cases certificate.target.stage.order_ground
      (Fin.cases certificate.target.stage.meet_ground (Fin.cases certificate.transition.map.points_ground
        (Fin.cases (fields 1).1 (Fin.cases (fields 3).1
          (Fin.cases certificate.filters_ground (Fin.cases (M.groundPower_mem powers source.stage.carrier_ground)
            (fun _ => certificate.compressionCapImages_ground pairing unions powers separation infinite))))))))))

theorem taskCapFamily :
    TaskCapFamilyCode (source.stage.compressionTasks Labels) source.stage.carrier
      certificate.target.stage.carrier certificate.target.stage.order certificate.target.stage.meetGraph
      certificate.transition.map.points (source.stage.compressionTargets Labels)
      (source.stage.compressionSeparators Labels) (source.stage.compressionFilters Labels)
      (M.groundPower source.stage.carrier) certificate.compressionCapImages := by
  refine ⟨certificate.compressionCapImages_function pairing unions powers separation infinite, ?_, ?_⟩
  · intro i _ c _ v _ F _ K _ c' _ v' _ target separator filter cap imageC imageV
    exact certificate.compressionCapImages_profile pairing unions powers separation infinite
      cap target separator filter imageC imageV
  · intro i _ j _ c _ K _ L _ c' _ different targetI targetJ capI capJ imageC
    exact certificate.compressionCapImages_common_target_meet pairing unions powers separation infinite
      hLabels capI capJ targetI targetJ different imageC

theorem realize_taskCapFamily :
    Realize M.sets (BoundedFormula.taskCapFamilyFormula 0 1 2 3 4 5 6 7 8 9 10).toFormula
      certificate.taskCapValues :=
  (BoundedFormula.realize_taskCapFamilyFormula M 0 1 2 3 4 5 6 7 8 9 10
    certificate.taskCapValues
    (certificate.taskCapValues_ground pairing unions powers separation infinite hLabels)).2
    (certificate.taskCapFamily pairing unions powers separation infinite hLabels)

end GroundInitialMainSuccessorData

end PartitionPilot.Forcing

end OAI
