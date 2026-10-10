import OAI.SetTheory.PartitionPrinciple.Definability.CompressionRequestRealization
import OAI.SetTheory.PartitionPrinciple.Definability.ExternalRequestGraphCoordinates
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundExternalOldAction
import OAI.SetTheory.PartitionPrinciple.Forcing.IdealInsertionProfileTransport

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "letters" => completion.externalFamilyLetterPresentation group oldAction data.original
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "U" => completion.algebra.union.fields 0
local notation "generators" => M.externalChildGenerators G
  (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one

local notation "root" => Compression.RecursiveMaps.TileRequests.Family.copy
  (completion.externalFamily group oldAction data.original)
  (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet) 1
local notation "ru" => completion.algebra.union.fields 1
local notation "au" => completion.algebra.union.fields 12
local notation "newAction" => completion.externalPointAction P0 r0 μ0 A0
local notation "newMeet" => completion.externalPointMeet P0 r0 μ0 A0
local notation "newOrder" => completion.externalPointOrder P0 r0 μ0 A0
local notation "P" => completion.algebra.union.meet.toSmallMeetOrder

include data group oldAction pairing unions powers separation infinite hG in
theorem separation_generator_fixes (W : SetMembers P0) :
    letI := group.toGroup
    ∀ k, ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 1) (SetMembers.raw W)) (natSetCode 0)) k ∈ generators →
      ∀ z ∈ completion.externalPointCarrier P0 r0 μ0 A0,
        ZFSet.pair z ((q).encode ((root).toFun
          (SetMembers.ofMem (SetMembers.raw W) (data.original.subset (SetMembers.raw_mem W))))) ∈ newOrder →
        ZFSet.pair (ZFSet.pair k z) z ∈ newAction := by
  let := group.toGroup
  intro k gen z hz lower
  rw [← data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG] at hz
  obtain ⟨z, rfl⟩ := ((q).mem_carrier _).1 hz
  apply (data.request_generator_action group oldAction pairing unions powers separation infinite hG
    (.inr (.inl W)) ⟨()⟩ k gen z z).2
  exact completion.external_separation_fixes group oldAction data.original W z
    (((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).1 _ _).1 lower)

include data group oldAction pairing unions powers separation infinite hG in
theorem separation_generator_meet (W : SetMembers P0) (x y : SetMembers U)
    (wx : ZFSet.pair (SetMembers.raw W) (SetMembers.raw x) ∈ ru)
    (wy : ZFSet.pair (SetMembers.raw W) (SetMembers.raw y) ∈ ru) :
    letI := group.toGroup
    ∀ k, ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 1) (SetMembers.raw W)) (natSetCode 0)) k ∈ generators →
      ∀ z, ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun x))) z ∈ newAction →
        ZFSet.pair (ZFSet.pair z ((q).encode ((root).toFun y)))
          ((q).encode ((root).toFun (SetMembers.ofMem (SetMembers.raw W)
            (data.original.subset (SetMembers.raw_mem W))))) ∈ newMeet := by
  let := group.toGroup
  intro k gen z acted
  rw [(data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inl W)) ⟨()⟩ k gen _ z).1 acted]
  exact ((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.1 _ _ _).2
    (completion.external_separation_meet group oldAction data.original W x y wx wy)

include data group oldAction pairing unions powers separation infinite hG in
theorem compression_generator_restriction (i : SetMembers I) (x y : SetMembers U)
    (map : ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ completion.externalMap i) :
    letI := group.toGroup
    ∀ k, ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun x))) ((q).encode ((root).toFun y)) ∈ newAction := by
  let := group.toGroup
  intro k gen
  apply (data.request_generator_action group oldAction pairing unions powers separation infinite hG
    (.inl i) ⟨()⟩ k gen _ _).2
  have equal : ((completion.externalCopy i).toFun x).val = y := by
    apply SetMembers.raw_injective U
    exact (show FunctionGraphOn U (completion.externalMap i) from
      ⟨U, (completion.algebra.embedding _ _ (completion.externalMap_entry i)).injection.function⟩).unique
      (completion.externalCopy_entry i x) map
  rw [completion.external_compression_restriction group oldAction data.original, equal]

include data group oldAction pairing unions powers separation infinite hG in
theorem compression_generator_top (i : SetMembers I) :
    letI := group.toGroup
    ∀ k, ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun (SetMembers.ofMem τ completion.top_mem))))
        ((q).encode ((root).toFun (completion.externalCap i))) ∈ newAction := by
  let := group.toGroup
  intro k gen
  exact (data.request_generator_action group oldAction pairing unions powers separation infinite hG
    (.inl i) ⟨()⟩ k gen _ _).2 (completion.external_compression_top group oldAction data.original i)

include data group oldAction pairing unions powers separation infinite hG in
theorem compression_generator_agreement (i : SetMembers I) {a g : ZFSet.{u}}
    (source : ZFSet.pair (SetMembers.raw i) a ∈ Sources)
    (rep : ZFSet.pair (SetMembers.raw i) g ∈ Reps)
    (x y : SetMembers U) (lower : ZFSet.pair (SetMembers.raw x) a ∈ ru)
    (acted : ZFSet.pair (ZFSet.pair g (SetMembers.raw x)) (SetMembers.raw y) ∈ au) :
    letI := group.toGroup
    ∀ k, ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun x))) ((q).encode ((root).toFun y)) ∈ newAction := by
  let := group.toGroup
  exact data.compression_generator_restriction group oldAction pairing unions powers separation infinite hG i x y
    ((completion.source_agreement _ _ _ _ _ _ (completion.externalMap_entry i) source rep lower).2 acted)

end GroundExternalGeometryInputs

namespace GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "letters" => completion.externalFamilyLetterPresentation group oldAction data.original
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "U" => completion.algebra.union.fields 0
local notation "generators" => M.externalChildGenerators G
  (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one

local notation "root" => Compression.RecursiveMaps.TileRequests.Family.copy
  (completion.externalFamily group oldAction data.original)
  (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet) 1
local notation "ru" => completion.algebra.union.fields 1
local notation "au" => completion.algebra.union.fields 12
local notation "newAction" => completion.externalPointAction P0 r0 μ0 A0
local notation "newMeet" => completion.externalPointMeet P0 r0 μ0 A0
local notation "newOrder" => completion.externalPointOrder P0 r0 μ0 A0
local notation "P" => completion.algebra.union.meet.toSmallMeetOrder

include data group oldAction pairing unions powers separation infinite hG in
theorem rectangle_generators_roots (z : SetMembers (externalRectangles P0 G r0 μ0 A0))
    (x : SetMembers U) (below : (P).le x (completion.externalRectangle group oldAction data.original z).C) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction data.original z
    ∀ k l,
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 1)) l ∈ generators →
      ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun x)))
        ((q).encode ((root).toFun (((action).iso r.first).toFun x))) ∈ newAction ∧
      ZFSet.pair (ZFSet.pair l ((q).encode ((root).toFun x)))
        ((q).encode ((root).toFun (((action).iso r.second).toFun x))) ∈ newAction := by
  let := group.toGroup
  dsimp only
  intro k l gen1 gen2
  have laws := completion.external_rectangle_roots group oldAction data.original z x below
  exact ⟨(data.request_generator_action group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨false⟩ k gen1 _ _).2 laws.1,
    (data.request_generator_action group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨true⟩ l gen2 _ _).2 laws.2⟩

include data group oldAction pairing unions powers separation infinite hG in
theorem rectangle_generators_agree (z : SetMembers (externalRectangles P0 G r0 μ0 A0))
    (x : SetMembers U) (below : (P).le x (completion.externalRectangle group oldAction data.original z).B) :
    letI := group.toGroup
    ∀ k l,
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 1)) l ∈ generators →
      ∀ y v, ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun x))) y ∈ newAction →
        ZFSet.pair (ZFSet.pair l ((q).encode ((root).toFun x))) v ∈ newAction → y = v := by
  let := group.toGroup
  intro k l gen1 gen2 y v act1 act2
  rw [(data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨false⟩ k gen1 _ y).1 act1,
    (data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨true⟩ l gen2 _ v).1 act2]
  exact congrArg (q).encode (completion.external_rectangle_children group oldAction data.original z x below)

include data group oldAction pairing unions powers separation infinite hG in
theorem rectangle_generators_root_meets (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) (x : SetMembers U) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction data.original z
    ∀ k l,
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 1)) l ∈ generators →
      ∀ y v, ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun r.D))) y ∈ newAction →
        ZFSet.pair (ZFSet.pair l ((q).encode ((root).toFun r.D))) v ∈ newAction →
        ZFSet.pair (ZFSet.pair y ((q).encode ((root).toFun x)))
          ((q).encode ((root).toFun ((P).meet (((action).iso r.first).toFun r.C) x))) ∈ newMeet ∧
        ZFSet.pair (ZFSet.pair v ((q).encode ((root).toFun x)))
          ((q).encode ((root).toFun ((P).meet (((action).iso r.second).toFun r.C) x))) ∈ newMeet := by
  let := group.toGroup
  dsimp only
  intro k l gen1 gen2 y v act1 act2
  rw [(data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨false⟩ k gen1 _ y).1 act1,
    (data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨true⟩ l gen2 _ v).1 act2]
  have laws := completion.external_rectangle_root_meets group oldAction data.original z x
  have meet := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.1
  exact ⟨(meet _ _ _).2 laws.1, (meet _ _ _).2 laws.2⟩

include data group oldAction pairing unions powers separation infinite hG in
theorem rectangle_generators_meet (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction data.original z
    ∀ k l,
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 1)) l ∈ generators →
      ∀ y v b, ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun r.D))) y ∈ newAction →
        ZFSet.pair (ZFSet.pair l ((q).encode ((root).toFun r.D))) v ∈ newAction →
        ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun r.B))) b ∈ newAction →
        ZFSet.pair (ZFSet.pair y v) b ∈ newMeet ∧
        ZFSet.pair (ZFSet.pair l ((q).encode ((root).toFun r.B))) b ∈ newAction := by
  let := group.toGroup
  dsimp only
  intro k l gen1 gen2 y v b act1 act2 actB
  rw [(data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨false⟩ k gen1 _ y).1 act1,
    (data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨true⟩ l gen2 _ v).1 act2,
    (data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨false⟩ k gen1 _ b).1 actB]
  refine ⟨((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.1 _ _ _).2
    (completion.external_rectangle_children_meet group oldAction data.original z), ?_⟩
  apply (data.request_generator_action group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨true⟩ l gen2 _ _).2
  exact (completion.external_rectangle_children group oldAction data.original z _ ((P).refl _)).symm

end GroundExternalGeometryInputs

namespace GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "letters" => completion.externalFamilyLetterPresentation group oldAction data.original
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "U" => completion.algebra.union.fields 0
local notation "generators" => M.externalChildGenerators G
  (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one

local notation "root" => Compression.RecursiveMaps.TileRequests.Family.copy
  (completion.externalFamily group oldAction data.original)
  (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet) 1
local notation "ru" => completion.algebra.union.fields 1
local notation "au" => completion.algebra.union.fields 12
local notation "newAction" => completion.externalPointAction P0 r0 μ0 A0
local notation "newMeet" => completion.externalPointMeet P0 r0 μ0 A0
local notation "newOrder" => completion.externalPointOrder P0 r0 μ0 A0
local notation "P" => completion.algebra.union.meet.toSmallMeetOrder

local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "identityCopy" => completion.externalCopyGraph P0 r0 μ0 A0
  (M.externalGroupIdentity G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one)

include data group oldAction pairing unions powers separation infinite hG in
theorem external_identity_copy_value :
    letI := group.toGroup
    ∀ (x : SetMembers U) y, ZFSet.pair (SetMembers.raw x) y ∈ identityCopy ↔
      y = (q).encode ((root).toFun x) := by
  let := group.toGroup
  intro x y
  rw [completion.externalFamilyGroupPresentation_identity group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground,
    data.externalCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG]
  constructor
  · intro entry
    obtain ⟨v, equal⟩ := ((SetMembers.presentation U).mem_graph (q) (root).toFun _).1 entry
    have parts := ZFSet.pair_inj.1 equal
    have same := (SetMembers.presentation U).injective parts.1
    simpa only [same] using parts.2.symm
  · rintro rfl
    exact ((SetMembers.presentation U).pair_mem_graph (q) _ _ _).2 rfl

include data group oldAction pairing unions powers separation infinite hG in
theorem external_identity_capProfile (hP0 : P0 ∈ M.sets)
    {c v K F c' v' K' : ZFSet.{u}}
    (profile : CodedCapProfile U (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) c v K F)
    (imageC : ZFSet.pair c c' ∈ identityCopy) (imageV : ZFSet.pair v v' ∈ identityCopy)
    (imageK : ZFSet.pair K K' ∈ identityCopy) :
    CodedCapProfile Q newOrder newMeet c' v' K' (relationImage F Q identityCopy) :=
  (data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG).capProfile
    completion.algebra.union.meet
    (data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0).meet
    completion.top_mem completion.top profile imageC imageV imageK

include data group oldAction pairing unions powers separation infinite hG in
theorem external_identity_filter_ground (hP0 : P0 ∈ M.sets)
    {F : ZFSet.{u}} (hF : F ∈ M.sets) : relationImage F Q identityCopy ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  exact M.relationImage_mem separation hF geometry.carrier_ground
    (geometry.copies_ground _ data.group.group_code.identity_mem)

include data group oldAction pairing unions powers separation infinite hG in
theorem external_compression_generator_profile (hP0 : P0 ∈ M.sets)
    (i : SetMembers I) {c v F c' v' τ' : ZFSet.{u}}
    (profile : CodedCapProfile U (completion.algebra.union.fields 1) (completion.algebra.union.fields 2)
      c v (SetMembers.raw (completion.externalCap i)) F)
    (imageC : ZFSet.pair c c' ∈ identityCopy) (imageV : ZFSet.pair v v' ∈ identityCopy)
    (imageTop : ZFSet.pair τ τ' ∈ identityCopy) :
    ∀ k, ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0)) k ∈ generators →
      ∀ K', ZFSet.pair (ZFSet.pair k τ') K' ∈ newAction →
        CodedCapProfile Q newOrder newMeet c' v' K' (relationImage F Q identityCopy) := by
  let := group.toGroup
  intro k gen K' acted
  have topEq := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG
    (SetMembers.ofMem τ completion.top_mem) τ').1 (by simpa only [SetMembers.raw_ofMem] using imageTop)
  rw [topEq] at acted
  have value := (data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inl i) ⟨()⟩ k gen _ K').1 acted
  rw [completion.external_compression_top group oldAction data.original] at value
  apply data.external_identity_capProfile group oldAction pairing unions powers separation infinite hG hP0 profile imageC imageV
  exact (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG
    (completion.externalCap i) K').2 value

end GroundExternalGeometryInputs

namespace GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
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
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "generators" => M.externalChildGenerators G letters m one
local notation "copyGraph" => completion.externalCopyGraph P0 r0 μ0 A0 (M.externalGroupIdentity G letters m one)
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "root" => Compression.RecursiveMaps.TileRequests.Family.copy
  (completion.externalFamily group oldAction data.original) action 1
local notation "newAction" => completion.externalPointAction P0 r0 μ0 A0
local notation "newOrder" => completion.externalPointOrder P0 r0 μ0 A0
local notation "P" => completion.algebra.union.meet.toSmallMeetOrder
include data group oldAction pairing unions powers separation infinite hG hP

theorem rectangle_generators_full_ideals (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction data.original z
    ∀ k l,
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 1)) l ∈ generators →
      ∀ g' h' c' b',
      ZFSet.pair (SetMembers.raw r.first) g' ∈ M.externalOldInclusion G letters m one →
      ZFSet.pair (SetMembers.raw r.second) h' ∈ M.externalOldInclusion G letters m one →
      ZFSet.pair (SetMembers.raw r.C) c' ∈ copyGraph →
      ZFSet.pair (SetMembers.raw r.B) b' ∈ copyGraph →
      ActionAgreementBelow Q newOrder newAction k g' c' ∧
      ActionAgreementBelow Q newOrder newAction l h' c' ∧
      ActionAgreementBelow Q newOrder newAction k l b' := by
  let := group.toGroup
  dsimp only
  intro k l gen1 gen2 g' h' c' b' ag ah ec eb
  let r := completion.externalRectangle group oldAction data.original z
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have ideal := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have hk := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 gen1)).2
  have hl := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 gen2)).2
  have hg' := (ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 ag)).2
  have hh' := (ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 ah)).2
  have same {a b x v : ZFSet.{u}} (ha : a ∈ M.externalGroupCarrier G letters m one) (hb : b ∈ M.externalGroupCarrier G letters m one)
      (hx : x ∈ Q) (first : ZFSet.pair (ZFSet.pair a x) v ∈ newAction)
      (second : ZFSet.pair (ZFSet.pair b x) v ∈ newAction) (y : ZFSet.{u}) :
      ZFSet.pair (ZFSet.pair a x) y ∈ newAction ↔ ZFSet.pair (ZFSet.pair b x) y ∈ newAction := by
    obtain ⟨_, _, ua⟩ := geometry.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨ha, hx⟩)
    obtain ⟨_, _, ub⟩ := geometry.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨hb, hx⟩)
    exact ⟨fun entry => ((ua y entry).trans (ua v first).symm).symm ▸ second,
      fun entry => ((ub y entry).trans (ub v second).symm).symm ▸ first⟩
  have atC (x' : ZFSet.{u}) (hx' : x' ∈ Q) (lower : ZFSet.pair x' c' ∈ newOrder) :
      ∀ y, (ZFSet.pair (ZFSet.pair k x') y ∈ newAction ↔ ZFSet.pair (ZFSet.pair g' x') y ∈ newAction) ∧
        (ZFSet.pair (ZFSet.pair l x') y ∈ newAction ↔ ZFSet.pair (ZFSet.pair h' x') y ∈ newAction) := by
    obtain ⟨x, hx, below, ex⟩ := ideal.ideal _ _ _ ec hx' lower
    let xu := SetMembers.ofMem x hx
    have eqX := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG xu x').1 (by simpa only [xu, SetMembers.raw_ofMem] using ex)
    have acts := data.rectangle_generators_roots group oldAction pairing unions powers separation infinite hG z xu (by
      change ZFSet.pair (SetMembers.raw xu) _ ∈ _
      simpa only [xu, SetMembers.raw_ofMem] using below) k l gen1 gen2
    rw [← eqX] at acts
    have old1 := (completion.algebra.union.action.toOrderAction_eq_iff group completion.algebra.union.meet
      r.first xu (((action).iso r.first).toFun xu)).1 rfl
    have old2 := (completion.algebra.union.action.toOrderAction_eq_iff group completion.algebra.union.meet
      r.second xu (((action).iso r.second).toFun xu)).1 rfl
    have copy1 := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG
      (((action).iso r.first).toFun xu) _).2 rfl
    have copy2 := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG
      (((action).iso r.second).toFun xu) _).2 rfl
    have acts1 := data.externalIdentityCopy_equivariant group oldAction pairing unions powers separation infinite hG ag ex copy1 (by simpa only [xu, SetMembers.raw_ofMem] using old1)
    have acts2 := data.externalIdentityCopy_equivariant group oldAction pairing unions powers separation infinite hG ah ex copy2 (by simpa only [xu, SetMembers.raw_ofMem] using old2)
    intro y
    exact ⟨same hk hg' hx' acts.1 acts1 y, same hl hh' hx' acts.2 acts2 y⟩
  refine ⟨fun x hx y _ lower => (atC x hx lower y).1,
    fun x hx y _ lower => (atC x hx lower y).2, ?_⟩
  intro x' hx' y _ lower
  obtain ⟨x, hx, below, ex⟩ := ideal.ideal _ _ _ eb hx' lower
  let xu := SetMembers.ofMem x hx
  have eqX := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG xu x').1 (by simpa only [xu, SetMembers.raw_ofMem] using ex)
  obtain ⟨u, act1, _⟩ := geometry.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨hk, hx'⟩)
  obtain ⟨v, act2, _⟩ := geometry.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨hl, hx'⟩)
  have equal := data.rectangle_generators_agree group oldAction pairing unions powers separation infinite hG z xu (by
    change ZFSet.pair (SetMembers.raw xu) _ ∈ _
    simpa only [xu, SetMembers.raw_ofMem] using below)
    k l gen1 gen2 u v (eqX ▸ act1) (eqX ▸ act2)
  exact same hk hl hx' act1 (equal.symm ▸ act2) y

end GroundExternalGeometryInputs

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

include profiled data group oldAction pairing unions powers separation infinite hG in
theorem external_generator_profile (hP0 : P0 ∈ M.sets) (hFilters : Filters ∈ M.sets)
    (i : SetMembers I) {c v F c' v' τ' : ZFSet.{u}}
    (target : ZFSet.pair (SetMembers.raw i) c ∈ Targets)
    (separator : ZFSet.pair (SetMembers.raw i) v ∈ Separators)
    (filter : ZFSet.pair (SetMembers.raw i) F ∈ Filters)
    (imageC : ZFSet.pair c c' ∈ identityCopy) (imageV : ZFSet.pair v v' ∈ identityCopy)
    (imageTop : ZFSet.pair τ τ' ∈ identityCopy) :
    relationImage F Q identityCopy ∈ M.sets ∧
      ∀ k, ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0)) k ∈
        M.externalChildGenerators G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one →
        ∀ K', ZFSet.pair (ZFSet.pair k τ') K' ∈ profiled.heighted.completion.externalPointAction P0 r0 μ0 A0 →
          CodedCapProfile Q (profiled.heighted.completion.externalPointOrder P0 r0 μ0 A0)
            (profiled.heighted.completion.externalPointMeet P0 r0 μ0 A0)
            c' v' K' (relationImage F Q identityCopy) := by
  have hPair := M.transitive hFilters filter
  have hF := M.transitive (M.transitive hPair (ZFSet.mem_pair.2 (Or.inr rfl)))
    (ZFSet.mem_pair.2 (Or.inr rfl))
  have profile := profiled.profiles (SetMembers.raw i) c v
    (SetMembers.raw (profiled.heighted.completion.externalCap i)) F
    (profiled.heighted.completion.externalCap_entry i) target separator filter
  exact ⟨data.external_identity_filter_ground group oldAction pairing unions powers separation infinite hG hP0 hF,
    data.external_compression_generator_profile group oldAction pairing unions powers separation infinite hG hP0
      i profile imageC imageV imageTop⟩

end GroundProfiledCompression

end PartitionPilot.Forcing

end OAI
