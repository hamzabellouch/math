import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalLocalHeightSelection

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
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

include data group oldAction pairing unions powers separation infinite hG in
theorem request_generator_value :
    letI := group.toGroup
    ∀ (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0))
      (j : (family).Child r) k,
      ZFSet.pair ((letters).encode ⟨r,j⟩) k ∈ generators ↔
        k = (s).encode (generator (SetMembers G) (family).Letters ⟨r,j⟩) := by
  let := group.toGroup
  intro r j k
  rw [completion.externalFamilyGroupPresentation_generators group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground]
  constructor
  · intro entry
    obtain ⟨v, equal⟩ := ((letters).mem_graph (s) (generator (SetMembers G) (family).Letters) _).1 entry
    have parts := ZFSet.pair_inj.1 equal
    have same := (letters).injective parts.1
    simpa only [same] using parts.2.symm
  · rintro rfl
    exact ((letters).pair_mem_graph (s) _ _ _).2 rfl

include data group oldAction pairing unions powers separation infinite hG in
theorem request_generator_action :
    letI := group.toGroup
    ∀ (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0))
      (j : (family).Child r) k,
      ZFSet.pair ((letters).encode ⟨r,j⟩) k ∈ generators →
      ∀ x y, ZFSet.pair (ZFSet.pair k ((q).encode x)) ((q).encode y) ∈
          completion.externalPointAction P0 r0 μ0 A0 ↔
        (family).translate (action) (generator (SetMembers G) (family).Letters ⟨r,j⟩) x = y := by
  let := group.toGroup
  intro r j k entry x y
  rw [(data.request_generator_value group oldAction pairing unions powers separation infinite hG r j k).1 entry]
  exact (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1 _ x y

include data group oldAction in
theorem request_generator_ground :
    letI := group.toGroup
    ∀ (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0))
      (j : (family).Child r) k,
      ZFSet.pair ((letters).encode ⟨r,j⟩) k ∈ generators → k ∈ M.sets := by
  let := group.toGroup
  intro r j k entry
  have point := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 entry)).2
  exact M.transitive data.group.carrier_mem point

include data group oldAction pairing unions powers separation infinite hG in
theorem request_action_value :
    letI := group.toGroup
    ∀ (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0))
      (j : (family).Child r) k,
      ZFSet.pair ((letters).encode ⟨r,j⟩) k ∈ generators →
      ∀ x y, ZFSet.pair (ZFSet.pair k ((q).encode x)) y ∈
          completion.externalPointAction P0 r0 μ0 A0 ↔
        y = (q).encode ((family).translate (action) (generator (SetMembers G) (family).Letters ⟨r,j⟩) x) := by
  let := group.toGroup
  intro r j k entry x y
  constructor
  · intro acted
    have hy := ((pair_mem_flatCopyActionGraph _ _ _ _ _ _ _ _).1 acted).2.2.1
    rw [← data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG] at hy
    obtain ⟨y, rfl⟩ := ((q).mem_carrier _).1 hy
    exact congrArg (q).encode ((data.request_generator_action group oldAction pairing unions powers separation
      infinite hG r j k entry x y).1 acted).symm
  · rintro rfl
    exact (data.request_generator_action group oldAction pairing unions powers separation infinite hG r j k entry x _).2 rfl

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end

end OAI
