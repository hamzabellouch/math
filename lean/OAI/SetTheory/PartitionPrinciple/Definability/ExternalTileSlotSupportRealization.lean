import OAI.SetTheory.PartitionPrinciple.Geometry.ExternalOwnerCoordinateLaws

namespace OAI



namespace PartitionPilot.Forcing.GroundCompressionCompletion
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
noncomputable def externalTileSlotPoints (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  externalTileSlotSupports
    (M.externalStarVertices G (externalChildLetters I P (externalRectangles P G r μ A))
      (externalRequestCarrier I P (externalRectangles P G r μ A)) m one)
    (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (externalRequestCarrier I P (externalRectangles P G r μ A))
    (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    (completion.externalPointAction P r μ A) (completion.localTileVertexImages P r μ A)

end PartitionPilot.Forcing.GroundCompressionCompletion

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
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
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "vcode" => completion.externalFamilyVertexCode group oldAction data.original
local notation "slots" => completion.externalTileSlotPoints P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG

theorem externalTileSlotPoints_entry :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index)
      (i : Option ((family).Child r)) (y : (family).Node (action)),
      ZFSet.pair (ZFSet.pair ((vpres).encode (.inr (w, r))) (vcode r i)) ((q).encode y) ∈ slots ↔
        ∃ x : SetMembers U,
          ((family).placedTile (action) w r).toFun (((family).flatVertex r i).toFun x) = y := by
  let := group.toGroup
  intro w r i y
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vc := (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1
  have acted := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1
  rw [GroundCompressionCompletion.externalTileSlotPoints, pair_mem_externalTileSlotSupports]
  constructor
  · rintro ⟨_, _, _, w', _, r', _, x, hx, z, hz, equal, copied, moved⟩
    change ZFSet.pair (natSetCode 1) (ZFSet.pair ((s).encode w) (externalRequestIndexCode r)) =
      ZFSet.pair (natSetCode 1) (ZFSet.pair w' r') at equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).2
    obtain ⟨z, rfl⟩ := ((q).mem_carrier z).1 (qc.symm ▸ hz)
    let x' := SetMembers.ofMem x hx
    have copied' := (data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG
      r i x' z).1 (by simpa only [GroundCompressionCompletion.externalFamilyTileVertexPresentation_encode,
        x', SetMembers.raw_ofMem] using copied)
    have moved' := (acted w z y).1 moved
    rw [← copied', ← (family).flatVertex_copy, (family).translate_tile, mul_one] at moved'
    exact ⟨x', moved'⟩
  · rintro ⟨x, rfl⟩
    refine ⟨vc ▸ (vpres).encode_mem _, data.localTileVertexCode_mem group oldAction r i,
      qc ▸ (q).encode_mem _, (s).encode w, sc ▸ (s).encode_mem _, externalRequestIndexCode r,
      (externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem _,
      SetMembers.raw x, SetMembers.raw_mem x,
      (q).encode (((family).placedTile (action) 1 r).toFun (((family).flatVertex r i).toFun x)),
      qc ▸ (q).encode_mem _, rfl, ?_, ?_⟩
    · apply (data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG r i x _).2
      exact ((family).flatVertex_copy (action) 1 r i x).symm
    · apply (acted w _ _).2
      rw [(family).translate_tile, mul_one]

theorem externalTileSlotPoints_ground (hP0 : P0 ∈ M.sets) : slots ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have localGround := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  exact M.externalTileSlotSupports_mem pairing unions powers separation infinite
    (data.externalStarCarriers_ground pairing unions powers separation hG).1 data.group.carrier_mem
    data.words.requests_ground (completion.algebra.union.ground 0) geometry.carrier_ground
    geometry.action_ground localGround.2.2.2.1

theorem externalTileSlotPoints_decode {v j x : ZFSet.{u}}
    (supported : ZFSet.pair (ZFSet.pair v j) x ∈ slots) :
    letI := group.toGroup
    ∃ (w : External (SetMembers G) (family).Letters) (r : Index)
      (i : Option ((family).Child r)) (a : SetMembers U),
      v = (vpres).encode (.inr (w, r)) ∧ j = vcode r i ∧
      x = (q).encode (((family).placedTile (action) w r).toFun (((family).flatVertex r i).toFun a)) := by
  let := group.toGroup
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have raw := (pair_mem_externalTileSlotSupports _ _ _ _ _ _ _ _ _ _).1 supported
  obtain ⟨_, _, hx, w, hw, r, hr, a, _, z, _, equal, copied, _⟩ := raw
  obtain ⟨w, rfl⟩ := ((s).mem_carrier w).1 (sc.symm ▸ hw)
  obtain ⟨r, rfl⟩ := ((externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).mem_carrier r).1 hr
  obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ hx)
  have vertex : ZFSet.pair (ZFSet.pair (externalRequestIndexCode r) j) a ∈
      completion.externalVertices P0 r0 μ0 A0 :=
    ((pair_mem_relationCompose _ _ _ _ _ _ _).1 copied).1
  have shape := (triple_mem_externalTileVertices _ _ _ _ _ _).1 vertex
  have range : j = natSetCode 0 ∨ j = natSetCode 1 ∨
      (externalRequestIndexCode r ∈ ZFSet.prod {natSetCode 2} (externalRectangles P0 G r0 μ0 A0) ∧
        j = natSetCode 2) := by tauto
  obtain ⟨i, rfl⟩ := (completion.externalFamilyVertexCode_range group oldAction data.original r j).1 range
  have ev : v = (vpres).encode (.inr (w, r)) := equal
  subst v
  obtain ⟨a, ha⟩ := (data.externalTileSlotPoints_entry group oldAction pairing unions powers separation infinite hG
    w r i x).1 supported
  exact ⟨w, r, i, a, rfl, rfl, congrArg (q).encode ha.symm⟩

theorem externalTileSlotPoints_owner_cover {x v : ZFSet.{u}}
    (fresh : x ∉ completion.externalSeedCarrier P0 r0 μ0 A0)
    (owned : ZFSet.pair x v ∈ completion.externalStarOwner P0 r0 μ0 A0) :
    ∃ j ∈ natSetCode 3, ZFSet.pair (ZFSet.pair v j) x ∈ slots := by
  let := group.toGroup
  obtain ⟨w, r, a, rfl, rfl, _⟩ := data.externalStarOwner_fresh_tile group oldAction pairing unions powers
    separation infinite hG x v owned fresh
  obtain ⟨i, b, rfl⟩ := (family).flatVertex_cover r a
  exact ⟨vcode r i, data.localTileVertexCode_mem group oldAction r i,
    (data.externalTileSlotPoints_entry group oldAction pairing unions powers separation infinite hG w r i _).2 ⟨b, rfl⟩⟩

theorem externalTileSlotPoints_lower {v j x y : ZFSet.{u}}
    (hx : x ∈ Q) (lower : ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0)
    (supported : ZFSet.pair (ZFSet.pair v j) y ∈ slots) :
    ZFSet.pair (ZFSet.pair v j) x ∈ slots := by
  let := group.toGroup
  obtain ⟨w, r, i, a, rfl, rfl, rfl⟩ :=
    data.externalTileSlotPoints_decode group oldAction pairing unions powers separation infinite hG supported
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ hx)
  have below := ((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).1 x _).1 lower
  rw [(family).flatVertex_copy] at below
  obtain ⟨b, equal⟩ := ((family).copy (action) ((family).flatWord w r i)).ideal a x below
  apply (data.externalTileSlotPoints_entry group oldAction pairing unions powers separation infinite hG w r i x).2
  exact ⟨b, ((family).flatVertex_copy (action) w r i b).trans equal⟩

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end OAI
