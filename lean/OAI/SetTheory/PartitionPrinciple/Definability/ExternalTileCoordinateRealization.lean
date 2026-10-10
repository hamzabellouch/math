import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalLocalHeightFamilies
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalTileSlotSupports

namespace OAI



namespace PartitionPilot.Forcing.GroundExternalLocalHeightData
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (heights : GroundExternalLocalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi completion)
noncomputable def coordinates : ZFSet.{u} :=
  transportedTileCoordinates
    (M.externalStarVertices G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0))
      (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)) m one)
    (M.externalGroupCarrier G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one)
    (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0))
    (completion.externalPointCarrier P0 r0 μ0 A0) D
    (completion.externalPointAction P0 r0 μ0 A0) heights.family

end PartitionPilot.Forcing.GroundExternalLocalHeightData

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
local notation "c" => data.externalCosetPresentation group oldAction pairing unions powers separation infinite hG
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "Requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "E" => M.externalGroupCarrier G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one
local notation "C" => M.externalCosetCarrier G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one
variable {D rD lo hi : ZFSet.{u}}
variable (heights : GroundExternalLocalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi completion)
local notation "coordinates" => heights.coordinates
local notation "localp" => data.localTilePresentation group oldAction pairing unions powers separation infinite hG
include data group oldAction pairing unions powers separation infinite hG

theorem externalTileCoordinates_iff :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index) (a : ((family).tile r).Space)
      (h : ZFSet.{u}), ZFSet.pair (externalRequestIndexCode r) h ∈ heights.family → ∀ d,
      ZFSet.pair (ZFSet.pair ((vpres).encode (.inr (w, r)))
        ((q).encode (((family).placedTile (action) w r).toFun a))) d ∈ coordinates ↔
          ZFSet.pair (((localp r)).encode a) d ∈ h := by
  let := group.toGroup
  intro w r a h selected d
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vc := (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1
  have acted := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1
  have code := (heights.values _ _ selected).2.1
  rw [GroundExternalLocalHeightData.coordinates, pair_mem_transportedTileCoordinates]
  constructor
  · rintro ⟨_, _, _, w', _, r', _, y, _, h', _, equal, selected', acted', value⟩
    change ZFSet.pair (natSetCode 1) (ZFSet.pair ((s).encode w) (externalRequestIndexCode r)) =
      ZFSet.pair (natSetCode 1) (ZFSet.pair w' r') at equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).2
    have sameH := (show FunctionGraphOn Requests heights.family from ⟨_, heights.function⟩).unique selected' selected
    subst h'
    have hy := (ZFSet.pair_mem_prod.1 (code.function.1 value)).1
    obtain ⟨b, rfl⟩ := (data.localTileCarrier_image group oldAction pairing unions powers separation infinite hG r y).1 hy
    have same := (acted w (((family).placedTile (action) 1 r).toFun b)
      (((family).placedTile (action) w r).toFun a)).1 acted'
    rw [(family).translate_tile, mul_one] at same
    have ba := embedding_injective ((family).placedTile (action) w r).toMeetEmbedding same
    subst b
    exact value
  · intro value
    have hd := (ZFSet.pair_mem_prod.1 (code.function.1 value)).2
    refine ⟨vc ▸ (vpres).encode_mem _, qc ▸ (q).encode_mem _, hd,
      (s).encode w, sc ▸ (s).encode_mem _, externalRequestIndexCode r,
      (externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem _,
      ((localp r)).encode a, ?_, h, pair_second_mem_doubleUnion selected, rfl, selected, ?_, value⟩
    · exact completion.localTileCarrier_subset P0 r0 μ0 A0 _ (((localp r)).encode_mem a)
    · apply (acted w (((family).placedTile (action) 1 r).toFun a) _).2
      rw [(family).translate_tile, mul_one]

include heights in
theorem externalTileCoordinates_ground (hP0 : P0 ∈ M.sets) (hD : D ∈ M.sets) : coordinates ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  exact M.transportedTileCoordinates_mem pairing unions powers separation
    (data.externalStarCarriers_ground pairing unions powers separation hG).1 data.group.carrier_mem
    data.words.requests_ground geometry.carrier_ground hD geometry.action_ground heights.family_ground

include heights in
theorem externalTileCoordinates_partial (hP0 : P0 ∈ M.sets) :
    PartialFunctionCode (ZFSet.prod
      (M.externalStarVertices G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) Requests m one) Q) D coordinates := by
  let := group.toGroup
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have acted := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1
  apply transportedTileCoordinates_partial (show FunctionGraphOn Requests heights.family from ⟨_, heights.function⟩)
  · intro i h y a b selected first second
    exact (functionCode_partial (heights.values _ _ selected).2.1.function).unique y a b first second
  · intro w hw y hy z hz x first second
    obtain ⟨w, rfl⟩ := ((s).mem_carrier w).1 (sc.symm ▸ hw)
    obtain ⟨y, rfl⟩ := ((q).mem_carrier y).1 (qc.symm ▸ hy)
    obtain ⟨z, rfl⟩ := ((q).mem_carrier z).1 (qc.symm ▸ hz)
    have hx := (ZFSet.pair_mem_prod.1 (geometry.action.function.1 first)).2
    obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ hx)
    have same := ((acted w y x).1 first).trans ((acted w z x).1 second).symm
    apply congrArg (q).encode
    have back := congrArg ((family).translate (action) w⁻¹) same
    simpa only [(family).translate_left_inverse] using back

theorem externalTileCoordinates_total :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index) (a : ((family).tile r).Space),
      ∃ d ∈ D, ZFSet.pair (ZFSet.pair ((vpres).encode (.inr (w, r)))
        ((q).encode (((family).placedTile (action) w r).toFun a))) d ∈ coordinates := by
  let := group.toGroup
  intro w r a
  obtain ⟨h, selected, _⟩ := heights.function.2 _
    ((externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem r)
  have code := (heights.values _ _ selected).2.1
  obtain ⟨d, value, _⟩ := code.function.2 _ (((localp r)).encode_mem a)
  exact ⟨d, (ZFSet.pair_mem_prod.1 (code.function.1 value)).2,
    (data.externalTileCoordinates_iff group oldAction pairing unions powers separation infinite hG heights w r a h selected d).2 value⟩

theorem externalTileCoordinates_strict :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index) (a b : ((family).tile r).Space),
      a ≠ b → ((family).tile r).order.le a b → ∀ d e,
      ZFSet.pair (ZFSet.pair ((vpres).encode (.inr (w, r)))
        ((q).encode (((family).placedTile (action) w r).toFun a))) d ∈ coordinates →
      ZFSet.pair (ZFSet.pair ((vpres).encode (.inr (w, r)))
        ((q).encode (((family).placedTile (action) w r).toFun b))) e ∈ coordinates →
      ZFSet.pair d e ∈ rD := by
  let := group.toGroup
  intro w r a b distinct lower d e first second
  obtain ⟨h, selected, _⟩ := heights.function.2 _
    ((externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem r)
  have code := (heights.values _ _ selected).2.1
  have first' := (data.externalTileCoordinates_iff group oldAction pairing unions powers separation infinite hG heights w r a h selected d).1 first
  have second' := (data.externalTileCoordinates_iff group oldAction pairing unions powers separation infinite hG heights w r b h selected e).1 second
  exact code.strict _ (((localp r)).encode_mem a) _ (((localp r)).encode_mem b)
    (fun equal => distinct (((localp r)).injective equal))
    ((data.localTileOrder_iff group oldAction pairing unions powers separation infinite hG r a b).2 lower) d e first' second'

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end OAI
