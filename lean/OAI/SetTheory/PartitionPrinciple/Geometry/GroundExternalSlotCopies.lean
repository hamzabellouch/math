import OAI.SetTheory.PartitionPrinciple.Definability.ExternalSlotCopyGraphs
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundExternalBirthLayers

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula SetRealization Compression Compression.RecursiveMaps.CosetGeometry
universe u

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalSlotCopyRelation (P r μ A j : ZFSet.{u}) : ZFSet.{u} :=
  externalSlotCopyGraph
    (M.externalStarVertices G (externalChildLetters I P (externalRectangles P G r μ A))
      (externalRequestCarrier I P (externalRectangles P G r μ A)) m one)
    (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (externalRequestCarrier I P (externalRectangles P G r μ A))
    (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    (completion.externalPointAction P r μ A) (completion.localTileVertexImages P r μ A) j

noncomputable def externalSlotCopyMaps (P r μ A Active j : ZFSet.{u}) : ZFSet.{u} :=
  M.indexedRelationSections Active (completion.algebra.union.fields 0)
    (completion.externalPointCarrier P r μ A) (completion.externalSlotCopyRelation P r μ A j)
end GroundCompressionCompletion

namespace GroundExternalGeometryInputs
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
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "vcode" => completion.externalFamilyVertexCode group oldAction data.original
local notation "R(" j ")" => completion.externalSlotCopyRelation P0 r0 μ0 A0 j
include data group oldAction pairing unions powers separation infinite hG

theorem externalSlotCopyRelation_ground (hP0 : P0 ∈ M.sets) {j : ZFSet.{u}} (hj : j ∈ M.sets) :
    R(j) ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have localGround := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  exact M.externalSlotCopyGraph_mem pairing unions powers separation
    (data.externalStarCarriers_ground pairing unions powers separation hG).1 data.group.carrier_mem
    data.words.requests_ground (completion.algebra.union.ground 0) geometry.carrier_ground
    geometry.action_ground localGround.2.2.2.1 hj

theorem externalSlotCopyRelation_entry :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index)
      (i : Option ((family).Child r)) (x : SetMembers U) (y : (family).Node (action)),
      ZFSet.pair (ZFSet.pair ((vpres).encode (.inr (w, r))) (SetMembers.raw x)) ((q).encode y) ∈ R(vcode r i) ↔
        ((family).placedTile (action) w r).toFun (((family).flatVertex r i).toFun x) = y := by
  let := group.toGroup
  intro w r i x y
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vc := (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1
  have acted := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1
  rw [GroundCompressionCompletion.externalSlotCopyRelation, triple_mem_externalSlotCopyGraph]
  constructor
  · rintro ⟨_, _, _, w', _, r', _, z, hz, equal, copied, moved⟩
    change ZFSet.pair (natSetCode 1) (ZFSet.pair ((s).encode w) (externalRequestIndexCode r)) =
      ZFSet.pair (natSetCode 1) (ZFSet.pair w' r') at equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).2
    obtain ⟨z, rfl⟩ := ((q).mem_carrier z).1 (qc.symm ▸ hz)
    have copied' := (data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG
      r i x z).1 copied
    have moved' := (acted w z y).1 moved
    rw [← copied', ← (family).flatVertex_copy, (family).translate_tile, mul_one] at moved'
    exact moved'
  · intro equal
    refine ⟨vc ▸ (vpres).encode_mem _, SetMembers.raw_mem x, qc ▸ (q).encode_mem _,
      (s).encode w, sc ▸ (s).encode_mem _, externalRequestIndexCode r,
      (externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem _,
      (q).encode (((family).placedTile (action) 1 r).toFun (((family).flatVertex r i).toFun x)),
      qc ▸ (q).encode_mem _, rfl, ?_, ?_⟩
    · apply (data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG r i x _).2
      exact ((family).flatVertex_copy (action) 1 r i x).symm
    · apply (acted w _ _).2
      rw [(family).translate_tile, mul_one]
      exact equal

theorem externalSlotCopySection_eq :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index) (i : Option ((family).Child r)),
      indexedRelationSection U B R(vcode r i) ((vpres).encode (.inr (w, r))) =
        completion.externalCopyGraph P0 r0 μ0 A0 ((s).encode ((family).flatWord w r i)) := by
  let := group.toGroup
  intro w r i
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  rw [data.externalCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG]
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, hx, y, hy, rfl, copied⟩ := (mem_indexedRelationSection _ _ _ _ _).1 entry
    obtain ⟨y, rfl⟩ := ((q).mem_carrier y).1 (qc.symm ▸ hy)
    let x' := SetMembers.ofMem x hx
    have image := (data.externalSlotCopyRelation_entry group oldAction pairing unions powers separation infinite hG
      w r i x' y).1 (by simpa only [x', SetMembers.raw_ofMem] using copied)
    rw [(family).flatVertex_copy] at image
    have result := ((SetMembers.presentation U).pair_mem_graph (q) _ x' y).2 image
    simpa only [SetMembers.presentation, x', SetMembers.raw_ofMem] using result
  · intro entry
    obtain ⟨x, rfl⟩ := ((SetMembers.presentation U).mem_graph (q) _ z).1 entry
    apply (pair_mem_indexedRelationSection _ _ _ _ _ _).2
    refine ⟨SetMembers.raw_mem x, qc ▸ (q).encode_mem _, ?_⟩
    exact (data.externalSlotCopyRelation_entry group oldAction pairing unions powers separation infinite hG
      w r i x _).2 ((family).flatVertex_copy (action) w r i x)

theorem externalSlotCopyMaps_spec (hP0 : P0 ∈ M.sets) {Active j : ZFSet.{u}}
    (hActive : Active ∈ M.sets) (hj : j ∈ M.sets) :
    completion.externalSlotCopyMaps P0 r0 μ0 A0 Active j ∈ M.sets ∧
      ZFSet.IsFunc Active (M.groundRelations U B) (completion.externalSlotCopyMaps P0 r0 μ0 A0 Active j) ∧
      ∀ v e, ZFSet.pair v e ∈ completion.externalSlotCopyMaps P0 r0 μ0 A0 Active j ↔
        v ∈ Active ∧ e = indexedRelationSection U B R(j) v := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  exact M.indexedRelationSections_spec pairing unions powers separation hActive
    (completion.algebra.union.ground 0) geometry.carrier_ground
    (data.externalSlotCopyRelation_ground group oldAction pairing unions powers separation infinite hG hP0 hj)

end GroundExternalGeometryInputs

end PartitionPilot.Forcing

end OAI
