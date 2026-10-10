import OAI.SetTheory.PartitionPrinciple.Forcing.RootedSupportOwners
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalLocalHeightFamilies
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalStarOverlaps

namespace OAI



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
include data group oldAction pairing unions powers separation infinite hG

theorem externalStarSupports_iff :
    letI := group.toGroup
    ∀ (v : TileStars.Vertex (SetMembers G) (family).Letters Index) (y : (family).Node (action)),
      ZFSet.pair ((vpres).encode v) ((q).encode y) ∈ completion.externalStarSupports P0 r0 μ0 A0 ↔
        ∃ x : (family).Space v, (((family).diagram (action)).vertex v).toFun x = y := by
  let := group.toGroup
  intro v y
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have cc := data.externalCosetPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vc := (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1
  have cosets := data.externalCosetClassifier_entry_iff group oldAction pairing unions powers separation infinite hG
  have copied := data.externalPointClassifier_entry_iff group oldAction pairing unions powers separation infinite hG
  have acted := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1
  have localImage := data.localTileCarrier_image group oldAction pairing unions powers separation infinite hG
  rw [GroundCompressionCompletion.externalStarSupports, pair_mem_externalStarSupportGraph]
  constructor
  · rintro ⟨_, _, body⟩
    cases v with
    | inl coset =>
      rcases body with cosetBody | tileBody
      · obtain ⟨c', _, w, hw, x, hx, equal, classified, image⟩ := cosetBody
        change ZFSet.pair (natSetCode 0) ((c).encode coset) = ZFSet.pair (natSetCode 0) c' at equal
        obtain rfl : (c).encode coset = c' := (ZFSet.pair_inj.1 equal).2
        obtain ⟨w, rfl⟩ := ((s).mem_carrier w).1 (sc.symm ▸ hw)
        have atCoset := (cosets w coset).1 classified
        obtain rfl := atCoset
        let x' := SetMembers.ofMem x hx
        refine ⟨((action).chart w).toFun x', ?_⟩
        exact (copied w x' y).1 (by simpa only [x', SetMembers.raw_ofMem] using image)
      · obtain ⟨_, _, _, _, _, _, equal, _⟩ := tileBody
        change ZFSet.pair (natSetCode 0) _ = ZFSet.pair (natSetCode 1) _ at equal
        exact False.elim (Nat.zero_ne_one (natSetCode_injective (ZFSet.pair_inj.1 equal).1))
    | inr wr =>
      rcases wr with ⟨w, r⟩
      rcases body with cosetBody | tileBody
      · obtain ⟨_, _, _, _, _, _, equal, _⟩ := cosetBody
        change ZFSet.pair (natSetCode 1) _ = ZFSet.pair (natSetCode 0) _ at equal
        exact False.elim (Nat.zero_ne_one (natSetCode_injective (ZFSet.pair_inj.1 equal).1.symm))
      · obtain ⟨w', _, r', _, x, hx, equal, localEntry, actionEntry⟩ := tileBody
        change ZFSet.pair (natSetCode 1) (ZFSet.pair ((s).encode w) (externalRequestIndexCode r)) =
          ZFSet.pair (natSetCode 1) (ZFSet.pair w' r') at equal
        obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).2
        obtain ⟨x', rfl⟩ := (localImage r x).1 ((mem_relationFiber _ _ _ _).2 ⟨hx, localEntry⟩)
        have translated := (acted w (((family).placedTile (action) 1 r).toFun x') y).1 actionEntry
        rw [(family).translate_tile, mul_one] at translated
        exact ⟨x', translated⟩
  · rintro ⟨x, image⟩
    refine ⟨vc ▸ (vpres).encode_mem v, qc ▸ (q).encode_mem y, ?_⟩
    cases v with
    | inl coset =>
      obtain ⟨w, rfl⟩ := representative_exists (SetMembers G) (family).Letters coset
      apply Or.inl
      let z := ((action).chart w).inverse x
      refine ⟨(c).encode (point (SetMembers G) (family).Letters w), cc ▸ (c).encode_mem _,
        (s).encode w, sc ▸ (s).encode_mem w, SetMembers.raw z, SetMembers.raw_mem z, rfl,
        (cosets _ _).2 rfl, (copied w z y).2 ?_⟩
      change (((family).diagram (action)).vertex (.inl (point (SetMembers G) (family).Letters w))).toFun
        (((action).chart w).toFun (((action).chart w).inverse x)) = y
      erw [((action).chart w).right_inverse]
      exact image
    | inr wr =>
      rcases wr with ⟨w, r⟩
      apply Or.inr
      let z := ((family).placedTile (action) 1 r).toFun x
      have localEntry := (mem_relationFiber _ _ _ _).1 ((localImage r ((q).encode z)).2 ⟨x, rfl⟩)
      refine ⟨(s).encode w, sc ▸ (s).encode_mem w, externalRequestIndexCode r,
        (externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem r,
        (q).encode z, qc ▸ (q).encode_mem z, rfl, localEntry.2, (acted w z y).2 ?_⟩
      change (family).translate (action) w (((family).placedTile (action) 1 r).toFun x) = y
      erw [(family).translate_tile, mul_one]
      exact image

theorem externalStarSupport_iff :
    letI := group.toGroup
    ∀ (v : TileStars.Vertex (SetMembers G) (family).Letters Index) (y : (family).Node (action)),
      (q).encode y ∈ completion.externalStarSupport P0 r0 μ0 A0 ((vpres).encode v) ↔
        ∃ x : (family).Space v, (((family).diagram (action)).vertex v).toFun x = y := by
  let := group.toGroup
  intro v y
  rw [GroundCompressionCompletion.externalStarSupport, mem_relationFiber,
    data.externalStarSupports_iff group oldAction pairing unions powers separation infinite hG]
  exact and_iff_right (data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG ▸ (q).encode_mem y)

end PartitionPilot.Forcing.GroundExternalGeometryInputs




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
include data group oldAction pairing unions powers separation infinite hG

theorem externalStarOverlaps_iff :
    letI := group.toGroup
    ∀ (v : TileStars.Vertex (SetMembers G) (family).Letters Index) (y : (family).Node (action)),
      ZFSet.pair ((vpres).encode v) ((q).encode y) ∈ completion.externalStarOverlaps P0 r0 μ0 A0 ↔
        (∃ x : (family).Space v, (((family).diagram (action)).vertex v).toFun x = y) ∧
        (∃ x : (family).Space (TileStars.parent (SetMembers G) (family).Letters Index Sigma.fst v),
          (((family).diagram (action)).vertex (TileStars.parent (SetMembers G) (family).Letters Index Sigma.fst v)).toFun x = y) := by
  let := group.toGroup
  intro v y
  have parent := (data.externalStarParent_iff group oldAction pairing unions powers separation infinite hG v _).2 rfl
  have function := (data.externalStarParent_ground_function group oldAction pairing unions powers separation infinite hG).2
  rw [GroundCompressionCompletion.externalStarOverlaps, pair_mem_parentSupportGraph_of_parent function parent,
    data.externalStarSupports_iff group oldAction pairing unions powers separation infinite hG,
    data.externalStarSupports_iff group oldAction pairing unions powers separation infinite hG]
  exact and_iff_right (data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG ▸ (q).encode_mem y)

theorem externalStarFresh_iff :
    letI := group.toGroup
    ∀ (v : TileStars.Vertex (SetMembers G) (family).Letters Index) (y : (family).Node (action)),
      ZFSet.pair ((vpres).encode v) ((q).encode y) ∈ completion.externalStarFresh P0 r0 μ0 A0 ↔
        (∃ x : (family).Space v, (((family).diagram (action)).vertex v).toFun x = y) ∧
        ¬ (∃ x : (family).Space (TileStars.parent (SetMembers G) (family).Letters Index Sigma.fst v),
          (((family).diagram (action)).vertex (TileStars.parent (SetMembers G) (family).Letters Index Sigma.fst v)).toFun x = y) := by
  let := group.toGroup
  intro v y
  rw [GroundCompressionCompletion.externalStarFresh, pair_mem_freshSupportGraph]
  change (ZFSet.pair ((vpres).encode v) ((q).encode y) ∈ completion.externalStarSupports P0 r0 μ0 A0 ∧
    ZFSet.pair ((vpres).encode v) ((q).encode y) ∉ completion.externalStarOverlaps P0 r0 μ0 A0) ↔ _
  rw [data.externalStarSupports_iff group oldAction pairing unions powers separation infinite hG,
    data.externalStarOverlaps_iff group oldAction pairing unions powers separation infinite hG]
  tauto

theorem externalStarOverlaps_vertex_iff :
    letI := group.toGroup
    ∀ (v : TileStars.Vertex (SetMembers G) (family).Letters Index)
      (nonzero : ((family).diagram (action)).scheme.depth v ≠ 0) (x : (family).Space v),
      ZFSet.pair ((vpres).encode v) ((q).encode ((((family).diagram (action)).vertex v).toFun x)) ∈
        completion.externalStarOverlaps P0 r0 μ0 A0 ↔
        (((family).diagram (action)).scheme.order v).le x (((family).diagram (action)).scheme.childAnchor v nonzero) := by
  let := group.toGroup
  intro v nonzero x
  erw [data.externalStarOverlaps_iff group oldAction pairing unions powers separation infinite hG]
  exact ⟨fun h => (((family).diagram (action)).scheme.supports_parent_iff v nonzero x).1 h.2,
    fun h => ⟨⟨x, rfl⟩, (((family).diagram (action)).scheme.supports_parent_iff v nonzero x).2 h⟩⟩

theorem externalStarFresh_vertex_iff :
    letI := group.toGroup
    ∀ (v : TileStars.Vertex (SetMembers G) (family).Letters Index)
      (nonzero : ((family).diagram (action)).scheme.depth v ≠ 0) (x : (family).Space v),
      ZFSet.pair ((vpres).encode v) ((q).encode ((((family).diagram (action)).vertex v).toFun x)) ∈
        completion.externalStarFresh P0 r0 μ0 A0 ↔
        ¬ (((family).diagram (action)).scheme.order v).le x (((family).diagram (action)).scheme.childAnchor v nonzero) := by
  let := group.toGroup
  intro v nonzero x
  rw [GroundCompressionCompletion.externalStarFresh, pair_mem_freshSupportGraph]
  change (ZFSet.pair ((vpres).encode v) ((q).encode ((((family).diagram (action)).vertex v).toFun x)) ∈
    completion.externalStarSupports P0 r0 μ0 A0 ∧
    ZFSet.pair ((vpres).encode v) ((q).encode ((((family).diagram (action)).vertex v).toFun x)) ∉
      completion.externalStarOverlaps P0 r0 μ0 A0) ↔ _
  erw [data.externalStarSupports_iff group oldAction pairing unions powers separation infinite hG,
    data.externalStarOverlaps_vertex_iff group oldAction pairing unions powers separation infinite hG]
  exact and_iff_right ⟨x, rfl⟩

theorem externalStarFresh_root :
    letI := group.toGroup
    ∀ y : (family).Node (action),
      ZFSet.pair ((vpres).encode (TileStars.root (SetMembers G) (family).Letters Index)) ((q).encode y) ∉
        completion.externalStarFresh P0 r0 μ0 A0 := by
  let := group.toGroup
  intro y entry
  have parts := (data.externalStarFresh_iff group oldAction pairing unions powers separation infinite hG _ y).1 entry
  erw [TileStars.parent_root] at parts
  exact parts.2 parts.1

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end OAI
