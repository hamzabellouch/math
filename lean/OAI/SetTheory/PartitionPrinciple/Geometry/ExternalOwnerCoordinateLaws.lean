import OAI.SetTheory.PartitionPrinciple.Definability.ExternalStarOverlapRealization
import OAI.SetTheory.PartitionPrinciple.Definability.ExternalTileCoordinateRealization
import OAI.SetTheory.PartitionPrinciple.Definability.LeastSlotOwnerCodes
import OAI.SetTheory.PartitionPrinciple.Definability.RootedSupportOwnerFunction
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundExternalOldAction
import OAI.SetTheory.PartitionPrinciple.Forcing.RequestedSupportOwners

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (P r μ A : ZFSet.{u})
noncomputable def externalIdentityCopyGraph : ZFSet.{u} :=
  completion.externalCopyGraph P r μ A
    (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
noncomputable def externalSeedCarrier : ZFSet.{u} :=
  relationImage (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    (completion.externalIdentityCopyGraph P r μ A)
noncomputable def externalSeedHeight (C D seed : ZFSet.{u}) : ZFSet.{u} :=
  pushedHeightGraph (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    (ZFSet.prod C D) (completion.externalIdentityCopyGraph P r μ A) seed

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
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "E" => completion.externalIdentityCopyGraph P0 r0 μ0 A0
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "family" => completion.externalFamily group oldAction data.original
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG

theorem externalIdentityCopyGraph_eq_graph :
    letI := group.toGroup
    E = (SetMembers.presentation U).graph (q) ((family).copy (action) 1).toFun := by
  let := group.toGroup
  have equal := data.externalCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG 1
  rw [← completion.externalFamilyGroupPresentation_identity group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground] at equal
  exact equal

theorem externalSeedCarrier_iff :
    letI := group.toGroup
    ∀ y, (q).encode y ∈ P ↔ ∃ x : SetMembers U, ((family).copy (action) 1).toFun x = y := by
  let := group.toGroup
  intro y
  rw [GroundCompressionCompletion.externalSeedCarrier, mem_relationImage,
    data.externalIdentityCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG]
  constructor
  · rintro ⟨_, x, hx, entry⟩
    let a := SetMembers.ofMem x hx
    refine ⟨a, ((SetMembers.presentation U).pair_mem_graph (q) _ a y).1 ?_⟩
    change ZFSet.pair (SetMembers.raw a) ((q).encode y) ∈ _
    simpa only [a, SetMembers.raw_ofMem] using entry
  · rintro ⟨x, equal⟩
    exact ⟨data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG ▸ (q).encode_mem y,
      SetMembers.raw x, SetMembers.raw_mem x, ((SetMembers.presentation U).pair_mem_graph (q) _ x y).2 equal⟩

include data group oldAction pairing unions powers separation infinite hG in
theorem externalSeedHeights_spec (hP0 : P0 ∈ M.sets) {C D rD original : ZFSet.{u}}
    (heights : GroundCompressionHeightData M initial I Sources Reps G m one T completion.algebra.union P0 C D rD original)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) :
    P ∈ M.sets ∧ completion.externalSeedHeight P0 r0 μ0 A0 C D heights.height ∈ M.sets ∧
      StrictLexHeightCode P C D (completion.externalPointOrder P0 r0 μ0 A0)
        (completion.externalSeedHeight P0 r0 μ0 A0 C D heights.height) rD ∧
      relationImage P (ZFSet.prod C D) (completion.externalSeedHeight P0 r0 μ0 A0 C D heights.height) =
        relationImage U (ZFSet.prod C D) heights.height ∧
      M.groundEmbeddable (relationImage P (ZFSet.prod C D)
        (completion.externalSeedHeight P0 r0 μ0 A0 C D heights.height)) ZFSet.omega := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have copyGround := geometry.copies_ground _ data.group.group_code.identity_mem
  have copy := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have range := pushedHeightGraph_range copy.injection heights.code.function
  refine ⟨M.relationImage_mem separation (completion.algebra.union.ground 0) geometry.carrier_ground copyGround,
    M.pushedHeightGraph_mem pairing unions powers separation (completion.algebra.union.ground 0)
      geometry.carrier_ground (M.prod_mem pairing unions powers separation hC hD) copyGround heights.height_ground,
    pushedHeightGraph_strictLex copy heights.code, range, ?_⟩
  exact range.symm ▸ heights.range_countable

theorem externalSeedHeight_entry {C D rD original : ZFSet.{u}}
    (heights : GroundCompressionHeightData M initial I Sources Reps G m one T completion.algebra.union P0 C D rD original) :
    letI := group.toGroup
    ∀ x y, ZFSet.pair ((q).encode (((family).copy (action) 1).toFun x)) y ∈
      completion.externalSeedHeight P0 r0 μ0 A0 C D heights.height ↔
        ZFSet.pair (SetMembers.raw x) y ∈ heights.height := by
  let := group.toGroup
  intro x y
  have copy := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  apply pushedHeightGraph_entry copy.injection heights.code.function
  change ZFSet.pair (SetMembers.raw x) ((q).encode (((family).copy (action) 1).toFun x)) ∈ E
  rw [data.externalIdentityCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG]
  exact ((SetMembers.presentation U).pair_mem_graph (q) _ x _).2 rfl

end GroundExternalGeometryInputs



namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
noncomputable def externalStarOwner (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  leastSupportGraph
    (M.externalStarVertices G (externalChildLetters I P (externalRectangles P G r μ A))
      (externalRequestCarrier I P (externalRectangles P G r μ A)) m one)
    (completion.externalPointCarrier P r μ A)
    (M.externalStarDepth G (externalChildLetters I P (externalRectangles P G r μ A))
      (externalRequestCarrier I P (externalRectangles P G r μ A)) m one)
    (completion.externalStarSupports P r μ A)

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
local notation "rectangles" => externalRectangles P0 G r0 μ0 A0
local notation "letters" => externalChildLetters I P0 rectangles
local notation "requests" => externalRequestCarrier I P0 rectangles
local notation "family" => completion.externalFamily group oldAction data.original
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "scheme" => TileStars.Spaces.scheme
  (Compression.RecursiveMaps.TileRequests.Family.diagram (family) (action))
local notation "sVertex" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG

theorem externalStarOwner_iff :
    letI := group.toGroup
    ∀ x v, ZFSet.pair ((q).encode x) ((sVertex).encode v) ∈ completion.externalStarOwner P0 r0 μ0 A0 ↔
      (scheme).LeastSupport v x := by
  let := group.toGroup
  intro x v
  have entry := leastSupportGraph_entry (sVertex) (q) (scheme).depth (scheme).Supports
    (data.externalStarDepth_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStarSupports_iff group oldAction pairing unions powers separation infinite hG) x v
  rw [(data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1,
    data.externalPointPresentation_carrier] at entry
  exact entry

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarOwner_ground_function (hP0 : P0 ∈ M.sets) :
    completion.externalStarOwner P0 r0 μ0 A0 ∈ M.sets ∧
      ZFSet.IsFunc (completion.externalPointCarrier P0 r0 μ0 A0)
        (M.externalStarVertices G letters requests m one) (completion.externalStarOwner P0 r0 μ0 A0) := by
  let := group.toGroup
  have vertices := (data.externalStarCarriers_ground pairing unions powers separation hG).1
  have points := (data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0).carrier_ground
  have depths := (data.externalStarDepth_ground_function group oldAction pairing unions powers separation infinite hG).1
  have supports := data.externalStarSupports_ground group oldAction pairing unions powers separation infinite hG hP0
  refine ⟨M.leastSupportGraph_mem pairing unions powers separation infinite vertices points depths supports, ?_⟩
  have function := leastSupportGraph_function (sVertex) (q) (scheme).depth (scheme).Supports
    (data.externalStarDepth_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStarSupports_iff group oldAction pairing unions powers separation infinite hG)
    (scheme).existsUnique_leastSupport
  rw [(data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1,
    data.externalPointPresentation_carrier] at function
  exact function

end GroundExternalGeometryInputs
end PartitionPilot.Forcing




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
local notation "rectangles" => externalRectangles P0 G r0 μ0 A0
local notation "letters" => externalChildLetters I P0 rectangles
local notation "requests" => externalRequestCarrier I P0 rectangles
local notation "family" => completion.externalFamily group oldAction data.original
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "scheme" => TileStars.Spaces.scheme
  (Compression.RecursiveMaps.TileRequests.Family.diagram (family) (action))
local notation "sVertex" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "oldCopy" => completion.externalCopyGraph P0 r0 μ0 A0 (M.externalGroupIdentity G letters m one)
local notation "oldImage" => relationImage U Q oldCopy

theorem externalStarOwner_subset : completion.externalStarOwner P0 r0 μ0 A0 ⊆
    ZFSet.prod Q (M.externalStarVertices G letters requests m one) := by
  intro z hz
  unfold GroundCompressionCompletion.externalStarOwner leastSupportGraph at hz
  exact (ZFSet.mem_sep.1 hz).1

theorem externalStarOwner_value_iff :
    letI := group.toGroup
    ∀ x v, ZFSet.pair ((q).encode x) ((sVertex).encode v) ∈ completion.externalStarOwner P0 r0 μ0 A0 ↔
      (scheme).owner x = v := by
  let := group.toGroup
  intro x v
  exact (data.externalStarOwner_iff group oldAction pairing unions powers separation infinite hG x v).trans
    ((scheme).owner_eq_iff x v).symm

theorem externalStarOwner_eq_graph :
    letI := group.toGroup
    completion.externalStarOwner P0 r0 μ0 A0 = (q).graph (sVertex) (scheme).owner := by
  let := group.toGroup
  apply presentedGraph_eq (q) (sVertex) (scheme).owner
  · rw [data.externalPointPresentation_carrier,
      (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1]
    exact externalStarOwner_subset
  · exact data.externalStarOwner_value_iff group oldAction pairing unions powers separation infinite hG

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarOwner_order_depth {x y v w : ZFSet.{u}} {n k : Nat}
    (lower : ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0)
    (first : ZFSet.pair x v ∈ completion.externalStarOwner P0 r0 μ0 A0)
    (second : ZFSet.pair y w ∈ completion.externalStarOwner P0 r0 μ0 A0)
    (firstDepth : ZFSet.pair v (natSetCode n) ∈ M.externalStarDepth G letters requests m one)
    (secondDepth : ZFSet.pair w (natSetCode k) ∈ M.externalStarDepth G letters requests m one) :
    n ≤ k ∧ (n = k → v = w) := by
  let := group.toGroup
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vc := (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1
  have firstShape := ZFSet.pair_mem_prod.1 (externalStarOwner_subset first)
  have secondShape := ZFSet.pair_mem_prod.1 (externalStarOwner_subset second)
  obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ firstShape.1)
  obtain ⟨y, rfl⟩ := ((q).mem_carrier y).1 (qc.symm ▸ secondShape.1)
  obtain ⟨v, rfl⟩ := ((sVertex).mem_carrier v).1 (vc.symm ▸ firstShape.2)
  obtain ⟨w, rfl⟩ := ((sVertex).mem_carrier w).1 (vc.symm ▸ secondShape.2)
  have firstOwner := (data.externalStarOwner_iff group oldAction pairing unions powers separation infinite hG x v).1 first
  have secondOwner := (data.externalStarOwner_iff group oldAction pairing unions powers separation infinite hG y w).1 second
  have order := ((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).1 x y).1 lower
  have hn := (data.externalStarDepth_iff group oldAction pairing unions powers separation infinite hG v n).1 firstDepth
  have hk := (data.externalStarDepth_iff group oldAction pairing unions powers separation infinite hG w k).1 secondDepth
  refine ⟨?_, ?_⟩
  · rw [hn, hk]
    exact (scheme).leastSupport_depth_mono firstOwner secondOwner order
  · intro same
    exact congrArg (sVertex).encode ((scheme).leastSupport_eq_of_depth_eq firstOwner secondOwner order
      (hn.symm.trans (same.trans hk)))

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarOwner_root_iff :
    ∀ x, ZFSet.pair x (M.externalStarRoot G letters m one) ∈ completion.externalStarOwner P0 r0 μ0 A0 ↔
      x ∈ oldImage := by
  let := group.toGroup
  intro x
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have rootEq := data.externalStarRoot_eq_encode group oldAction pairing unions powers separation infinite hG
  have identity := completion.externalFamilyGroupPresentation_identity group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have copies := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.2
  constructor
  · intro entry
    have hx := (ZFSet.pair_mem_prod.1 (externalStarOwner_subset entry)).1
    obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ hx)
    rw [rootEq, data.externalStarOwner_iff group oldAction pairing unions powers separation infinite hG] at entry
    obtain ⟨a, image⟩ := ((family).leastSupport_root_copy_iff (action) x).1 entry
    refine (mem_relationImage _ _ _ _).2 ⟨hx, SetMembers.raw a, SetMembers.raw_mem a, ?_⟩
    have copyEntry := (copies 1 a x).2 image
    rw [← identity] at copyEntry
    exact copyEntry
  · intro hx
    obtain ⟨member, a, ha, entry⟩ := (mem_relationImage _ _ _ _).1 hx
    obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ member)
    let a' := SetMembers.ofMem a ha
    have copyEntry : ZFSet.pair (SetMembers.raw a') ((q).encode x) ∈
        completion.externalCopyGraph P0 r0 μ0 A0 ((sGroup).encode 1) := by
      simpa only [identity, a', SetMembers.raw_ofMem] using entry
    have image := (copies 1 a' x).1 copyEntry
    rw [rootEq, data.externalStarOwner_iff group oldAction pairing unions powers separation infinite hG]
    exact ((family).leastSupport_root_copy_iff (action) x).2 ⟨a', image⟩

theorem externalStarOwner_fresh_tile :
    letI := group.toGroup
    ∀ x v, ZFSet.pair x v ∈ completion.externalStarOwner P0 r0 μ0 A0 → x ∉ oldImage →
      ∃ w r, ∃ y : ((family).tile r).Space,
        v = (sVertex).encode (.inr (w, r)) ∧ x = (q).encode (((family).placedTile (action) w r).toFun y) ∧
        ¬ ((family).tile r).order.le y
          (((family).diagram (action)).localGlue (.inr (w, r)) ((family).tile_depth_ne_zero (action) w r)).rightAnchor := by
  let := group.toGroup
  intro x v entry fresh
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vc := (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1
  have shape := ZFSet.pair_mem_prod.1 (externalStarOwner_subset entry)
  obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ shape.1)
  obtain ⟨v, rfl⟩ := ((sVertex).mem_carrier v).1 (vc.symm ▸ shape.2)
  have least := (data.externalStarOwner_iff group oldAction pairing unions powers separation infinite hG x v).1 entry
  rcases (family).leastSupport_cases (action) v x least with ⟨rfl, _⟩ | ⟨w, r, y, rfl, eq, outside⟩
  · apply False.elim
    apply fresh
    apply (data.externalStarOwner_root_iff group oldAction pairing unions powers separation infinite hG _).1
    rw [data.externalStarRoot_eq_encode group oldAction pairing unions powers separation infinite hG]
    exact entry
  · exact ⟨w, r, y, rfl, congrArg (q).encode eq.symm, outside⟩

end PartitionPilot.Forcing.GroundExternalGeometryInputs



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
local notation "rectangles" => externalRectangles P0 G r0 μ0 A0
local notation "letters" => externalChildLetters I P0 rectangles
local notation "requests" => externalRequestCarrier I P0 rectangles
local notation "family" => completion.externalFamily group oldAction data.original
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "scheme" => TileStars.Spaces.scheme
  (Compression.RecursiveMaps.TileRequests.Family.diagram (family) (action))
local notation "sVertex" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "oldCopy" => completion.externalCopyGraph P0 r0 μ0 A0 (M.externalGroupIdentity G letters m one)
local notation "oldImage" => relationImage U Q oldCopy
local notation "seedCarrier" => completion.externalSeedCarrier P0 r0 μ0 A0

include data group oldAction pairing unions powers separation infinite hG

theorem externalStarOwner_seed_iff (x : ZFSet.{u}) :
    ZFSet.pair x (M.externalStarRoot G letters m one) ∈ completion.externalStarOwner P0 r0 μ0 A0 ↔
      x ∈ seedCarrier :=
  data.externalStarOwner_root_iff group oldAction pairing unions powers separation infinite hG x

theorem externalSeedCarrier_lower {x y : ZFSet.{u}} (hx : x ∈ Q) (hy : y ∈ seedCarrier)
    (lower : ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0) : x ∈ seedCarrier := by
  have ideal := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  obtain ⟨_, a, _, entry⟩ := (mem_relationImage _ _ _ _).1 hy
  obtain ⟨b, hb, _, image⟩ := ideal.ideal a y x entry hx lower
  exact (mem_relationImage _ _ _ _).2 ⟨hx, b, hb, image⟩

theorem externalSeedCarrier_no_new_below {x y : ZFSet.{u}} (hx : x ∈ Q)
    (fresh : x ∉ seedCarrier) (old : y ∈ seedCarrier) :
    ZFSet.pair x y ∉ completion.externalPointOrder P0 r0 μ0 A0 :=
  fun lower => fresh (data.externalSeedCarrier_lower group oldAction pairing unions powers separation infinite hG hx old lower)

theorem externalStarOwner_order {x y v w n k : ZFSet.{u}}
    (lower : ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0)
    (first : ZFSet.pair x v ∈ completion.externalStarOwner P0 r0 μ0 A0)
    (second : ZFSet.pair y w ∈ completion.externalStarOwner P0 r0 μ0 A0)
    (firstDepth : ZFSet.pair v n ∈ M.externalStarDepth G letters requests m one)
    (secondDepth : ZFSet.pair w k ∈ M.externalStarDepth G letters requests m one) :
    (n = k ∨ n ∈ k) ∧ (n = k → v = w) := by
  have depthFunction := (data.externalStarDepth_ground_function group oldAction pairing unions powers separation infinite hG).2
  have hn := (ZFSet.pair_mem_prod.1 (depthFunction.1 firstDepth)).2
  have hk := (ZFSet.pair_mem_prod.1 (depthFunction.1 secondDepth)).2
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
  have laws := data.externalStarOwner_order_depth group oldAction pairing unions powers separation infinite hG
    lower first second firstDepth secondDepth
  refine ⟨?_, fun same => laws.2 (natSetCode_injective same)⟩
  rcases Nat.lt_or_eq_of_le laws.1 with less | same
  · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
  · exact Or.inl (congrArg natSetCode same)

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
variable {D rD lo hi : ZFSet.{u}}
variable (heights : GroundExternalLocalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi completion)
local notation "coordinates" => heights.coordinates
local notation "localp" => data.localTilePresentation group oldAction pairing unions powers separation infinite hG
include data group oldAction pairing unions powers separation infinite hG

theorem externalTileCoordinates_support :
    letI := group.toGroup
    ∀ v x d, ZFSet.pair (ZFSet.pair v x) d ∈ coordinates →
      ∃ (w : External (SetMembers G) (family).Letters) (r : Index) (a : ((family).tile r).Space),
        v = (vpres).encode (.inr (w, r)) ∧ x = (q).encode (((family).placedTile (action) w r).toFun a) := by
  let := group.toGroup
  intro v x d entry
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have acted := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1
  obtain ⟨_, hx, _, w, hw, r, hr, y, _, h, _, equal, selected, acting, value⟩ :=
    (pair_mem_transportedTileCoordinates _ _ _ _ _ _ _ _ _ _).1 entry
  obtain ⟨w, rfl⟩ := ((s).mem_carrier w).1 (sc.symm ▸ hw)
  obtain ⟨r, rfl⟩ := ((externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).mem_carrier r).1 hr
  have code := (heights.values _ _ selected).2.1
  have localMember := (ZFSet.pair_mem_prod.1 (code.function.1 value)).1
  obtain ⟨a, rfl⟩ := (data.localTileCarrier_image group oldAction pairing unions powers separation infinite hG r y).1 localMember
  obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ hx)
  have translated := (acted w (((family).placedTile (action) 1 r).toFun a) x).1 acting
  rw [(family).translate_tile, mul_one] at translated
  exact ⟨w, r, a, equal, congrArg (q).encode translated.symm⟩

include heights in
theorem externalTileCoordinates_owner_total :
    ∀ x ∈ Q, x ∉ completion.externalSeedCarrier P0 r0 μ0 A0 → ∀ v,
      ZFSet.pair x v ∈ completion.externalStarOwner P0 r0 μ0 A0 →
      ∃ d ∈ D, ZFSet.pair (ZFSet.pair v x) d ∈ coordinates := by
  let := group.toGroup
  intro x _ fresh v owner
  obtain ⟨w, r, a, rfl, rfl, _⟩ :=
    data.externalStarOwner_fresh_tile group oldAction pairing unions powers separation infinite hG x v owner fresh
  exact data.externalTileCoordinates_total group oldAction pairing unions powers separation infinite hG heights w r a

include heights in
theorem externalTileCoordinates_raw_strict :
    ∀ v x y a b, ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0 → x ≠ y →
      ZFSet.pair (ZFSet.pair v x) a ∈ coordinates →
      ZFSet.pair (ZFSet.pair v y) b ∈ coordinates → ZFSet.pair a b ∈ rD := by
  let := group.toGroup
  intro v x y a b lower distinct first second
  obtain ⟨w, r, x', rfl, rfl⟩ :=
    data.externalTileCoordinates_support group oldAction pairing unions powers separation infinite hG heights v x a first
  obtain ⟨w', r', y', sameVertex, samePoint⟩ :=
    data.externalTileCoordinates_support group oldAction pairing unions powers separation infinite hG heights _ y b second
  have same := Sum.inr.inj ((vpres).injective sameVertex)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  subst y
  have localLower := (((family).placedTile (action) w r).le_iff x' y').1
    (((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).1 _ _).1 lower)
  have localDistinct : x' ≠ y' := fun equal => distinct (congrArg
    (fun z => (q).encode (((family).placedTile (action) w r).toFun z)) equal)
  exact data.externalTileCoordinates_strict group oldAction pairing unions powers separation infinite hG
    heights w r x' y' localDistinct localLower a b first second

end PartitionPilot.Forcing.GroundExternalGeometryInputs



namespace PartitionPilot.Forcing
universe u
namespace GroundExternalLocalHeightData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (localHeights : GroundExternalLocalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 D rD lo hi completion)

noncomputable def externalHeightGraph (C seed columns : ZFSet.{u}) : ZFSet.{u} :=
  externalOwnerHeightGraph (completion.externalSeedCarrier P0 r0 μ0 A0)
    (completion.externalPointCarrier P0 r0 μ0 A0)
    (M.externalStarVertices G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0))
      (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)) m one) C D
    (completion.externalSeedHeight P0 r0 μ0 A0 C D seed)
    (completion.externalStarOwner P0 r0 μ0 A0)
    (M.externalStarDepth G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0))
      (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)) m one)
    columns localHeights.coordinates

end GroundExternalLocalHeightData

structure GroundExternalHeightData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) where
  localHeights : GroundExternalLocalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi completion
  columns : GroundExternalColumnData M C (heightColumns (completion.externalSeedCarrier P0 r0 μ0 A0) C D
    (completion.externalSeedHeight P0 r0 μ0 A0 C D seed))
  height_ground : localHeights.externalHeightGraph C seed columns.sequence ∈ M.sets
  code : StrictLexHeightCode (completion.externalPointCarrier P0 r0 μ0 A0) C D
    (completion.externalPointOrder P0 r0 μ0 A0) (localHeights.externalHeightGraph C seed columns.sequence) rD
  range_ground : relationImage (completion.externalPointCarrier P0 r0 μ0 A0) (ZFSet.prod C D)
    (localHeights.externalHeightGraph C seed columns.sequence) ∈ M.sets
  range_countable : M.groundEmbeddable (relationImage (completion.externalPointCarrier P0 r0 μ0 A0) (ZFSet.prod C D)
    (localHeights.externalHeightGraph C seed columns.sequence)) ZFSet.omega
  preserves_seed : ∀ x y z, ZFSet.pair x y ∈ completion.externalIdentityCopyGraph P0 r0 μ0 A0 →
    (ZFSet.pair y z ∈ localHeights.externalHeightGraph C seed columns.sequence ↔ ZFSet.pair x z ∈ seed)
  below_cap : ∀ x a d, ZFSet.pair x (ZFSet.pair a d) ∈ localHeights.externalHeightGraph C seed columns.sequence →
    a ∈ columns.cap

namespace GroundExternalHeightData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
noncomputable def height (data : GroundExternalHeightData M initial I Sources Reps G m one T τ
    P0 r0 μ0 A0 C D rD lo hi seed completion) : ZFSet.{u} :=
  data.localHeights.externalHeightGraph C seed data.columns.sequence

end GroundExternalHeightData

end PartitionPilot.Forcing

end OAI
