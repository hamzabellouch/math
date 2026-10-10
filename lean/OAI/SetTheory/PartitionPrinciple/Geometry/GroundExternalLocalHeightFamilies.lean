import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalLocalHeightSelection

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
local notation "vertices" => completion.externalFamilyTileVertexPresentation group oldAction data.original
local notation "Requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "vcode" => completion.externalFamilyVertexCode group oldAction data.original
include data group oldAction pairing unions powers separation infinite hG

theorem localTileVertexImages_entry_iff :
    letI := group.toGroup
    ∀ (r : Index) (i : Option ((family).Child r)) (x : SetMembers U) (y : (family).Node (action)),
      ZFSet.pair ((vertices).encode ⟨r, i, x⟩) ((q).encode y) ∈
        completion.localTileVertexImages P0 r0 μ0 A0 ↔
          ((family).copy (action) ((family).flatWord 1 r i)).toFun x = y := by
  let := group.toGroup
  intro r i x y
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have identity := completion.externalFamilyGroupPresentation_identity group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have placements := completion.externalPlacements_entry_iff group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have classed := data.externalPointClassifier_entry_iff group oldAction pairing unions powers separation infinite hG
  rw [GroundCompressionCompletion.localTileVertexImages, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, z, hz, placed, classified⟩
    have hz' : z ∈ ((s).product (SetMembers.presentation U)).carrier := by
      change z ∈ ZFSet.prod (s).carrier U
      rw [sc]
      exact hz
    obtain ⟨⟨w, a⟩, rfl⟩ := (((s).product (SetMembers.presentation U)).mem_carrier z).1 hz'
    have placed' := ((pair_mem_indexedRelationSection _ _ _ _ _ _).1 placed).2.2
    rw [identity] at placed'
    have same := (placements 1 ⟨r, i, x⟩ (w, a)).1 placed'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact (classed _ _ _).1 classified
  · intro equal
    let z := (((s).product (SetMembers.presentation U)).encode ((family).flatWord 1 r i, x))
    have hz : z ∈ ZFSet.prod (M.externalGroupCarrier G
        (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one) U := by
      rw [← sc]
      exact ((s).product (SetMembers.presentation U)).encode_mem _
    refine ⟨(vertices).encode_mem _, qc ▸ (q).encode_mem _, z, hz, ?_, (classed _ _ _).2 equal⟩
    apply (pair_mem_indexedRelationSection _ _ _ _ _ _).2
    refine ⟨(vertices).encode_mem _, hz, ?_⟩
    rw [identity]
    exact (placements 1 ⟨r, i, x⟩ _).2 rfl

theorem localTileCarrier_image :
    letI := group.toGroup
    ∀ (r : Index) (z : ZFSet.{u}),
      z ∈ completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r) ↔
        ∃ x : ((family).tile r).Space, (q).encode (((family).placedTile (action) 1 r).toFun x) = z := by
  let := group.toGroup
  intro r z
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vertexEntries := data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG
  constructor
  · intro hz
    obtain ⟨hzQ, domain⟩ := (mem_relationFiber _ _ _ _).1 hz
    obtain ⟨z, rfl⟩ := ((q).mem_carrier z).1 (qc.symm ▸ hzQ)
    obtain ⟨_, _, j, _, x, hx, vertex, image⟩ :=
      (pair_mem_vertexImageDomains _ _ _ _ _ _ _ _).1 domain
    have shape := (triple_mem_externalTileVertices _ _ _ _ _ _).1 vertex
    have range : j = natSetCode 0 ∨ j = natSetCode 1 ∨
        (externalRequestIndexCode r ∈ ZFSet.prod {natSetCode 2} (externalRectangles P0 G r0 μ0 A0) ∧
          j = natSetCode 2) := by tauto
    obtain ⟨i, rfl⟩ := (completion.externalFamilyVertexCode_range group oldAction data.original r j).1 range
    let x' := SetMembers.ofMem x hx
    have copied : ((family).copy (action) ((family).flatWord 1 r i)).toFun x' = z :=
      (vertexEntries r i x' z).1 (by simpa only [GroundCompressionCompletion.externalFamilyTileVertexPresentation_encode, x', SetMembers.raw_ofMem] using image)
    refine ⟨((family).flatVertex r i).toFun x', ?_⟩
    rw [(family).flatVertex_copy, copied]
  · rintro ⟨z, rfl⟩
    obtain ⟨i, x, rfl⟩ := (family).flatVertex_cover r z
    apply (mem_relationFiber _ _ _ _).2
    refine ⟨qc ▸ (q).encode_mem _, ?_⟩
    apply (pair_mem_vertexImageDomains _ _ _ _ _ _ _ _).2
    have range := (completion.externalFamilyVertexCode_range group oldAction data.original r _).2 ⟨i, rfl⟩
    have hj : vcode r i ∈ natSetCode 3 := by
      rcases range with equal | equal | ⟨_, equal⟩
      all_goals rw [equal]; exact (natSetCode_mem_iff _ 3).2 (by decide)
    refine ⟨(externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem r,
      qc ▸ (q).encode_mem _, vcode r i, hj, SetMembers.raw x, SetMembers.raw_mem x,
      (vertices).encode_mem ⟨r, i, x⟩, ?_⟩
    apply (vertexEntries r i x _).2
    exact ((family).flatVertex_copy (action) 1 r i x).symm

noncomputable def localTilePresentation (r : Index) :
    letI := group.toGroup
    Presentation (((family).tile r).Space) := by
  letI := group.toGroup
  exact {
    carrier := completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r)
    encode := fun x => (q).encode (((family).placedTile (action) 1 r).toFun x)
    injective := fun _ _ equal => embedding_injective ((family).placedTile (action) 1 r).toMeetEmbedding ((q).injective equal)
    mem_carrier := data.localTileCarrier_image group oldAction pairing unions powers separation infinite hG r }

theorem localTilePresentation_carrier (r : Index) :
    letI := group.toGroup
    (data.localTilePresentation group oldAction pairing unions powers separation infinite hG r).carrier =
      completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r) := by
  let := group.toGroup
  rfl

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
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "p" => data.localTilePresentation group oldAction pairing unions powers separation infinite hG
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "requestPresentation" => externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "vcode" => completion.externalFamilyVertexCode group oldAction data.original
include data group oldAction pairing unions powers separation infinite hG

theorem localTileOrder_iff :
    letI := group.toGroup
    ∀ (r : Index) (x y : ((family).tile r).Space),
      ZFSet.pair ((p r).encode x) ((p r).encode y) ∈
        completion.localTileOrder P0 r0 μ0 A0 (externalRequestIndexCode r) ↔
          ((family).tile r).order.le x y := by
  let := group.toGroup
  intro r x y
  have hx := (p r).encode_mem x
  have hy := (p r).encode_mem y
  have hi : externalRequestIndexCode r ∈ externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0) :=
    (requestPresentation).encode_mem r
  rw [GroundCompressionCompletion.localTileOrder, suborderFiber_pair_iff hi]
  change (_ ∧ (p r).encode x ∈ (p r).carrier ∧ (p r).encode y ∈ (p r).carrier) ↔ _
  simp only [hx, hy, and_true]
  exact ((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).1 _ _).trans
    (((family).placedTile (action) 1 r).le_iff x y)

theorem localTileMeet_iff :
    letI := group.toGroup
    ∀ (r : Index) (x y z : ((family).tile r).Space),
      ZFSet.pair (ZFSet.pair ((p r).encode x) ((p r).encode y)) ((p r).encode z) ∈
        completion.localTileMeet P0 r0 μ0 A0 (externalRequestIndexCode r) ↔
          ((family).tile r).order.meet x y = z := by
  let := group.toGroup
  intro r x y z
  have hx := (p r).encode_mem x
  have hy := (p r).encode_mem y
  have hz := (p r).encode_mem z
  have hi : externalRequestIndexCode r ∈ externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0) :=
    (requestPresentation).encode_mem r
  rw [GroundCompressionCompletion.localTileMeet, submeetFiber_triple_iff hi]
  change (_ ∧ (p r).encode x ∈ (p r).carrier ∧ (p r).encode y ∈ (p r).carrier ∧
    (p r).encode z ∈ (p r).carrier) ↔ _
  simp only [hx, hy, hz, and_true]
  refine ((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.1 _ _ _).trans ?_
  rw [← ((family).placedTile (action) 1 r).map_meet]
  exact ⟨fun equal => embedding_injective ((family).placedTile (action) 1 r).toMeetEmbedding equal,
    fun equal => congrArg _ equal⟩

omit data group oldAction pairing unions powers separation infinite hG in
theorem localTileOrder_shape (r : Index) :
    completion.localTileOrder P0 r0 μ0 A0 (externalRequestIndexCode r) ⊆
      ZFSet.prod (completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r))
        (completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r)) := by
  intro z hz
  have entry := (mem_relationFiber _ _ _ _).1 hz |>.2
  obtain ⟨_, _, x, hx, y, hy, rfl⟩ := (pair_mem_indexedSuborderGraph _ _ _ _ _ _).1 entry
  exact ZFSet.pair_mem_prod.2 ⟨hx, hy⟩

theorem localTileMeet_eq_canonical (r : Index) :
    completion.localTileMeet P0 r0 μ0 A0 (externalRequestIndexCode r) =
      canonicalMeetGraph (completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r))
        (completion.localTileOrder P0 r0 μ0 A0 (externalRequestIndexCode r)) := by
  let := group.toGroup
  have related := data.localTileOrder_iff group oldAction pairing unions powers separation infinite hG r
  have meet := data.localTileMeet_iff group oldAction pairing unions powers separation infinite hG r
  apply ZFSet.ext
  intro v
  constructor
  · intro hv
    have entry := (mem_relationFiber _ _ _ _).1 hv |>.2
    obtain ⟨_, _, x, hx, y, hy, z, hz, rfl⟩ := (pair_mem_indexedSubmeetGraph _ _ _ _ _ _).1 entry
    obtain ⟨x, rfl⟩ := ((p r).mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := ((p r).mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := ((p r).mem_carrier z).1 hz
    exact ((p r).canonicalMeetGraph_iff ((family).tile r).order related x y z).2 ((meet x y z).1 hv)
  · intro hv
    obtain ⟨x, hx, y, hy, z, hz, rfl, _⟩ := (mem_canonicalMeetGraph _ _ _).1 hv
    obtain ⟨x, rfl⟩ := ((p r).mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := ((p r).mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := ((p r).mem_carrier z).1 hz
    exact (meet x y z).2 (((p r).canonicalMeetGraph_iff ((family).tile r).order related x y z).1 hv)

theorem localTileMeet_code (r : Index) :
    MeetOrderCode (completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r))
      (completion.localTileOrder P0 r0 μ0 A0 (externalRequestIndexCode r))
      (completion.localTileMeet P0 r0 μ0 A0 (externalRequestIndexCode r)) := by
  let := group.toGroup
  rw [data.localTileMeet_eq_canonical group oldAction pairing unions powers separation infinite hG]
  exact (p r).canonicalMeetOrderCode ((family).tile r).order
    (localTileOrder_shape (completion := completion) r)
    (data.localTileOrder_iff group oldAction pairing unions powers separation infinite hG r)

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
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "p" => data.localTilePresentation group oldAction pairing unions powers separation infinite hG
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "Requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "vcode" => completion.externalFamilyVertexCode group oldAction data.original
local notation "vertexGraph(" r "," i ")" => indexedRelationSection U Q (completion.localTileVertexImages P0 r0 μ0 A0)
  (ZFSet.pair (externalRequestIndexCode r) (vcode r i))
include data group oldAction pairing unions powers separation infinite hG

theorem localTileVertexGraph_iff :
    letI := group.toGroup
    ∀ (r : Index) (i : Option ((family).Child r)) (x : SetMembers U) (y : ((family).tile r).Space),
      ZFSet.pair (SetMembers.raw x) ((p r).encode y) ∈ vertexGraph(r, i) ↔
        ((family).flatVertex r i).toFun x = y := by
  let := group.toGroup
  intro r i x y
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  rw [pair_mem_indexedRelationSection]
  have hy : (p r).encode y ∈ Q := qc ▸ (q).encode_mem _
  simp only [SetMembers.raw_mem, hy, true_and]
  change ZFSet.pair
    ((completion.externalFamilyTileVertexPresentation group oldAction data.original).encode ⟨r, i, x⟩)
    ((q).encode (((family).placedTile (action) 1 r).toFun y)) ∈ _ ↔ _
  rw [data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG]
  rw [← (family).flatVertex_copy]
  exact ⟨fun equal => embedding_injective ((family).placedTile (action) 1 r).toMeetEmbedding equal,
    fun equal => congrArg _ equal⟩

theorem localTileVertexGraph_eq :
    letI := group.toGroup
    ∀ (r : Index) (i : Option ((family).Child r)),
      vertexGraph(r, i) = (SetMembers.presentation U).graph (p r) ((family).flatVertex r i).toFun := by
  let := group.toGroup
  intro r i
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  apply ZFSet.ext
  intro v
  constructor
  · intro hv
    obtain ⟨x, hx, y, hy, rfl, entry⟩ := (mem_indexedRelationSection _ _ _ _ _).1 hv
    obtain ⟨y, rfl⟩ := ((q).mem_carrier y).1 (qc.symm ▸ hy)
    let x' := SetMembers.ofMem x hx
    have copied := (data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG
      r i x' y).1 (by simpa only [GroundCompressionCompletion.externalFamilyTileVertexPresentation_encode,
        x', SetMembers.raw_ofMem] using entry)
    have equal : (q).encode y = (p r).encode (((family).flatVertex r i).toFun x') := by
      change (q).encode y = (q).encode (((family).placedTile (action) 1 r).toFun _)
      rw [(family).flatVertex_copy, copied]
    rw [equal]
    exact ((SetMembers.presentation U).mem_graph (p r) _ _).2
      ⟨x', by change ZFSet.pair (SetMembers.raw x') _ = _; simp only [x', SetMembers.raw_ofMem]⟩
  · intro hv
    obtain ⟨x, rfl⟩ := ((SetMembers.presentation U).mem_graph (p r) _ _).1 hv
    exact (data.localTileVertexGraph_iff group oldAction pairing unions powers separation infinite hG r i x _).2 rfl

omit pairing unions powers separation infinite hG in
theorem localTileVertexCode_mem (r : Index) (i : Option ((family).Child r)) : vcode r i ∈ natSetCode 3 := by
  have range := (completion.externalFamilyVertexCode_range group oldAction data.original r _).2 ⟨i, rfl⟩
  rcases range with equal | equal | ⟨_, equal⟩
  all_goals rw [equal]; exact (natSetCode_mem_iff _ 3).2 (by decide)

theorem localTileVertexGraph_mem (hP0 : P0 ∈ M.sets) (r : Index) (i : Option ((family).Child r)) :
    vertexGraph(r, i) ∈ M.sets := by
  have grounds := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  have requestGround := M.transitive data.words.requests_ground
    ((externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem r)
  have indexGround := M.transitive (M.natSetCode_mem separation infinite 3)
    (data.localTileVertexCode_mem group oldAction r i)
  exact M.indexedRelationSection_mem pairing unions powers separation (completion.algebra.union.ground 0)
    grounds.1 grounds.2.2.2.1 (M.orderedPair_mem pairing requestGround indexGround)

theorem localTileVertexGraph_family (hP0 : P0 ∈ M.sets) (r : Index) (i : Option ((family).Child r)) :
    ZFSet.pair (ZFSet.pair (externalRequestIndexCode r) (vcode r i)) (vertexGraph(r, i)) ∈
      completion.localTileVertexGraphs P0 r0 μ0 A0 := by
  apply ((data.localTileVertexGraphs_spec group oldAction pairing unions powers separation infinite hG hP0).2.2 _ _).2
  exact ⟨ZFSet.pair_mem_prod.2
    ⟨(externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem r,
      data.localTileVertexCode_mem group oldAction r i⟩, rfl⟩

theorem localTileVertexGraph_code (r : Index) (i : Option ((family).Child r)) :
    IdealEmbeddingCode U (completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r))
      (completion.algebra.union.fields 1) (completion.localTileOrder P0 r0 μ0 A0 (externalRequestIndexCode r))
      (completion.algebra.union.fields 2) (completion.localTileMeet P0 r0 μ0 A0 (externalRequestIndexCode r))
      (vertexGraph(r, i)) := by
  let := group.toGroup
  rw [data.localTileVertexGraph_eq group oldAction pairing unions powers separation infinite hG]
  exact (SetMembers.presentation U).idealEmbeddingCode (p r) ((family).flatVertex r i)
    (fun _ _ => Iff.rfl)
    (data.localTileOrder_iff group oldAction pairing unions powers separation infinite hG r)
    (fun x y z => (completion.algebra.union.meet.toSmallMeetOrder_meet_eq_iff x y z).symm)
    (data.localTileMeet_iff group oldAction pairing unions powers separation infinite hG r)

end PartitionPilot.Forcing.GroundExternalGeometryInputs




namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 C Q rQ original D rD c lo hi : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (heights : GroundCompressionHeightData M initial I Sources Reps G m one T
  completion.algebra.union P0 C Q rQ original)
variable (columns : ordinalSetProperty C) (heightOrder : StrictLinearOrderCode Q rQ)
variable (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hrQ : rQ ∈ M.sets)
variable (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
variable (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
variable (hlo : lo ∈ D) (hhi : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD)
local notation "Requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "family" => completion.externalFamily group oldAction data.original
include data group oldAction pairing unions powers separation collection infinite hG hP0
  heights columns heightOrder hC hQ hrQ target injection hD hrD hc hlo hhi gap

theorem exists_localTileHeight (i : ZFSet.{u}) (hIndex : i ∈ Requests) :
    ∃ height ∈ M.sets,
      IntervalHeightCode (completion.localTileCarrier P0 r0 μ0 A0 i)
        (completion.localTileOrder P0 r0 μ0 A0 i) D rD lo hi height := by
  let := group.toGroup
  let requests := externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)
  obtain ⟨r, rfl⟩ := (requests.mem_carrier i).1 hIndex
  let p := data.localTilePresentation group oldAction pairing unions powers separation infinite hG r
  let source := SetMembers.presentation U
  let values := SetMembers.presentation (ZFSet.prod C Q)
  let linear := lexHeightOrder_code columns heightOrder
  let seed := heights.code.strictHeightGraph.smallHeight completion.algebra.union.meet linear
  have seedGround : source.graph values seed.value ∈ M.sets := by
    rw [StrictHeightGraphCode.smallHeight_graph]
    exact heights.height_ground
  have seedSmall : M.groundEmbeddable (relationImage U (ZFSet.prod C Q)
      (source.graph values seed.value)) ZFSet.omega := by
    rw [StrictHeightGraphCode.smallHeight_graph]
    exact heights.range_countable
  have carriers := data.localTileCarriers_spec group oldAction pairing unions powers separation infinite hG hP0
  have meets := data.localTileMeets_spec group oldAction pairing unions powers separation infinite hG hP0
  have indexMember := requests.encode_mem r
  have carrierGround : p.carrier ∈ M.sets :=
    M.pair_right (M.transitive carriers.1 ((carriers.2.2 _ _).2 ⟨indexMember, rfl⟩))
  have meetGround : completion.localTileMeet P0 r0 μ0 A0 (externalRequestIndexCode r) ∈ M.sets :=
    M.pair_right (M.transitive meets.1 ((meets.2.2 _ _).2 ⟨indexMember, rfl⟩))
  have tileMeet := data.localTileMeet_code group oldAction pairing unions powers separation infinite hG r
  have rootGround : source.graph p (((family).tile r).root.toFun) ∈ M.sets := by
    change source.graph p (((family).flatVertex r none).toFun) ∈ M.sets
    rw [← data.localTileVertexGraph_eq group oldAction pairing unions powers separation infinite hG]
    exact data.localTileVertexGraph_mem group oldAction pairing unions powers separation infinite hG hP0 r none
  have childrenGround : ∀ j, source.graph p ((((family).tile r).child j).toFun) ∈ M.sets := by
    intro j
    change source.graph p (((family).flatVertex r (some j)).toFun) ∈ M.sets
    rw [← data.localTileVertexGraph_eq group oldAction pairing unions powers separation infinite hG]
    exact data.localTileVertexGraph_mem group oldAction pairing unions powers separation infinite hG hP0 r (some j)
  obtain ⟨height, ground, code, _, _⟩ := M.exists_requestTileIntervalHeight
    pairing unions powers separation collection infinite source values
    ((family).top) ((family).greatest) linear.smallOrder seed
    (fun _ _ => Iff.rfl) linear target injection (completion.algebra.union.ground 0)
    (M.prod_mem pairing unions powers separation hC hQ) seedGround
    (M.lexHeightOrder_mem pairing unions powers separation hC hQ hrQ)
    hD hrD hc seedSmall hlo hhi gap ((family).request r) p carrierGround meetGround
    (data.localTileOrder_iff group oldAction pairing unions powers separation infinite hG r)
    tileMeet.operation
    (fun x y => (data.localTileMeet_iff group oldAction pairing unions powers separation infinite hG r x y _).2 rfl)
    rootGround childrenGround
  exact ⟨height, ground, code⟩

theorem exists_localHeightFamily (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    Nonempty (GroundExternalLocalHeightData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 D rD lo hi completion) := by
  apply data.localHeightFamily_of_witnesses group oldAction pairing unions powers separation infinite choice hG hP0
    hD hrD hc (M.transitive hD hlo) (M.transitive hD hhi) injection
  exact data.exists_localTileHeight group oldAction pairing unions powers separation collection infinite hG hP0
    heights columns heightOrder hC hQ hrQ target injection hD hrD hc hlo hhi gap

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end OAI
