import OAI.SetTheory.PartitionPrinciple.Forcing.GroundExternalStarSupports

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem lowerDepthEdgeCode_iff {B : Type u} (s : Presentation B) (depth : B → Nat)
    {depths adjacency : ZFSet.{u}}
    (entries : ∀ x n, ZFSet.pair (s.encode x) (natSetCode n) ∈ depths ↔ n = depth x)
    (p v : B) :
    LowerDepthEdgeCode ZFSet.omega depths adjacency (s.encode p) (s.encode v) ↔
      ZFSet.pair (s.encode p) (s.encode v) ∈ adjacency ∧ depth p + 1 = depth v := by
  constructor
  · rintro ⟨edge, n, hn, m, hm, en, em, successor⟩
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
    rw [(entries v n).1 en, (entries p m).1 em, ← natSetCode_succ] at successor
    exact ⟨edge, (natSetCode_injective successor).symm⟩
  · rintro ⟨edge, lower⟩
    exact ⟨edge, natSetCode (depth v), natSetCode_mem_omega _,
      natSetCode (depth p), natSetCode_mem_omega _, (entries v _).2 rfl,
      (entries p _).2 rfl, by rw [← lower, natSetCode_succ]⟩

end PartitionPilot.Forcing

namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars
open Forcing SetRealization SetFormula
universe u
variable (J S R : Type u) [Group J] (request : S → R)
variable (s : Presentation (Vertex J S R)) {depths adjacency : ZFSet.{u}}
variable (depthEntries : ∀ x n, ZFSet.pair (s.encode x) (natSetCode n) ∈ depths ↔
  n = depth J S R request x)
variable (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ adjacency ↔
  ∃ d : Dart J S R, TileStars.source J S R request d = x ∧ TileStars.target J S R request d = y)

include depthEntries edges
theorem parentGraph_entry (v p : Vertex J S R) :
    ZFSet.pair (s.encode v) (s.encode p) ∈
      treeParentGraph s.carrier depths adjacency (s.encode (root J S R)) ↔
        parent J S R request v = p := by
  rw [pair_mem_treeParentGraph, lowerDepthEdgeCode_iff s (depth J S R request) depthEntries,
    edges, s.injective.eq_iff, s.injective.eq_iff]
  exact ⟨fun h => (parent_iff J S R request v p).2 h.2.2,
    fun h => ⟨s.encode_mem v, s.encode_mem p, (parent_iff J S R request v p).1 h⟩⟩

theorem parentGraph_eq_graph :
    treeParentGraph s.carrier depths adjacency (s.encode (root J S R)) =
      s.graph s (parent J S R request) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨v, hv, p, hp, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 entry).1
    obtain ⟨v, rfl⟩ := (s.mem_carrier v).1 hv
    obtain ⟨p, rfl⟩ := (s.mem_carrier p).1 hp
    exact (s.pair_mem_graph s _ v p).2
      ((parentGraph_entry J S R request s depthEntries edges v p).1 entry)
  · intro entry
    obtain ⟨v, rfl⟩ := (s.mem_graph s (parent J S R request) z).1 entry
    exact (parentGraph_entry J S R request s depthEntries edges v _).2 rfl

theorem parentGraph_spec (M : Forcing.TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hV : s.carrier ∈ M.sets) (hDepths : depths ∈ M.sets) (hAdjacency : adjacency ∈ M.sets) :
    treeParentGraph s.carrier depths adjacency (s.encode (root J S R)) ∈ M.sets ∧
      ZFSet.IsFunc s.carrier s.carrier
        (treeParentGraph s.carrier depths adjacency (s.encode (root J S R))) := by
  refine ⟨M.treeParentGraph_mem pairing unions powers separation infinite hV hDepths hAdjacency
    (M.transitive hV (s.encode_mem _)), ?_⟩
  rw [parentGraph_eq_graph J S R request s depthEntries edges]
  exact s.graph_isFunc s _

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars

end

namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalStarRoot (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair (natSetCode 0) (equivalenceClass (M.externalGroupCarrier G S m one)
    (M.externalCosetEquivalence G S m one) (M.externalGroupIdentity G S m one))
noncomputable def externalStarDepth (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  M.relationDepthGraph (M.externalStarVertices G S R m one) (M.externalStarAdjacency G S R m one)
    (M.externalStarRoot G S m one)

end TransitiveGround

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
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "sLetter" => completion.externalFamilyLetterPresentation group oldAction data.original
local notation "sRequest" => externalRequestPresentation I P0 rectangles
local notation "sCoset" => data.externalCosetPresentation group oldAction pairing unions powers separation infinite hG
local notation "sVertex" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "sDart" => data.externalStarDartPresentation group oldAction pairing unions powers separation infinite hG

theorem externalStarRoot_eq_encode :
    letI := group.toGroup
    M.externalStarRoot G letters m one =
      (sVertex).encode (TileStars.root (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)) := by
  let instRootEncodeGroup := group.toGroup
  change ZFSet.pair (natSetCode 0) (equivalenceClass (M.externalGroupCarrier G letters m one)
    (M.externalCosetEquivalence G letters m one) (M.externalGroupIdentity G letters m one)) =
    ZFSet.pair (natSetCode 0) (equivalenceClass (sGroup).carrier
      (externalCosetRelation (sGroup).carrier G (M.externalOldInclusion G letters m one)
        (M.externalGroupMultiplication G letters m one)) ((sGroup).encode 1))
  rw [completion.externalFamilyGroupPresentation_carrier,
    completion.externalFamilyGroupPresentation_identity group oldAction data.original
      pairing unions powers separation infinite hG data.words.letters_ground]
  rfl

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarRoot_mem : M.externalStarRoot G letters m one ∈ M.sets := by
  let instRootMembershipGroup := group.toGroup
  rw [data.externalStarRoot_eq_encode group oldAction pairing unions powers separation infinite hG]
  have members := data.externalStarCarriers_ground pairing unions powers separation hG
  have carriers := data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG
  exact M.transitive (carriers.1.symm ▸ members.1) ((sVertex).encode_mem _)

theorem externalStarDepth_eq_graph :
    letI := group.toGroup
    M.externalStarDepth G letters requests m one = (sVertex).graph natPresentation
      (fun x => ⟨TileStars.depth (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) x⟩) := by
  let instDepthGraphGroup := group.toGroup
  have carriers := data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG
  have members := data.externalStarCarriers_ground pairing unions powers separation hG
  have eq := TileStars.depthGraph_eq_graph (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)
    (fun a => a.1) M pairing unions separation infinite (sVertex)
    (data.externalStarAdjacency_iff group oldAction pairing unions powers separation infinite hG)
    (carriers.1.symm ▸ members.1)
  rw [carriers.1, ← data.externalStarRoot_eq_encode group oldAction pairing unions powers separation infinite hG] at eq
  exact eq

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarDepth_ground_function :
    M.externalStarDepth G letters requests m one ∈ M.sets ∧
      ZFSet.IsFunc (M.externalStarVertices G letters requests m one) ZFSet.omega
        (M.externalStarDepth G letters requests m one) := by
  let instDepthFunctionGroup := group.toGroup
  have members := data.externalStarCarriers_ground pairing unions powers separation hG
  have adjacency := (data.externalStarIncidence_ground pairing unions powers separation hG).2.2.2.2.2
  refine ⟨M.relationDepthGraph_mem pairing unions powers separation infinite members.1 adjacency
    (data.externalStarRoot_mem group oldAction pairing unions powers separation infinite hG), ?_⟩
  rw [data.externalStarDepth_eq_graph group oldAction pairing unions powers separation infinite hG]
  have function := (sVertex).graph_isFunc natPresentation
    (fun x => ⟨TileStars.depth (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) x⟩)
  rw [(data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1] at function
  exact function

theorem externalStarDepth_iff :
    letI := group.toGroup
    ∀ x n, ZFSet.pair ((sVertex).encode x) (natSetCode n) ∈ M.externalStarDepth G letters requests m one ↔
      n = TileStars.depth (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) x := by
  let instDepthEntryGroup := group.toGroup
  intro x n
  rw [data.externalStarDepth_eq_graph group oldAction pairing unions powers separation infinite hG]
  have entry := (sVertex).pair_mem_graph natPresentation
    (fun x => ⟨TileStars.depth (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) x⟩) x ⟨n⟩
  exact entry.trans ⟨fun equal => (congrArg ULift.down equal).symm, fun equal => congrArg ULift.up equal.symm⟩

end GroundExternalGeometryInputs

namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalStarLayer (G S R m one n : ZFSet.{u}) : ZFSet.{u} :=
  relationFiber (M.externalStarVertices G S R m one)
    (relationConverse (M.externalStarVertices G S R m one) ZFSet.omega (M.externalStarDepth G S R m one)) n
noncomputable def externalStarLayers (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  M.relationFiberFamily ZFSet.omega (M.externalStarVertices G S R m one)
    (relationConverse (M.externalStarVertices G S R m one) ZFSet.omega (M.externalStarDepth G S R m one))

end TransitiveGround

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
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "sLetter" => completion.externalFamilyLetterPresentation group oldAction data.original
local notation "sRequest" => externalRequestPresentation I P0 rectangles
local notation "sCoset" => data.externalCosetPresentation group oldAction pairing unions powers separation infinite hG
local notation "sVertex" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "sDart" => data.externalStarDartPresentation group oldAction pairing unions powers separation infinite hG

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarLayers_spec :
    M.externalStarLayers G letters requests m one ∈ M.sets ∧
      ZFSet.IsFunc ZFSet.omega (M.groundPower (M.externalStarVertices G letters requests m one))
        (M.externalStarLayers G letters requests m one) ∧
      ∀ n L, ZFSet.pair n L ∈ M.externalStarLayers G letters requests m one ↔
        n ∈ ZFSet.omega ∧ L = M.externalStarLayer G letters requests m one n := by
  have vertices := (data.externalStarCarriers_ground pairing unions powers separation hG).1
  have depth := (data.externalStarDepth_ground_function group oldAction pairing unions powers separation infinite hG).1
  have omega := M.omega_mem separation infinite
  have converse := M.relationConverse_mem pairing unions powers separation vertices omega depth
  exact ⟨M.relationFiberFamily_mem pairing unions powers separation omega vertices converse,
    M.relationFiberFamily_function separation omega vertices converse,
    M.relationFiberFamily_entries separation omega vertices converse⟩

theorem externalStarLayer_iff :
    letI := group.toGroup
    ∀ x n, (sVertex).encode x ∈ M.externalStarLayer G letters requests m one (natSetCode n) ↔
      n = TileStars.depth (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) x := by
  let instLayerEntryGroup := group.toGroup
  intro x n
  rw [TransitiveGround.externalStarLayer, mem_relationFiber, pair_mem_relationConverse]
  have hx : (sVertex).encode x ∈ M.externalStarVertices G letters requests m one :=
    (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1 ▸
      (sVertex).encode_mem x
  exact ⟨fun h => (data.externalStarDepth_iff group oldAction pairing unions powers separation infinite hG x n).1 h.2.2.2,
    fun h => ⟨hx, hx, natSetCode_mem_omega n,
      (data.externalStarDepth_iff group oldAction pairing unions powers separation infinite hG x n).2 h⟩⟩

end GroundExternalGeometryInputs

namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalStarParent (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  treeParentGraph (M.externalStarVertices G S R m one) (M.externalStarDepth G S R m one)
    (M.externalStarAdjacency G S R m one) (M.externalStarRoot G S m one)

end TransitiveGround

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
local notation "sVertex" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG

theorem externalStarParent_eq_graph :
    letI := group.toGroup
    M.externalStarParent G letters requests m one = (sVertex).graph (sVertex)
      (TileStars.parent (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1)) := by
  let instParentGraphGroup := group.toGroup
  have equal := TileStars.parentGraph_eq_graph (SetMembers G) (family).Letters
    (ExternalRequestIndex I P0 rectangles) (fun a => a.1) (sVertex)
    (data.externalStarDepth_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStarAdjacency_iff group oldAction pairing unions powers separation infinite hG)
  rw [(data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1,
    ← data.externalStarRoot_eq_encode group oldAction pairing unions powers separation infinite hG] at equal
  exact equal

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarParent_ground_function :
    M.externalStarParent G letters requests m one ∈ M.sets ∧
      ZFSet.IsFunc (M.externalStarVertices G letters requests m one)
        (M.externalStarVertices G letters requests m one) (M.externalStarParent G letters requests m one) := by
  let instParentFunctionGroup := group.toGroup
  have members := data.externalStarCarriers_ground pairing unions powers separation hG
  have depths := data.externalStarDepth_ground_function group oldAction pairing unions powers separation infinite hG
  have adjacency := (data.externalStarIncidence_ground pairing unions powers separation hG).2.2.2.2.2
  refine ⟨M.treeParentGraph_mem pairing unions powers separation infinite members.1 depths.1 adjacency
    (data.externalStarRoot_mem group oldAction pairing unions powers separation infinite hG), ?_⟩
  rw [data.externalStarParent_eq_graph group oldAction pairing unions powers separation infinite hG]
  have function := (sVertex).graph_isFunc (sVertex)
    (TileStars.parent (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1))
  rw [(data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1] at function
  exact function

theorem externalStarParent_iff :
    letI := group.toGroup
    ∀ v p, ZFSet.pair ((sVertex).encode v) ((sVertex).encode p) ∈ M.externalStarParent G letters requests m one ↔
      TileStars.parent (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) v = p := by
  let instParentEntryGroup := group.toGroup
  intro v p
  rw [data.externalStarParent_eq_graph group oldAction pairing unions powers separation infinite hG]
  exact (sVertex).pair_mem_graph (sVertex) _ v p

end GroundExternalGeometryInputs

namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalStarNonroots (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  treeNonrootCarrier (M.externalStarVertices G S R m one) (M.externalStarRoot G S m one)
noncomputable def externalStarIncoming (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  treeIncomingGraph (M.externalStarVertices G S R m one) (M.externalStarDarts G S R m one)
    (M.externalStarParent G S R m one) (M.externalStarSource G S R m one)
    (M.externalStarTarget G S R m one) (M.externalStarRoot G S m one)

end TransitiveGround

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
local notation "sVertex" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "sDart" => data.externalStarDartPresentation group oldAction pairing unions powers separation infinite hG

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarIncoming_ground_function :
    M.externalStarNonroots G letters requests m one ∈ M.sets ∧
      M.externalStarIncoming G letters requests m one ∈ M.sets ∧
      ZFSet.IsFunc (M.externalStarNonroots G letters requests m one)
        (M.externalStarDarts G letters requests m one) (M.externalStarIncoming G letters requests m one) := by
  let instIncomingFunctionGroup := group.toGroup
  have members := data.externalStarCarriers_ground pairing unions powers separation hG
  have parents := data.externalStarParent_ground_function group oldAction pairing unions powers separation infinite hG
  have incidence := data.externalStarIncidence_ground pairing unions powers separation hG
  have root := data.externalStarRoot_mem group oldAction pairing unions powers separation infinite hG
  refine ⟨M.treeNonrootCarrier_mem separation members.1 root,
    M.treeIncomingGraph_mem pairing unions powers separation members.1 members.2.2 parents.1 incidence.2.1 incidence.2.2.1 root, ?_⟩
  have function := TileStars.incomingGraph_function (SetMembers G) (family).Letters
    (ExternalRequestIndex I P0 rectangles) (fun a => a.1) (sVertex) (sDart)
    (data.externalStarParent_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStarSource_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStarTarget_iff group oldAction pairing unions powers separation infinite hG)
  have carriers := data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG
  rw [carriers.1, carriers.2.2,
    ← data.externalStarRoot_eq_encode group oldAction pairing unions powers separation infinite hG] at function
  exact function

theorem externalStarIncoming_iff :
    letI := group.toGroup
    ∀ v (nonroot : v ≠ TileStars.root (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)) d,
      ZFSet.pair ((sVertex).encode v) ((sDart).encode d) ∈ M.externalStarIncoming G letters requests m one ↔
        TileStars.incoming (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) v nonroot = d := by
  let instIncomingEntryGroup := group.toGroup
  intro v nonroot d
  have entry := TileStars.incomingGraph_entry (SetMembers G) (family).Letters
    (ExternalRequestIndex I P0 rectangles) (fun a => a.1) (sVertex) (sDart)
    (data.externalStarParent_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStarSource_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStarTarget_iff group oldAction pairing unions powers separation infinite hG) v nonroot d
  have carriers := data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG
  rw [carriers.1, carriers.2.2,
    ← data.externalStarRoot_eq_encode group oldAction pairing unions powers separation infinite hG] at entry
  exact entry

end GroundExternalGeometryInputs
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (P r μ A : ZFSet.{u})
local notation "letters" => externalChildLetters I P (externalRectangles P G r μ A)
local notation "requests" => externalRequestCarrier I P (externalRectangles P G r μ A)
local notation "Q" => completion.externalPointCarrier P r μ A
local notation "vertices" => M.externalStarVertices G letters requests m one
local notation "parents" => M.externalStarParent G letters requests m one

noncomputable def externalStarOverlaps : ZFSet.{u} :=
  parentSupportGraph vertices Q (completion.externalStarSupports P r μ A) parents
noncomputable def externalStarFresh : ZFSet.{u} :=
  freshSupportGraph vertices Q (completion.externalStarSupports P r μ A) parents
noncomputable def externalStarOverlapFamily : ZFSet.{u} :=
  M.relationFiberFamily vertices Q (completion.externalStarOverlaps P r μ A)
noncomputable def externalStarFreshFamily : ZFSet.{u} :=
  M.relationFiberFamily vertices Q (completion.externalStarFresh P r μ A)

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
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "vertices" => M.externalStarVertices G letters requests m one
include data group oldAction pairing unions powers separation infinite hG hP0

theorem externalStarOverlapFresh_ground :
    completion.externalStarOverlaps P0 r0 μ0 A0 ∈ M.sets ∧
      completion.externalStarFresh P0 r0 μ0 A0 ∈ M.sets := by
  have hv := (data.externalStarCarriers_ground pairing unions powers separation hG).1
  have hq := (data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0).1
  have hs := data.externalStarSupports_ground group oldAction pairing unions powers separation infinite hG hP0
  have hp := (data.externalStarParent_ground_function group oldAction pairing unions powers separation infinite hG).1
  exact ⟨M.parentSupportGraph_mem pairing unions powers separation hv hq hs hp,
    M.freshSupportGraph_mem pairing unions powers separation hv hq hs hp⟩

theorem externalStarOverlapFamily_spec :
    completion.externalStarOverlapFamily P0 r0 μ0 A0 ∈ M.sets ∧
      ZFSet.IsFunc vertices (M.groundPower Q) (completion.externalStarOverlapFamily P0 r0 μ0 A0) ∧
      ∀ v f, ZFSet.pair v f ∈ completion.externalStarOverlapFamily P0 r0 μ0 A0 ↔
        v ∈ vertices ∧ f = relationFiber Q (completion.externalStarOverlaps P0 r0 μ0 A0) v := by
  have hv := (data.externalStarCarriers_ground pairing unions powers separation hG).1
  have hq := (data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0).1
  have hs := (data.externalStarOverlapFresh_ground group oldAction pairing unions powers separation infinite hG hP0).1
  exact ⟨M.relationFiberFamily_mem pairing unions powers separation hv hq hs,
    M.relationFiberFamily_function separation hv hq hs,
    M.relationFiberFamily_entries separation hv hq hs⟩

theorem externalStarFreshFamily_spec :
    completion.externalStarFreshFamily P0 r0 μ0 A0 ∈ M.sets ∧
      ZFSet.IsFunc vertices (M.groundPower Q) (completion.externalStarFreshFamily P0 r0 μ0 A0) ∧
      ∀ v f, ZFSet.pair v f ∈ completion.externalStarFreshFamily P0 r0 μ0 A0 ↔
        v ∈ vertices ∧ f = relationFiber Q (completion.externalStarFresh P0 r0 μ0 A0) v := by
  have hv := (data.externalStarCarriers_ground pairing unions powers separation hG).1
  have hq := (data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0).1
  have hs := (data.externalStarOverlapFresh_ground group oldAction pairing unions powers separation infinite hG hP0).2
  exact ⟨M.relationFiberFamily_mem pairing unions powers separation hv hq hs,
    M.relationFiberFamily_function separation hv hq hs,
    M.relationFiberFamily_entries separation hv hq hs⟩

end GroundExternalGeometryInputs
end PartitionPilot.Forcing

end OAI
