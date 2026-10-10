import OAI.SetTheory.PartitionPrinciple.Forcing.RefinementAssignmentActionLaws
import OAI.SetTheory.PartitionPrinciple.Forcing.RelationActionFamilies
import OAI.SetTheory.PartitionPrinciple.Forcing.StageThreeAssignmentTestActions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBinaryUnionFamilies

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem refinementAssignment_relationLaws {G P L : Type u}
    [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
    (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (params : StageOneActionParameters M a s t b d T T2 valid) :
    RelationActionLaws G (stageOneAssignments (M.niceRefinementIndices a s b d level T T2 valid) T)
      (M.refinementAssignmentActionGraph a s b d level T T2 valid valid2) := by
  exact ⟨M.refinementAssignmentActionGraph_function a s b d level T T2 valid valid2 params.terms_closed t
      pairing unions powers separation collection carrier order params.condition_maps params.pairs_closed params.family_ground,
    M.refinementAssignmentActionGraph_injection a s b d level T T2 valid valid2 t
      pairing unions powers separation collection carrier order params.condition_maps params.terms_closed params.pairs_closed params.family_ground,
    fun _ hx => M.refinementAssignmentActionGraph_one a s b d level T T2 valid valid2 t
      pairing unions powers separation collection carrier order params.condition_maps params.terms_closed params.pairs_closed params.family_ground hx,
    fun g h _ hx => M.refinementAssignmentActionGraph_mul a s b d level T T2 valid valid2 t
      pairing unions powers separation collection carrier order params.condition_maps params.terms_closed params.pairs_closed params.family_ground g h hx⟩

variable {G P0 P1 L : Type u}
variable [Group G] [PartialOrder P0] [OrderTop P0] [PartialOrder P1] [OrderTop P1] [PartialOrder L]
variable (a0 : PosetAction G P0) (s0 : Presentation P0) (a1 : PosetAction G P1) (s1 : Presentation P1)
variable (b : Presentation L) (d : PosetAction G L) (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier0 : s0.carrier ∈ M.sets) (order0 : s0.conditionOrder ∈ M.sets)
variable (carrier1 : s1.carrier ∈ M.sets) (order1 : s1.conditionOrder ∈ M.sets)
variable (params0 : StageOneActionParameters M a0 s0 t b d T T2 v0)
variable (params1 : StageOneActionParameters M a1 s1 t b d T T2 v1)
local notation "I0" => M.niceRefinementIndices a0 s0 b d ∅ T T2 v0
local notation "I1" => M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1
local notation "J" => stageOneAssignments (I0 ∪ I1) T
local notation "graph" => M.stageTwoAssignmentActionGraph a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "image" => M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "laws0" => M.refinementAssignment_relationLaws a0 s0 b d ∅ T T2 v0 v02 t
  pairing unions powers separation collection carrier0 order0 params0
local notation "laws1" => M.refinementAssignment_relationLaws a1 s1 b d (natSetCode 1) T T2 v1 v12 t
  pairing unions powers separation collection carrier1 order1 params1
include pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1

theorem stageTwoAssignmentImage_eq_relationImage (g : G) (A : ZFSet.{u}) :
    image g A = relationImage A J (graph g) := by
  rw [stageOneAssignments_union]
  exact (relationImage_union_graph ((laws0).function g) ((laws1).function g) A).symm

variable (first : RefinementIndexLevelCode (M.niceRefinementIndices a0 s0 b d ∅ T T2 v0) ∅)
variable (second : RefinementIndexLevelCode (M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1) (natSetCode 1))
include first second

theorem stageTwoAssignment_relationLaws : RelationActionLaws G J graph := by
  rw [stageOneAssignments_union]
  exact (laws0).union (laws1) (stageTwoAssignments_disjoint first second)

theorem stageTwoAssignmentImage_one {A : ZFSet.{u}} (subset : A ⊆ J) : image 1 A = A := by
  rw [M.stageTwoAssignmentImage_eq_relationImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1]
  exact (M.stageTwoAssignment_relationLaws a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1 first second).image_one subset

theorem stageTwoAssignmentImage_mul (g h : G) {A : ZFSet.{u}} (subset : A ⊆ J) :
    image (g * h) A = image g (image h A) := by
  simp only [M.stageTwoAssignmentImage_eq_relationImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1]
  exact (M.stageTwoAssignment_relationLaws a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1 first second).image_mul g h subset

end

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable {G P0 P1 L : Type u}
variable [Group G] [PartialOrder P0] [OrderTop P0] [PartialOrder P1] [OrderTop P1] [PartialOrder L]
variable (a0 : PosetAction G P0) (s0 : Presentation P0) (a1 : PosetAction G P1) (s1 : Presentation P1)
variable (b : Presentation L) (d : PosetAction G L) (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier0 : s0.carrier ∈ M.sets) (order0 : s0.conditionOrder ∈ M.sets)
variable (carrier1 : s1.carrier ∈ M.sets) (order1 : s1.conditionOrder ∈ M.sets)
variable (params0 : StageOneActionParameters M a0 s0 t b d T T2 v0)
variable (params1 : StageOneActionParameters M a1 s1 t b d T T2 v1)
local notation "I0" => M.niceRefinementIndices a0 s0 b d ∅ T T2 v0
local notation "I1" => M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1
local notation "J" => stageOneAssignments (I0 ∪ I1) T
local notation "graph" => M.stageTwoAssignmentActionGraph a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "image" => M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "laws0" => M.refinementAssignment_relationLaws a0 s0 b d ∅ T T2 v0 v02 t
  pairing unions powers separation collection carrier0 order0 params0
local notation "laws1" => M.refinementAssignment_relationLaws a1 s1 b d (natSetCode 1) T T2 v1 v12 t
  pairing unions powers separation collection carrier1 order1 params1

local notation "oldImage" => M.stageOneAssignmentImage a0 s0 b d T T2 v0 v02
local notation "levels" => stageTwoAssignmentLevels I0 I1 T
variable (first : RefinementIndexLevelCode (M.niceRefinementIndices a0 s0 b d ∅ T T2 v0) ∅)
variable (second : RefinementIndexLevelCode (M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1) (natSetCode 1))

include pairing unions powers separation collection carrier0 order0 params0 first second in
theorem stageTwoAssignmentImage_cut (g : G) (A : ZFSet.{u}) :
    assignmentCut levels (natSetCode 1) (image g A) =
      oldImage g (assignmentCut levels (natSetCode 1) A) := by
  rw [stageTwoAssignmentCut_one first second, stageTwoAssignmentCut_one first second]
  change ZFSet.sep (fun z => z ∈ stageOneAssignments I0 T)
    (relationImage A (stageOneAssignments I0 T)
      (M.refinementAssignmentActionGraph a0 s0 b d ∅ T T2 v0 v02 g) ∪
     relationImage A (stageOneAssignments I1 T)
      (M.refinementAssignmentActionGraph a1 s1 b d (natSetCode 1) T T2 v1 v12 g)) = _
  rw [disjointRelationImage_selection (stageTwoAssignments_disjoint first second)]
  exact relationImage_source_selection ((laws0).function g) A

include pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1 first second in
theorem stageTwoAssignmentImage_on_old (g : G) {A : ZFSet.{u}}
    (subset : A ⊆ stageOneAssignments I0 T) : image g A = oldImage g A := by
  have only : image g A ⊆ stageOneAssignments I0 T := by
    intro z member
    rcases ZFSet.mem_union.1 member with left | right
    · exact M.refinementAssignmentImage_subset a0 s0 b d ∅ T T2 v0 v02 g A left
    · obtain ⟨_,x,hx,entry⟩ := (mem_relationImage A (stageOneAssignments I1 T)
        (M.refinementAssignmentActionGraph a1 s1 b d (natSetCode 1) T T2 v1 v12 g) z).1 right
      exact False.elim (stageTwoAssignments_disjoint first second x (subset hx)
        (ZFSet.pair_mem_prod.1 (((laws1).function g).1 entry)).1)
  rw [← stageTwoAssignmentCut_one_eq first second only,
    M.stageTwoAssignmentImage_cut a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
      pairing unions powers separation collection carrier0 order0 params0 first second,
    stageTwoAssignmentCut_one_eq first second subset]

end

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable {G P0 P1 L : Type u}
variable [Group G] [PartialOrder P0] [OrderTop P0] [PartialOrder P1] [OrderTop P1] [PartialOrder L]
variable (a0 : PosetAction G P0) (s0 : Presentation P0) (a1 : PosetAction G P1) (s1 : Presentation P1)
variable (b : Presentation L) (d : PosetAction G L) (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier0 : s0.carrier ∈ M.sets) (order0 : s0.conditionOrder ∈ M.sets)
variable (carrier1 : s1.carrier ∈ M.sets) (order1 : s1.conditionOrder ∈ M.sets)
variable (params0 : StageOneActionParameters M a0 s0 t b d T T2 v0)
variable (params1 : StageOneActionParameters M a1 s1 t b d T T2 v1)
local notation "I0" => M.niceRefinementIndices a0 s0 b d ∅ T T2 v0
local notation "I1" => M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1
local notation "J" => stageOneAssignments (I0 ∪ I1) T
local notation "graph" => M.stageTwoAssignmentActionGraph a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "image" => M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "laws0" => M.refinementAssignment_relationLaws a0 s0 b d ∅ T T2 v0 v02 t
  pairing unions powers separation collection carrier0 order0 params0
local notation "laws1" => M.refinementAssignment_relationLaws a1 s1 b d (natSetCode 1) T T2 v1 v12 t
  pairing unions powers separation collection carrier1 order1 params1

noncomputable def stageTwoAssignmentActionFamily : ZFSet.{u} := familyCodeGraph t.encode graph

theorem pair_mem_stageTwoAssignmentActionFamily (g : G) (F : ZFSet.{u}) :
    ZFSet.pair (t.encode g) F ∈ M.stageTwoAssignmentActionFamily a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t ↔
      F = graph g := pair_mem_familyCodeGraph _ _ t.injective g F

include pairing unions powers separation in
theorem stageTwoAssignmentActionFamily_mem
    (group : t.carrier ∈ M.sets)
    (whole0 : M.refinementAssignmentActionFamily a0 s0 t b d ∅ T T2 v0 v02 ∈ M.sets)
    (whole1 : M.refinementAssignmentActionFamily a1 s1 t b d (natSetCode 1) T T2 v1 v12 ∈ M.sets) :
    M.stageTwoAssignmentActionFamily a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t ∈ M.sets :=
  M.familyCodeGraph_binaryUnions_mem t
    (M.refinementAssignmentActionGraph a0 s0 b d ∅ T T2 v0 v02)
    (M.refinementAssignmentActionGraph a1 s1 b d (natSetCode 1) T T2 v1 v12)
    pairing unions powers separation group whole0 whole1

include pairing unions powers separation collection carrier0 carrier1 params0 params1 in
theorem stageTwoAssignmentActionGraph_mem
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (g : G) : graph g ∈ M.sets := by
  exact M.binary_union_mem pairing unions
    (M.refinementAssignmentActionGraph_mem a0 s0 b d ∅ T T2 v0 v02 t
      pairing unions powers separation collection carrier0 params0.condition_maps params0.node_maps
      (M.empty_mem ⟨T,hT⟩) hT hT2 hI0 g)
    (M.refinementAssignmentActionGraph_mem a1 s1 b d (natSetCode 1) T T2 v1 v12 t
      pairing unions powers separation collection carrier1 params1.condition_maps params1.node_maps
      (M.transitive omega (natSetCode_mem_omega 1)) hT hT2 hI1 g)

include pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1 in
theorem stageTwoAssignmentActionFamily_mem_of_inputs
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.stageTwoAssignmentActionFamily a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t ∈ M.sets := by
  apply M.stageTwoAssignmentActionFamily_mem a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
    pairing unions powers separation group
  · exact M.refinementAssignmentActionFamily_mem_of_inputs a0 s0 t b d ∅ T T2 v0 v02
      pairing unions powers separation collection carrier0 group nodes order0 params0.condition_maps params0.node_maps
      (M.empty_mem ⟨T,hT⟩) hT hT2 hI0 params0.terms_closed params0.pairs_closed params0.family_ground
  · exact M.refinementAssignmentActionFamily_mem_of_inputs a1 s1 t b d (natSetCode 1) T T2 v1 v12
      pairing unions powers separation collection carrier1 group nodes order1 params1.condition_maps params1.node_maps
      (M.transitive omega (natSetCode_mem_omega 1)) hT hT2 hI1 params1.terms_closed params1.pairs_closed params1.family_ground

variable (first : RefinementIndexLevelCode (M.niceRefinementIndices a0 s0 b d ∅ T T2 v0) ∅)
variable (second : RefinementIndexLevelCode (M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1) (natSetCode 1))

include pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1 first second in
theorem stageTwoAssignmentImage_small
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (g : G) {A : ZFSet.{u}}
    (member : A ∈ M.groundSmallSubsets J ZFSet.omega) :
    image g A ∈ M.groundSmallSubsets J ZFSet.omega := by
  obtain ⟨hA,subset,small⟩ := (M.mem_groundSmallSubsets J ZFSet.omega A).1 member
  have hJ := M.stageOneAssignments_mem pairing unions powers separation
    (M.binary_union_mem pairing unions hI0 hI1) hT
  have whole := M.stageTwoAssignmentActionGraph_mem a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
    pairing unions powers separation collection carrier0 carrier1 params0 params1 hT hT2 hI0 hI1 omega g
  have laws := M.stageTwoAssignment_relationLaws a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1 first second
  rw [M.stageTwoAssignmentImage_eq_relationImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1]
  exact (M.mem_groundSmallSubsets J ZFSet.omega _).2
    ⟨M.relationImage_mem separation hA hJ whole,
      fun z hz => ((mem_relationImage A J (graph g) z).1 hz).1,
      M.groundEmbeddable_image pairing unions powers separation hA hJ omega whole (laws.injection g) subset small⟩

end

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P0 P1 P2 L : Type u}
variable [Group G] [PartialOrder P0] [OrderTop P0] [PartialOrder P1] [OrderTop P1]
variable [PartialOrder P2] [OrderTop P2] [PartialOrder L]
variable (a0 : PosetAction G P0) (s0 : Presentation P0) (a1 : PosetAction G P1) (s1 : Presentation P1)
variable (a2 : PosetAction G P2) (s2 : Presentation P2)
variable (b : Presentation L) (d : PosetAction G L) (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
variable (v2 : ∀ z ∈ T, IsName s2 z) (v22 : ∀ z ∈ T2, IsName s2 z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier0 : s0.carrier ∈ M.sets) (order0 : s0.conditionOrder ∈ M.sets)
variable (carrier1 : s1.carrier ∈ M.sets) (order1 : s1.conditionOrder ∈ M.sets)
variable (carrier2 : s2.carrier ∈ M.sets) (order2 : s2.conditionOrder ∈ M.sets)
variable (params0 : StageOneActionParameters M a0 s0 t b d T T2 v0)
variable (params1 : StageOneActionParameters M a1 s1 t b d T T2 v1)
variable (params2 : StageOneActionParameters M a2 s2 t b d T T2 v2)
local notation "I0" => M.niceRefinementIndices a0 s0 b d ∅ T T2 v0
local notation "I1" => M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1
local notation "I2" => M.niceRefinementIndices a2 s2 b d (natSetCode 2) T T2 v2
local notation "Jold" => stageOneAssignments (I0 ∪ I1) T
local notation "Jnew" => stageOneAssignments I2 T
local notation "J" => stageOneAssignments ((I0 ∪ I1) ∪ I2) T
local notation "graph" => M.stageThreeAssignmentActionGraph a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22
local notation "image" => M.stageThreeAssignmentImage a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22
local notation "oldGraph" => M.stageTwoAssignmentActionGraph a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "oldImage" => M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "newGraph" => M.refinementAssignmentActionGraph a2 s2 b d (natSetCode 2) T T2 v2 v22
local notation "newImage" => M.refinementAssignmentImage a2 s2 b d (natSetCode 2) T T2 v2 v22
variable (first : RefinementIndexLevelCode (M.niceRefinementIndices a0 s0 b d ∅ T T2 v0) ∅)
variable (second : RefinementIndexLevelCode (M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1) (natSetCode 1))
local notation "oldLaws" => M.stageTwoAssignment_relationLaws a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
  pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1 first second
local notation "newLaws" => M.refinementAssignment_relationLaws a2 s2 b d (natSetCode 2) T T2 v2 v22 t
  pairing unions powers separation collection carrier2 order2 params2

include pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
  params0 params1 params2 first second in
theorem stageThreeAssignmentImage_eq_relationImage (g : G) (A : ZFSet.{u}) :
    image g A = relationImage A J (graph g) := by
  change oldImage g A ∪ newImage g A = _
  rw [M.stageTwoAssignmentImage_eq_relationImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1]
  rw [stageOneAssignments_union (I0 ∪ I1) I2 T]
  exact (relationImage_union_graph ((oldLaws).function g) ((newLaws).function g) A).symm

variable (third : RefinementIndexLevelCode (M.niceRefinementIndices a2 s2 b d (natSetCode 2) T T2 v2) (natSetCode 2))
include pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
  params0 params1 params2 first second third

theorem stageThreeAssignment_relationLaws : RelationActionLaws G J graph := by
  rw [stageOneAssignments_union (I0 ∪ I1) I2 T]
  exact (oldLaws).union (newLaws) (stageThreeAssignments_disjoint first second third)

theorem stageThreeAssignmentImage_one {A : ZFSet.{u}} (subset : A ⊆ J) : image 1 A = A := by
  rw [M.stageThreeAssignmentImage_eq_relationImage a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
    params0 params1 params2 first second]
  exact (M.stageThreeAssignment_relationLaws a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
    params0 params1 params2 first second third).image_one subset

theorem stageThreeAssignmentImage_mul (g h : G) {A : ZFSet.{u}} (subset : A ⊆ J) :
    image (g * h) A = image g (image h A) := by
  simp only [M.stageThreeAssignmentImage_eq_relationImage a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
    params0 params1 params2 first second]
  exact (M.stageThreeAssignment_relationLaws a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
    params0 params1 params2 first second third).image_mul g h subset

end

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P0 P1 P2 L : Type u}
variable [Group G] [PartialOrder P0] [OrderTop P0] [PartialOrder P1] [OrderTop P1]
variable [PartialOrder P2] [OrderTop P2] [PartialOrder L]
variable (a0 : PosetAction G P0) (s0 : Presentation P0) (a1 : PosetAction G P1) (s1 : Presentation P1)
variable (a2 : PosetAction G P2) (s2 : Presentation P2)
variable (b : Presentation L) (d : PosetAction G L) (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
variable (v2 : ∀ z ∈ T, IsName s2 z) (v22 : ∀ z ∈ T2, IsName s2 z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier0 : s0.carrier ∈ M.sets) (order0 : s0.conditionOrder ∈ M.sets)
variable (carrier1 : s1.carrier ∈ M.sets) (order1 : s1.conditionOrder ∈ M.sets)
variable (carrier2 : s2.carrier ∈ M.sets) (order2 : s2.conditionOrder ∈ M.sets)
variable (params0 : StageOneActionParameters M a0 s0 t b d T T2 v0)
variable (params1 : StageOneActionParameters M a1 s1 t b d T T2 v1)
variable (params2 : StageOneActionParameters M a2 s2 t b d T T2 v2)
local notation "I0" => M.niceRefinementIndices a0 s0 b d ∅ T T2 v0
local notation "I1" => M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1
local notation "I2" => M.niceRefinementIndices a2 s2 b d (natSetCode 2) T T2 v2
local notation "Jold" => stageOneAssignments (I0 ∪ I1) T
local notation "Jnew" => stageOneAssignments I2 T
local notation "J" => stageOneAssignments ((I0 ∪ I1) ∪ I2) T
local notation "graph" => M.stageThreeAssignmentActionGraph a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22
local notation "image" => M.stageThreeAssignmentImage a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22
local notation "oldGraph" => M.stageTwoAssignmentActionGraph a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "oldImage" => M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "newGraph" => M.refinementAssignmentActionGraph a2 s2 b d (natSetCode 2) T T2 v2 v22
local notation "newImage" => M.refinementAssignmentImage a2 s2 b d (natSetCode 2) T T2 v2 v22
variable (first : RefinementIndexLevelCode (M.niceRefinementIndices a0 s0 b d ∅ T T2 v0) ∅)
variable (second : RefinementIndexLevelCode (M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1) (natSetCode 1))
local notation "oldLaws" => M.stageTwoAssignment_relationLaws a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
  pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1 first second
local notation "newLaws" => M.refinementAssignment_relationLaws a2 s2 b d (natSetCode 2) T T2 v2 v22 t
  pairing unions powers separation collection carrier2 order2 params2

local notation "levels" => stageThreeAssignmentLevels I0 I1 I2 T
variable (third : RefinementIndexLevelCode (M.niceRefinementIndices a2 s2 b d (natSetCode 2) T T2 v2) (natSetCode 2))

include pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1
  first second third in
theorem stageThreeAssignmentImage_cut (g : G) (A : ZFSet.{u}) :
    assignmentCut levels (natSetCode 2) (image g A) =
      oldImage g (assignmentCut levels (natSetCode 2) A) := by
  rw [stageThreeAssignmentCut_two first second third, stageThreeAssignmentCut_two first second third]
  change ZFSet.sep (fun z => z ∈ Jold) (oldImage g A ∪ newImage g A) = _
  simp only [M.stageTwoAssignmentImage_eq_relationImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1]
  change ZFSet.sep (fun z => z ∈ Jold)
    (relationImage A Jold (oldGraph g) ∪ relationImage A Jnew (newGraph g)) = _
  rw [disjointRelationImage_selection (stageThreeAssignments_disjoint first second third)]
  exact relationImage_source_selection ((oldLaws).function g) A

include pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
  params0 params1 params2 first second third in
theorem stageThreeAssignmentImage_on_old (g : G) {A : ZFSet.{u}}
    (subset : A ⊆ Jold) : image g A = oldImage g A := by
  have only : image g A ⊆ Jold := by
    intro z member
    rcases ZFSet.mem_union.1 member with old | new
    · exact M.stageTwoAssignmentImage_subset a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 g A old
    · obtain ⟨_,x,hx,entry⟩ := (mem_relationImage A Jnew (newGraph g) z).1 new
      exact False.elim (stageThreeAssignments_disjoint first second third x (subset hx)
        (ZFSet.pair_mem_prod.1 (((newLaws).function g).1 entry)).1)
  rw [← stageThreeAssignmentCut_two_eq first second third only,
    M.stageThreeAssignmentImage_cut a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
      pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1 first second third,
    stageThreeAssignmentCut_two_eq first second third subset]

end

open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P0 P1 P2 L : Type u}
variable [Group G] [PartialOrder P0] [OrderTop P0] [PartialOrder P1] [OrderTop P1]
variable [PartialOrder P2] [OrderTop P2] [PartialOrder L]
variable (a0 : PosetAction G P0) (s0 : Presentation P0) (a1 : PosetAction G P1) (s1 : Presentation P1)
variable (a2 : PosetAction G P2) (s2 : Presentation P2)
variable (b : Presentation L) (d : PosetAction G L) (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
variable (v2 : ∀ z ∈ T, IsName s2 z) (v22 : ∀ z ∈ T2, IsName s2 z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier0 : s0.carrier ∈ M.sets) (order0 : s0.conditionOrder ∈ M.sets)
variable (carrier1 : s1.carrier ∈ M.sets) (order1 : s1.conditionOrder ∈ M.sets)
variable (carrier2 : s2.carrier ∈ M.sets) (order2 : s2.conditionOrder ∈ M.sets)
variable (params0 : StageOneActionParameters M a0 s0 t b d T T2 v0)
variable (params1 : StageOneActionParameters M a1 s1 t b d T T2 v1)
variable (params2 : StageOneActionParameters M a2 s2 t b d T T2 v2)
local notation "I0" => M.niceRefinementIndices a0 s0 b d ∅ T T2 v0
local notation "I1" => M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1
local notation "I2" => M.niceRefinementIndices a2 s2 b d (natSetCode 2) T T2 v2
local notation "Jold" => stageOneAssignments (I0 ∪ I1) T
local notation "Jnew" => stageOneAssignments I2 T
local notation "J" => stageOneAssignments ((I0 ∪ I1) ∪ I2) T
local notation "graph" => M.stageThreeAssignmentActionGraph a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22
local notation "image" => M.stageThreeAssignmentImage a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22
local notation "oldGraph" => M.stageTwoAssignmentActionGraph a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "oldImage" => M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "newGraph" => M.refinementAssignmentActionGraph a2 s2 b d (natSetCode 2) T T2 v2 v22
local notation "newImage" => M.refinementAssignmentImage a2 s2 b d (natSetCode 2) T T2 v2 v22
variable (first : RefinementIndexLevelCode (M.niceRefinementIndices a0 s0 b d ∅ T T2 v0) ∅)
variable (second : RefinementIndexLevelCode (M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1) (natSetCode 1))
local notation "oldLaws" => M.stageTwoAssignment_relationLaws a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
  pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1 first second
local notation "newLaws" => M.refinementAssignment_relationLaws a2 s2 b d (natSetCode 2) T T2 v2 v22 t
  pairing unions powers separation collection carrier2 order2 params2

noncomputable def stageThreeAssignmentActionFamily : ZFSet.{u} := familyCodeGraph t.encode graph

theorem pair_mem_stageThreeAssignmentActionFamily (g : G) (F : ZFSet.{u}) :
    ZFSet.pair (t.encode g) F ∈ M.stageThreeAssignmentActionFamily
      a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t ↔ F = graph g :=
  pair_mem_familyCodeGraph _ _ t.injective g F

include pairing unions powers separation in
theorem stageThreeAssignmentActionFamily_mem
    (group : t.carrier ∈ M.sets)
    (wholeOld : M.stageTwoAssignmentActionFamily a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t ∈ M.sets)
    (wholeNew : M.refinementAssignmentActionFamily a2 s2 t b d (natSetCode 2) T T2 v2 v22 ∈ M.sets) :
    M.stageThreeAssignmentActionFamily a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t ∈ M.sets :=
  M.familyCodeGraph_binaryUnions_mem t oldGraph newGraph
    pairing unions powers separation group wholeOld wholeNew

include pairing unions powers separation collection carrier0 carrier1 carrier2 params0 params1 params2 in
theorem stageThreeAssignmentActionGraph_mem
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets) (hI2 : I2 ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (g : G) : graph g ∈ M.sets :=
  M.binary_union_mem pairing unions
    (M.stageTwoAssignmentActionGraph_mem a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
      pairing unions powers separation collection carrier0 carrier1 params0 params1 hT hT2 hI0 hI1 omega g)
    (M.refinementAssignmentActionGraph_mem a2 s2 b d (natSetCode 2) T T2 v2 v22 t
      pairing unions powers separation collection carrier2 params2.condition_maps params2.node_maps
      (M.transitive omega (natSetCode_mem_omega 2)) hT hT2 hI2 g)

include pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
  params0 params1 params2 in
theorem stageThreeAssignmentActionFamily_mem_of_inputs
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets) (hI2 : I2 ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.stageThreeAssignmentActionFamily a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t ∈ M.sets := by
  apply M.stageThreeAssignmentActionFamily_mem a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
    pairing unions powers separation group
  · exact M.stageTwoAssignmentActionFamily_mem_of_inputs a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
      pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1
      group nodes hT hT2 hI0 hI1 omega
  · exact M.refinementAssignmentActionFamily_mem_of_inputs a2 s2 t b d (natSetCode 2) T T2 v2 v22
      pairing unions powers separation collection carrier2 group nodes order2 params2.condition_maps params2.node_maps
      (M.transitive omega (natSetCode_mem_omega 2)) hT hT2 hI2
      params2.terms_closed params2.pairs_closed params2.family_ground

variable (third : RefinementIndexLevelCode (M.niceRefinementIndices a2 s2 b d (natSetCode 2) T T2 v2) (natSetCode 2))
include pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
  params0 params1 params2 first second third in
theorem stageThreeAssignmentImage_small
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets) (hI2 : I2 ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (g : G) {A : ZFSet.{u}}
    (member : A ∈ M.groundSmallSubsets J ZFSet.omega) :
    image g A ∈ M.groundSmallSubsets J ZFSet.omega := by
  obtain ⟨hA,subset,small⟩ := (M.mem_groundSmallSubsets J ZFSet.omega A).1 member
  have hJ := M.stageOneAssignments_mem pairing unions powers separation
    (M.binary_union_mem pairing unions (M.binary_union_mem pairing unions hI0 hI1) hI2) hT
  have whole := M.stageThreeAssignmentActionGraph_mem a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
    pairing unions powers separation collection carrier0 carrier1 carrier2 params0 params1 params2
    hT hT2 hI0 hI1 hI2 omega g
  have laws := M.stageThreeAssignment_relationLaws a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
    params0 params1 params2 first second third
  rw [M.stageThreeAssignmentImage_eq_relationImage a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
    params0 params1 params2 first second]
  exact (M.mem_groundSmallSubsets J ZFSet.omega _).2
    ⟨M.relationImage_mem separation hA hJ whole,
      fun z hz => ((mem_relationImage A J (graph g) z).1 hz).1,
      M.groundEmbeddable_image pairing unions powers separation hA hJ omega whole (laws.injection g) subset small⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
