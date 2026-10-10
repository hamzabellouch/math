import OAI.SetTheory.PartitionPrinciple.Definability.GroundLiftedRowTupleSupports
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageThreeDataBoundFixation
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageTwoNamePositionSupports

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L : Type u} [Preorder L] (b : Presentation L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include pairing unions powers separation infinite choice

theorem exists_stageOneDataBound {A I T S mu X anchors tuples used extra : ZFSet.{u}}
    (hA : A ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (whole : stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples ∈ M.sets)
    (smallA : M.groundEmbeddable A ZFSet.omega)
    (total : ∀ z ∈ A, ∃ E ∈ b.carrier, ZFSet.pair z E ∈
      stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples)
    (hUsed : used ∈ M.sets) (hExtra : extra ∈ M.sets)
    (usedSubset : used ⊆ b.carrier) (extraSubset : extra ⊆ b.carrier)
    (smallUsed : M.groundEmbeddable used ZFSet.omega)
    (smallExtra : M.groundEmbeddable extra ZFSet.omega)
    (countable_bound : ∀ W ∈ M.sets, W ⊆ b.carrier → M.groundEmbeddable W ZFSet.omega →
      ∃ D : L, ∀ x : L, b.encode x ∈ W → x ≤ D) :
    ∃ D : L, ∃ f ∈ M.sets, ∃ W ∈ M.sets,
      ZFSet.IsFunc A b.carrier f ∧
      f ⊆ stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples ∧
      W = (relationImage A b.carrier f ∪ used) ∪ extra ∧
      W ⊆ b.carrier ∧ M.groundEmbeddable W ZFSet.omega ∧
      (∀ x : L, b.encode x ∈ W → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (b.encode D) ∈
        stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples) ∧
      (∀ x : L, b.encode x ∈ used → x ≤ D) ∧
      (∀ x : L, b.encode x ∈ extra → x ≤ D) := by
  obtain ⟨f,hf,W,hW,function,selected,equal,subset,small,included,usedIn,extraIn⟩ :=
    M.exists_countableNodeSelection pairing unions powers separation infinite choice
      hA nodes whole smallA total hUsed hExtra usedSubset extraSubset smallUsed smallExtra
  obtain ⟨D,bound⟩ := countable_bound W hW subset small
  refine ⟨D,f,hf,W,hW,function,selected,equal,subset,small,bound,?_,?_,?_⟩
  · intro z hz
    obtain ⟨E,entry,_⟩ := function.2 z hz
    have hE := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    obtain ⟨E,rfl⟩ := (b.mem_carrier E).1 hE
    exact stageOneDataBounds_mono b (selected entry) (bound E (included z (b.encode E) entry))
  · intro x hx
    exact bound x (usedIn hx)
  · intro x hx
    exact bound x (extraIn hx)

end TransitiveGround

section
open SetFormula SetRealization
universe u

theorem refinementIndexFieldGraph_three_union (I0 I1 I2 B : ZFSet.{u}) (j : Fin 6) :
    refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) B j =
      (refinementIndexFieldGraph I0 B j ∪ refinementIndexFieldGraph I1 B j) ∪
        refinementIndexFieldGraph I2 B j := by
  rw [refinementIndexFieldGraph_union, refinementIndexFieldGraph_union]

theorem refinementIndexAnchor_three_entry {L : Type u} (b : Presentation L)
    (I0 I1 I2 level : ZFSet.{u}) (C E : L) (U Rf Rc y : ZFSet.{u}) :
    ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E) U Rf Rc) y ∈
      refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) b.carrier 2 ↔
    refinementIndexCode level (b.encode C) (b.encode E) U Rf Rc ∈ (I0 ∪ I1) ∪ I2 ∧
      y = b.encode E :=
  refinementIndexAnchor_union_entry b (I0 ∪ I1) I2 level C E U Rf Rc y

namespace NiceRefinementIndexSystem
variable {M : TransitiveGround.{u}} {G P0 P1 P2 L : Type u}
variable [Group G] [PartialOrder P0] [OrderTop P0] [PartialOrder P1] [OrderTop P1]
variable [PartialOrder P2] [OrderTop P2] [PartialOrder L]
variable {a0 : PosetAction G P0} {a1 : PosetAction G P1} {a2 : PosetAction G P2}
variable {s0 : Presentation P0} {s1 : Presentation P1} {s2 : Presentation P2}
variable {b : Presentation L} {d : PosetAction G L}
variable {level0 level1 level2 T T2 : ZFSet.{u}}
variable {v0 : ∀ z ∈ T, IsName s0 z} {v02 : ∀ z ∈ T2, IsName s0 z}
variable {v1 : ∀ z ∈ T, IsName s1 z} {v12 : ∀ z ∈ T2, IsName s1 z}
variable {v2 : ∀ z ∈ T, IsName s2 z} {v22 : ∀ z ∈ T2, IsName s2 z}
local notation "I0" => M.niceRefinementIndices a0 s0 b d level0 T T2 v0
local notation "I1" => M.niceRefinementIndices a1 s1 b d level1 T T2 v1
local notation "I2" => M.niceRefinementIndices a2 s2 b d level2 T T2 v2

theorem three_anchor_data
    (first : NiceRefinementIndexSystem M a0 s0 b d level0 T T2 v0 v02)
    (second : NiceRefinementIndexSystem M a1 s1 b d level1 T T2 v1 v12)
    (third : NiceRefinementIndexSystem M a2 s2 b d level2 T T2 v2 v22)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (nodes : b.carrier ∈ M.sets) :
    (I0 ∪ I1) ∪ I2 ∈ M.sets ∧
      refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) b.carrier 2 ∈ M.sets ∧
      ZFSet.IsFunc ((I0 ∪ I1) ∪ I2) b.carrier
        (refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) b.carrier 2) ∧
      refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) b.carrier 2 =
        (refinementIndexFieldGraph I0 b.carrier 2 ∪ refinementIndexFieldGraph I1 b.carrier 2) ∪
          refinementIndexFieldGraph I2 b.carrier 2 := by
  obtain ⟨oldGround, _, oldFunction, _⟩ :=
    first.union_anchor_data second pairing unions powers separation nodes
  have ground := M.binary_union_mem pairing unions oldGround third.index_ground
  refine ⟨ground, M.refinementIndexFieldGraph_mem pairing unions powers separation ground nodes 2,
    refinementIndexFieldGraph_function_union 2 oldFunction ?_,
    refinementIndexFieldGraph_three_union I0 I1 I2 b.carrier 2⟩
  apply refinementIndexFieldGraph_function
  intro z hz
  obtain ⟨C, E, U, Rf, Rc, equal⟩ := third.decoded z hz
  exact ⟨![level2, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val], equal, b.encode_mem E⟩

end NiceRefinementIndexSystem

end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L : Type u} [PartialOrder L] [OrderBot L]
variable (s : Presentation L) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hC : C ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include pairing unions powers separation collection infinite choice hL order hC directed countable_bound

theorem binaryRowStageOneDataBound {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) :
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C one
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode one) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let tuples := liftedRowTupleFamily c (c.encode one) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets) (I anchors : ZFSet.{u}),
      I ∈ M.sets → anchors ∈ M.sets → ZFSet.IsFunc I s.carrier anchors →
    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
      A ∈ M.groundSmallSubsets (stageOneAssignments I lifted) ZFSet.omega →
    ∀ (extra : ZFSet.{u}), extra ∈ M.sets → extra ⊆ s.carrier →
      M.groundEmbeddable extra ZFSet.omega →
    ∃ D : L,
      (∀ x : L, s.encode x ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) ∧
      (∀ x : L, s.encode x ∈ extra → x ≤ D) := by
  intro c rows S T valid lifted tuples hLifted I anchors hI hAnchors anchorFunction p A member extra hExtra extraSubset smallExtra
  have nonbottom := M.nonbottom_carrier_mem s separation hL
  have hS := M.rowPositionSequences_mem pairing unions powers separation hL order nonbottom hmu
  have hTuples := M.binaryLiftedRowTupleFamily_mem pairing unions powers separation collection infinite
    hL order nonbottom hC hmu one valid
  obtain ⟨hA,subset,smallA⟩ := (M.mem_groundSmallSubsets (stageOneAssignments I lifted) ZFSet.omega A).1 member
  have whole := M.stageOneDataBounds_mem pairing unions powers separation hA hI hLifted hS hL
    hmu nonbottom order hAnchors hTuples
  have total := stageOneDataBounds_total s directed subset anchorFunction
    (liftedRowTupleFamily_surjective c (c.encode one) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid)
    (fun f hf => by
      obtain ⟨D,hD,bound⟩ := M.rowPositionSequence_bound hf
      obtain ⟨D,rfl⟩ := (s.mem_carrier D).1 hD
      exact ⟨D,bound⟩)
  obtain ⟨hUsed,smallUsed⟩ := M.countablePartialFunctions_rowSupport pairing unions powers separation
    infinite choice nonbottom hC (M.natSetCode_mem separation infinite 2) (SetMembers.raw_mem p)
  have usedSubset : rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) ⊆ s.carrier := by
    intro x hx
    exact ((s.mem_nonbottom_carrier x).1 (rowUsedRows_subset _ _ _ _ hx)).1
  obtain ⟨D,_,_,_,_,_,_,_,_,_,_,bounds,usedBound,extraBound⟩ :=
    M.exists_stageOneDataBound s pairing unions powers separation infinite choice hA hL whole smallA total
      hUsed hExtra usedSubset extraSubset smallUsed smallExtra countable_bound
  exact ⟨D,usedBound,bounds,extraBound⟩

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G P Q : Type u}
variable [PartialOrder L] [OrderBot L] [Group G] [PartialOrder P] [OrderTop P] [PartialOrder Q] [OrderTop Q]
variable (s : Presentation L) (C : ZFSet.{u})
variable (e : PosetAction G P) (t : Presentation P)
variable (e2 : PosetAction G Q) (t2 : Presentation Q) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hC : C ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include pairing unions powers separation collection infinite choice hL order hC directed countable_bound

theorem binaryRowStageThreeDataBound {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C one
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode one) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let tuples := liftedRowTupleFamily c (c.encode one) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets) (a : PosetAction G (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) (T2 : ZFSet.{u})
      (valid0 : ∀ z ∈ lifted, IsName c.pairEmpty z) (valid02 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (valid1 : ∀ z ∈ lifted, IsName t z) (valid12 : ∀ z ∈ T2, IsName t z)
      (valid2 : ∀ z ∈ lifted, IsName t2 z) (valid22 : ∀ z ∈ T2, IsName t2 z)
      (_first : NiceRefinementIndexSystem M a c.pairEmpty s d ∅ lifted T2 valid0 valid02)
      (_second : NiceRefinementIndexSystem M e t s d (natSetCode 1) lifted T2 valid1 valid12)
      (_third : NiceRefinementIndexSystem M e2 t2 s d (natSetCode 2) lifted T2 valid2 valid22),
    let I0 := M.niceRefinementIndices a c.pairEmpty s d ∅ lifted T2 valid0
    let I1 := M.niceRefinementIndices e t s d (natSetCode 1) lifted T2 valid1
    let I2 := M.niceRefinementIndices e2 t2 s d (natSetCode 2) lifted T2 valid2
    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
      A ∈ M.groundSmallSubsets (stageOneAssignments ((I0 ∪ I1) ∪ I2) lifted) ZFSet.omega →
    ∀ (extra : ZFSet.{u}), extra ∈ M.sets → extra ⊆ s.carrier →
      M.groundEmbeddable extra ZFSet.omega →
    ∃ D : L,
      (∀ x : L, s.encode x ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A ((I0 ∪ I1) ∪ I2) lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder
          (refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) s.carrier 2) tuples) ∧
      (∀ x : L, s.encode x ∈ extra → x ≤ D) := by
  let instSmallFunctionOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let instSmallFunctionTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro c rows S T valid lifted tuples hLifted a T2 valid0 valid02 valid1 valid12 valid2 valid22 first second third I0 I1 I2
    p A member extra hExtra extraSubset extraSmall
  obtain ⟨indexGround, anchorGround, anchorFunction, _⟩ :=
    first.three_anchor_data second third pairing unions powers separation hL
  exact M.binaryRowStageOneDataBound s C pairing unions powers separation collection infinite choice
    hL order hC directed countable_bound hmu one valid hLifted ((I0 ∪ I1) ∪ I2)
    (refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) s.carrier 2) indexGround anchorGround anchorFunction
    p A member extra hExtra extraSubset extraSmall

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [PartialOrder L] [OrderBot L] [Group G] [PartialOrder P] [OrderTop P]
variable (s : Presentation L) (C : ZFSet.{u})
variable (e : PosetAction G P) (t : Presentation P) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hC : C ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include pairing unions powers separation collection infinite choice hL order hC directed countable_bound

theorem binaryRowStageTwoDataBound {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C one
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode one) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let tuples := liftedRowTupleFamily c (c.encode one) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets) (a : PosetAction G (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) (T2 : ZFSet.{u})
      (valid0 : ∀ z ∈ lifted, IsName c.pairEmpty z) (valid02 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (valid1 : ∀ z ∈ lifted, IsName t z) (valid12 : ∀ z ∈ T2, IsName t z)
      (_first : NiceRefinementIndexSystem M a c.pairEmpty s d ∅ lifted T2 valid0 valid02)
      (_second : NiceRefinementIndexSystem M e t s d (natSetCode 1) lifted T2 valid1 valid12),
    let I0 := M.niceRefinementIndices a c.pairEmpty s d ∅ lifted T2 valid0
    let I1 := M.niceRefinementIndices e t s d (natSetCode 1) lifted T2 valid1
    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
      A ∈ M.groundSmallSubsets (stageOneAssignments (I0 ∪ I1) lifted) ZFSet.omega →
    ∀ (extra : ZFSet.{u}), extra ∈ M.sets → extra ⊆ s.carrier →
      M.groundEmbeddable extra ZFSet.omega →
    ∃ D : L,
      (∀ x : L, s.encode x ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A (I0 ∪ I1) lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder
          (refinementIndexFieldGraph (I0 ∪ I1) s.carrier 2) tuples) ∧
      (∀ x : L, s.encode x ∈ extra → x ≤ D) := by
  let instSmallFunctionOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let instSmallFunctionTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro c rows S T valid lifted tuples hLifted a T2 valid0 valid02 valid1 valid12 first second I0 I1
    p A member extra hExtra extraSubset extraSmall
  obtain ⟨indexGround, anchorGround, anchorFunction, _⟩ :=
    first.union_anchor_data second pairing unions powers separation hL
  exact M.binaryRowStageOneDataBound s C pairing unions powers separation collection infinite choice
    hL order hC directed countable_bound hmu one valid hLifted (I0 ∪ I1)
    (refinementIndexFieldGraph (I0 ∪ I1) s.carrier 2) indexGround anchorGround anchorFunction
    p A member extra hExtra extraSubset extraSmall

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hT : T ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "I" => I0 ∪ M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid

structure StageTwoPositionSupport (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u})
    (action : letI := smallOrder; PosetAction G (Shrink Condition)) : Prop where
  bounds : letI := smallOrder
    ∀ (q : Shrink Condition) (extra : ZFSet.{u}),
      extra ∈ M.sets → extra ⊆ b.carrier → M.groundEmbeddable extra ZFSet.omega →
      ∃ D : L,
        (∀ x : L, b.encode x ∈ used ((equivShrink Condition).symm q).row → x ≤ D) ∧
        (∀ z ∈ ((equivShrink Condition).symm q).assignments,
          ZFSet.pair z (b.encode D) ∈ stageOneDataBounds ((equivShrink Condition).symm q).assignments
            I T S b.carrier mu X b.conditionOrder (refinementIndexFieldGraph I b.carrier 2) tuples) ∧
        (∀ x : L, b.encode x ∈ extra → x ≤ D) ∧
        (∀ g ∈ d.principalFix D, action.iso g q = q)

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [PartialOrder L] [OrderBot L] [Group G] [PartialOrder P] [OrderTop P]
variable (e : PosetAction G P) (t : Presentation P)
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include order choice countable_bound

theorem binaryRowStageTwoPositionSupport {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
    let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
    ∀ (hLifted : lifted ∈ M.sets)
      (valid0 : ∀ z ∈ lifted, IsName c.pairEmpty z) (valid02 : ∀ z ∈ squared, IsName c.pairEmpty z)
      (valid1 : ∀ z ∈ lifted, IsName t z) (valid12 : ∀ z ∈ squared, IsName t z)
      (_indices0 : NiceRefinementIndexSystem M act c.pairEmpty s a ∅ lifted squared valid0 valid02)
      (_indices1 : NiceRefinementIndexSystem M e t s a (natSetCode 1) lifted squared valid1 valid12)
      (_params0 : StageOneActionParameters M act c.pairEmpty b s a lifted squared valid0)
      (_params1 : StageOneActionParameters M e t b s a lifted squared valid1)
      (system1 : NiceNameSystem M e t s a ⊥ directed lifted valid1)
      (carrier1 : t.carrier ∈ M.sets) (order1 : t.conditionOrder ∈ M.sets),
      let I0 := M.niceRefinementIndices act c.pairEmpty s a ∅ lifted squared valid0
      let image := M.stageTwoAssignmentImage act c.pairEmpty e t s a lifted squared valid0 valid02 valid1 valid12
      ∀ inputs : StageTwoConditionActionInputs M c I0 e t s a lifted squared valid1
        pairing unions powers separation collection carrier1 order1 hLifted ⊥ directed system1 act image,
      (∀ (D : L), ∀ f ∈ S, ∀ u : Name t, ZFSet.pair f u.val ∈ tuples →
        RowPositionBound mu s.nonbottom.carrier s.conditionOrder f (s.encode D) →
        a.principalFix D ≤ e.stabilizer t u) →
      StageTwoPositionSupport M c I0 e t s a lifted squared valid1
        pairing unions powers separation collection carrier1 order1 hLifted ⊥ directed system1
        S mu s.nonbottom.carrier tuples
        (fun p => rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p))
        (M.stageTwoSmallAction c I0 e t s a lifted squared valid1
          pairing unions powers separation collection carrier1 order1 hLifted ⊥ directed system1 act image inputs) := by
  let instSmallFunctionOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let instSmallFunctionTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared tuples hLifted valid0 valid02 valid1 valid12
    indices0 indices1 params0 params1 system1 carrier1 order1 I0 image inputs support1
  let instStageTwoConditionSmallOrder := M.stageTwoConditionSmallOrder c I0 e t s a lifted squared valid1
    pairing unions powers separation collection carrier1 order1 hLifted ⊥ directed system1
  refine ⟨?_⟩
  intro q extra hExtra extraSubset extraSmall
  let p := (equivShrink _).symm q
  obtain ⟨D, rowBound, dataBound, extraBound⟩ :=
    M.binaryRowStageTwoDataBound s C e t a pairing unions powers separation collection infinite choice
      hL order hC directed countable_bound hmu ⊤ valid hLifted act squared valid0 valid02 valid1 valid12
      indices0 indices1 p.row p.assignments p.assignments_mem extra hExtra extraSubset extraSmall
  refine ⟨D, rowBound, dataBound, extraBound, ?_⟩
  intro g actor
  have coordinates := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation hL) hC
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  have forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  apply M.stageTwoSmallAction_fixed_of_dataBound act c.pairEmpty c e t s a lifted squared
    valid0 valid02 valid1 valid12 b pairing unions powers separation collection
    (M.pairEmpty_carrier_mem pairing unions powers separation c carrier)
    (M.pairEmpty_order_mem pairing unions powers separation c carrier forcingOrder)
    carrier1 order1 params0 params1 hLifted ⊥ directed system1 indices0.levelCode indices1.levelCode inputs
    S mu s.nonbottom.carrier tuples D
    (fun f _ u entry bound => M.liftedRowTuple_supported a s b C pairing unions powers separation
      infinite hL hC hG graph hmu ordinal valid f u D entry bound.2)
    (support1 D) g actor q
  · exact M.internalRowAction_eq_of_principalFix a s b C pairing unions powers separation infinite
      hL hC hG graph g p.row D (fun i used => rowBound i.val used) actor
  · exact dataBound

end TransitiveGround

open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageTwoSupportData (M : TransitiveGround.{u})
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u}) : Prop where
  action_data : StageTwoActionData M a c e s actors nodes d base directed T T2 valid
    pairing unions powers separation collection
  support :
    let prior := action_data.closure_data.projection_data.carrier_data
    let next := prior.index_data.next
    let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
    let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2
      valid action_data.valid2 next.valid1 next.valid2
    letI := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
      prior.terms_ground base directed next.first
    ∀ inputs : StageTwoConditionActionInputs M c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
      prior.terms_ground base directed next.first a image,
    TransitiveGround.StageTwoPositionSupport M c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
      prior.terms_ground base directed next.first S mu X tuples used
      (M.stageTwoSmallAction c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first a image inputs)

end PartitionPilot.Forcing

end OAI
