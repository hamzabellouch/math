import Mathlib.Logic.Equiv.Option
import OAI.SetTheory.PartitionPrinciple.Definability.GroundPairedCompositionRows
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainDiagramAppend
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixFieldFamilies

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
instance withTopSmall : Small.{u} (WithTop I) :=
  small_map (Equiv.optionEquivSumPUnit I)
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def appendKey : WithTop I → ZFSet.{u}
  | none => run.indices
  | some i => run.key i

theorem appendKey_injective : Function.Injective run.appendKey := by
  intro i j equal
  cases i with
  | top =>
    cases j with
    | top => rfl
    | coe j =>
      have h := ZFSet.rank_lt_of_mem (ZFSet.mem_range.2 ⟨j, rfl⟩ : run.key j ∈ run.indices)
      change run.indices = run.key j at equal
      exact False.elim ((ne_of_lt h) (congrArg ZFSet.rank equal).symm)
  | coe i =>
    cases j with
    | top =>
      have h := ZFSet.rank_lt_of_mem (ZFSet.mem_range.2 ⟨i, rfl⟩ : run.key i ∈ run.indices)
      exact False.elim ((ne_of_lt h) (congrArg ZFSet.rank equal))
    | coe j => exact congrArg (fun k : I => (k : WithTop I)) (run.key_injective equal)

theorem appendKey_order (i j : WithTop I) :
    i ≤ j ↔ run.appendKey i = run.appendKey j ∨ run.appendKey i ∈ run.appendKey j := by
  cases i with
  | top =>
    cases j with
    | top => exact iff_of_true le_rfl (Or.inl rfl)
    | coe j =>
      have lower := ZFSet.rank_lt_of_mem (ZFSet.mem_range.2 ⟨j, rfl⟩ : run.key j ∈ run.indices)
      constructor
      · exact fun h => False.elim (WithTop.not_top_le_coe j h)
      · rintro (equal | member)
        · exact False.elim ((ne_of_lt lower) (congrArg ZFSet.rank equal).symm)
        · exact False.elim (lt_asymm lower (ZFSet.rank_lt_of_mem member))
  | coe i =>
    cases j with
    | top => exact iff_of_true le_top (Or.inr (ZFSet.mem_range.2 ⟨i, rfl⟩))
    | coe j => exact WithTop.coe_le_coe.trans (run.key_order i j)

theorem appendKey_range : ZFSet.range run.appendKey = insert run.indices run.indices := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_range, ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | top => exact Or.inl rfl
    | coe i => exact Or.inr (ZFSet.mem_range.2 ⟨i, rfl⟩)
  · rintro (rfl | hz)
    · exact ⟨⊤, rfl⟩
    · obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hz
      exact ⟨(i : WithTop I), rfl⟩

theorem indices_of_greatest (last : I) (greatest : ∀ i, i ≤ last) :
    run.indices = insert (run.key last) (run.key last) := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_insert_iff]
  constructor
  · intro hz
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hz
    exact (run.key_order i last).1 (greatest i)
  · rintro (rfl | hz)
    · exact ZFSet.mem_range.2 ⟨last, rfl⟩
    · exact run.indices_ordinal.1 _ (ZFSet.mem_range.2 ⟨last, rfl⟩) z hz

def appendLinked (target : GroundLinkedMainStage M K Labels C D rD) :
    WithTop I → GroundLinkedMainStage M K Labels C D rD
  | none => target
  | some i => run.linked i

theorem appendStageGraph_eq (target : GroundLinkedMainStage M K Labels C D rD) :
    familyCodeGraph run.appendKey (fun i => (run.appendLinked target i).code) =
      insert (ZFSet.pair run.indices target.code) run.stageGraph := by
  apply ZFSet.ext
  intro z
  rw [mem_familyCodeGraph, ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | top => exact Or.inl rfl
    | coe i => exact Or.inr ((mem_familyCodeGraph _ _ _).2 ⟨i, rfl⟩)
  · rintro (rfl | hz)
    · exact ⟨⊤, rfl⟩
    · obtain ⟨i, rfl⟩ := (mem_familyCodeGraph _ _ _).1 hz
      exact ⟨(i : WithTop I), rfl⟩

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing
open SetFormula
universe u v

theorem relationCompose_uniformSource_eq {A B C R f g : ZFSet.{u}}
    (member : f ∈ R) (shape : f ⊆ ZFSet.prod A B) :
    relationCompose (⋃₀ ⋃₀ ⋃₀ R) B C f g = relationCompose A B C f g := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, _, y, hy, w, hw, rfl, xy, yw⟩ := (mem_relationCompose _ _ _ _ _ z).1 hz
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨(ZFSet.pair_mem_prod.1 (shape xy)).1, hw, y, hy, xy, yw⟩
  · intro hz
    obtain ⟨x, _, y, hy, w, hw, rfl, xy, yw⟩ := (mem_relationCompose _ _ _ _ _ z).1 hz
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨pair_first_mem_doubleUnion (ZFSet.mem_sUnion.2 ⟨f, member, xy⟩), hw, y, hy, xy, yw⟩

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_appendRow (last : I) (greatest : ∀ i, i ≤ last)
    (target : GroundLinkedMainStage M K Labels C D rD)
    (step : GroundChronologicalMainTransition (run.diagram.stage last) target.main) :
    ∃ row ∈ M.sets, FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row ∧
      ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
        z = ((run.diagram.transition (greatest i)).comp pairing unions powers separation step).map.code := by
  let V := ⋃₀ ⋃₀ run.transitionGraph
  let F := indexedRelationSection run.indices V run.transitionGraph (run.key last)
  have hV : V ∈ M.sets := M.union_mem unions (M.union_mem unions run.transitions_ground)
  have hLast := M.transitive run.indices_ground (ZFSet.mem_range.2 ⟨last, rfl⟩)
  have hF : F ∈ M.sets := M.indexedRelationSection_mem pairing unions powers separation
    run.indices_ground hV run.transitions_ground hLast
  have oldEntry (i : I) : ZFSet.pair (run.key i) (run.diagram.transition (greatest i)).map.code ∈ F := by
    have old := (run.transitionGraph_entry (greatest i) _).2 rfl
    exact (pair_mem_indexedRelationSection _ _ _ _ _ _).2
      ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, pair_second_mem_doubleUnion old, old⟩
  have oldUnique (i : I) (z : ZFSet.{u}) (entry : ZFSet.pair (run.key i) z ∈ F) :
      z = (run.diagram.transition (greatest i)).map.code :=
    (run.transitionGraph_entry (greatest i) z).1
      ((pair_mem_indexedRelationSection _ _ _ _ _ _).1 entry).2.2
  let R := ⋃₀ ⋃₀ ⋃₀ ⋃₀ F
  have hR : R ∈ M.sets := M.union_mem unions (M.union_mem unions
    (M.union_mem unions (M.union_mem unions hF)))
  have mapBounds (i : I) : (run.diagram.transition (greatest i)).map.points ∈ R ∧
      (run.diagram.transition (greatest i)).map.actors ∈ R :=
    ⟨pair_first_mem_doubleUnion (pair_second_mem_doubleUnion (oldEntry i)),
      pair_second_mem_doubleUnion (pair_second_mem_doubleUnion (oldEntry i))⟩
  have function : ZFSet.IsFunc run.indices (ZFSet.prod R R) F := by
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨i, hi, value, _, rfl, entry⟩ := (mem_indexedRelationSection _ _ _ _ z).1 hz
      obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hi
      have equal := (run.transitionGraph_entry (greatest i) value).1 entry
      rw [equal]
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_range.2 ⟨i, rfl⟩,
        ZFSet.pair_mem_prod.2 (mapBounds i)⟩
    · intro x hx
      obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
      exact ⟨_, oldEntry i, oldUnique i⟩
  obtain ⟨row, ground, func, entries⟩ := M.exists_pairedCompositionRow pairing unions powers separation
    run.indices_ground run.indices_ground hR
    (M.union_mem unions (M.union_mem unions (M.union_mem unions hR)))
    (run.diagram.stage last).stage.carrier_ground target.main.stage.carrier_ground
    (run.diagram.stage last).stage.actors_ground target.main.stage.actors_ground
    hF step.map.points_ground step.map.actors_ground function
  refine ⟨row, ground, func, ?_⟩
  intro i z
  have entry := entries (run.key i) _ _ z (oldEntry i)
  rw [relationCompose_uniformSource_eq (mapBounds i).1
      (run.diagram.transition (greatest i)).map.point_embedding.injection.function.1,
    relationCompose_uniformSource_eq (mapBounds i).2
      (run.diagram.transition (greatest i)).map.group_embedding.injection.function.1] at entry
  exact entry

end GroundMainPrefix

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable {S : ZFSet.{u}} (subset : S ⊆ run.indices)
include subset

theorem restrictedKey_range :
    ZFSet.range (fun i : {i // run.key i ∈ S} => run.key i.val) = S := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact i.property
  · intro hz
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 (subset hz)
    exact ⟨⟨i, hz⟩, rfl⟩

theorem restrictedStageGraph_eq :
    familyCodeGraph (fun i : {i // run.key i ∈ S} => run.key i.val)
      (fun i => (run.linked i.val).code) = graphRestriction S run.stageGraph := by
  have equal := familyCodeGraph_restrict run.key (fun i => (run.linked i).code)
    run.key_injective (fun i => run.key i ∈ S)
  rw [run.restrictedKey_range subset] at equal
  exact equal.symm

theorem restrictedTransitionGraph_eq :
    familyCodeGraph (mainTransitionIndexKey (fun i : {i // run.key i ∈ S} => run.key i.val))
      (fun p => (run.diagram.transition (show p.val.1.val ≤ p.val.2.val from p.property)).map.code) =
        graphRestriction (chronologyPairs S) run.transitionGraph := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨p, rfl⟩ := (mem_familyCodeGraph _ _ z).1 hz
    exact pair_mem_graphRestriction.2
      ⟨(run.transitionGraph_entry p.property _).2 rfl,
        (pair_mem_chronologyPairs S _ _).2
          ⟨p.val.2.property, p.val.1.property, (run.key_order _ _).1 p.property⟩⟩
  · intro hz
    obtain ⟨q, hq, value, rfl, entry⟩ := mem_graphRestriction.1 hz
    obtain ⟨target, ht, source, hs, rfl, before⟩ := (mem_chronologyPairs S q).1 hq
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 (subset ht)
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 (subset hs)
    have ordered := (run.key_order i j).2 before
    have equal := (run.transitionGraph_entry ordered value).1 entry
    exact (mem_familyCodeGraph _ _ _).2
      ⟨⟨(⟨i, hs⟩, ⟨j, ht⟩), ordered⟩,
        congrArg (ZFSet.pair (ZFSet.pair (run.key j) (run.key i))) equal.symm⟩

noncomputable def restrict (ground : S ∈ M.sets) (ordinal : ordinalSetProperty S) :
    GroundMainPrefix M K Labels C D rD pairing unions powers separation {i // run.key i ∈ S} where
  key i := run.key i.val
  key_injective := fun _ _ equal => Subtype.ext (run.key_injective equal)
  key_order i j := run.key_order i.val j.val
  indices_ground := (run.restrictedKey_range subset).symm ▸ ground
  indices_ordinal := (run.restrictedKey_range subset).symm ▸ ordinal
  diagram := run.diagram.reindex Subtype.val (fun _ _ before => before)
  linked i := run.linked i.val
  linked_main i := run.linked_main i.val
  coverage := fun before => run.coverage before
  stages_ground := (run.restrictedStageGraph_eq subset).symm ▸
    M.graphRestriction_mem unions separation ground run.stages_ground
  transitions_ground := (run.restrictedTransitionGraph_eq subset).symm ▸
    M.graphRestriction_mem unions separation
      (M.chronologyPairs_mem pairing unions powers separation ground) run.transitions_ground

theorem restrict_indices (ground : S ∈ M.sets) (ordinal : ordinalSetProperty S) :
    (run.restrict subset ground ordinal).indices = S := run.restrictedKey_range subset

theorem restrict_stageGraph (ground : S ∈ M.sets) (ordinal : ordinalSetProperty S) :
    (run.restrict subset ground ordinal).stageGraph = graphRestriction S run.stageGraph :=
  run.restrictedStageGraph_eq subset

theorem restrict_transitionGraph (ground : S ∈ M.sets) (ordinal : ordinalSetProperty S) :
    (run.restrict subset ground ordinal).transitionGraph =
      graphRestriction (chronologyPairs S) run.transitionGraph := run.restrictedTransitionGraph_eq subset

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (target : GroundLinkedMainStage M K Labels C D rD) (cone : run.diagram.Cone target.main)

noncomputable def appendTransitionGraph : ZFSet.{u} :=
  familyCodeGraph (mainTransitionIndexKey run.appendKey)
    (fun p => (cone.append.transition p.property).map.code)

theorem appendTransitionGraph_eq {row : ZFSet.{u}}
    (function : FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row)
    (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔ z = (cone.leg i).map.code) :
    run.appendTransitionGraph target cone =
      insert (ZFSet.pair (ZFSet.pair run.indices run.indices)
        (GroundChronologicalMainTransition.identity pairing unions powers separation target.main).map.code)
        (run.transitionGraph ∪ row) := by
  apply ZFSet.ext
  intro z
  rw [appendTransitionGraph, mem_familyCodeGraph, ZFSet.mem_insert_iff, ZFSet.mem_union]
  constructor
  · rintro ⟨⟨⟨i, j⟩, before⟩, rfl⟩
    cases i with
    | top =>
      cases j with
      | top => exact Or.inl rfl
      | coe j => exact False.elim (WithTop.not_top_le_coe j before)
    | coe i =>
      cases j with
      | top => exact Or.inr (Or.inr ((entries i _).2 rfl))
      | coe j => exact Or.inr (Or.inl ((run.transitionGraph_entry (WithTop.coe_le_coe.mp before) _).2 rfl))
  · rintro (rfl | old | fresh)
    · exact ⟨⟨(⊤, ⊤), le_rfl⟩, rfl⟩
    · obtain ⟨⟨⟨i, j⟩, before⟩, rfl⟩ := (mem_familyCodeGraph _ _ _).1 old
      exact ⟨⟨((i : WithTop I), (j : WithTop I)), WithTop.coe_le_coe.mpr before⟩, rfl⟩
    · obtain ⟨key, keyMember, value, rfl⟩ := function.shape _ fresh
      obtain ⟨a, ha, x, hx, rfl⟩ := ZFSet.mem_prod.1 keyMember
      have equal := ZFSet.mem_singleton.1 ha
      subst a
      obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
      have valueEq := (entries i value).1 fresh
      exact ⟨⟨((i : WithTop I), ⊤), le_top⟩,
        congrArg (ZFSet.pair (ZFSet.pair run.indices (run.key i))) valueEq.symm⟩

noncomputable def appendCone {row : ZFSet.{u}} (ground : row ∈ M.sets)
    (function : FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row)
    (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔ z = (cone.leg i).map.code)
    (covered : cone.append.CoversOldBirths) :
    GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I) where
  key := run.appendKey
  key_injective := run.appendKey_injective
  key_order := run.appendKey_order
  indices_ground := run.appendKey_range.symm ▸ M.insert_mem pairing unions run.indices_ground run.indices_ground
  indices_ordinal := run.appendKey_range.symm ▸ ordinalSetProperty_succ run.indices_ordinal
  diagram := cone.append
  linked := run.appendLinked target
  linked_main := by
    intro i
    cases i with
    | top => rfl
    | coe i => exact run.linked_main i
  coverage := covered
  stages_ground := (run.appendStageGraph_eq target).symm ▸
    M.insert_mem pairing unions (M.orderedPair_mem pairing run.indices_ground (target.code_ground pairing)) run.stages_ground
  transitions_ground := by
    change run.appendTransitionGraph target cone ∈ M.sets
    rw [run.appendTransitionGraph_eq target cone function entries]
    exact M.insert_mem pairing unions (M.orderedPair_mem pairing
      (M.orderedPair_mem pairing run.indices_ground run.indices_ground)
      ((GroundChronologicalMainTransition.identity pairing unions powers separation target.main).map.code_mem pairing))
      (M.binary_union_mem pairing unions run.transitions_ground ground)

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem restrict_code_rank_lt {S : ZFSet.{u}} (subset : S ⊆ run.indices)
    (ground : S ∈ M.sets) (ordinal : ordinalSetProperty S)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (oldRank : ZFSet.rank run.code < o) :
    ZFSet.rank (run.restrict subset ground ordinal).code < o := by
  have indices : ZFSet.rank (run.restrict subset ground ordinal).indices < o := by
    rw [run.restrict_indices subset ground ordinal]
    exact (ZFSet.rank_mono subset).trans_lt (run.indices_rank_le_code.trans_lt oldRank)
  have stages : ZFSet.rank (run.restrict subset ground ordinal).stageGraph < o := by
    rw [run.restrict_stageGraph subset ground ordinal]
    exact (ZFSet.rank_mono (graphRestriction_subset S run.stageGraph)).trans_lt
      (run.stageGraph_rank_le_code.trans_lt oldRank)
  have transitions : ZFSet.rank (run.restrict subset ground ordinal).transitionGraph < o := by
    rw [run.restrict_transitionGraph subset ground ordinal]
    exact (ZFSet.rank_mono (graphRestriction_subset (chronologyPairs S) run.transitionGraph)).trans_lt
      (run.transitionGraph_rank_le_code.trans_lt oldRank)
  exact rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases indices (Fin.cases stages (fun _ => transitions)))

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (last : I) (greatest : ∀ i, i ≤ last)
variable (target : GroundLinkedMainStage M K Labels C D rD)
variable (step : GroundChronologicalMainTransition (run.diagram.stage last) target.main)
variable (covered : step.CoversOldBirths)

noncomputable def appendLast :
    GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I) := by
  let witnesses := run.exists_appendRow last greatest target step
  let row := Classical.choose witnesses
  have spec := Classical.choose_spec witnesses
  exact run.appendCone target (run.diagram.coneOfLast last greatest step) spec.1 spec.2.1 spec.2.2
    (run.diagram.coneOfLast_coverage last greatest step run.coverage covered)

theorem appendLast_indices :
    (run.appendLast last greatest target step covered).indices = insert run.indices run.indices :=
  run.appendKey_range

theorem appendLast_linked_old (i : I) :
    (run.appendLast last greatest target step covered).linked (i : WithTop I) = run.linked i := rfl

theorem appendLast_linked_top :
    (run.appendLast last greatest target step covered).linked ⊤ = target := rfl

theorem appendLast_transition_old {i j : I} (before : i ≤ j) :
    (run.appendLast last greatest target step covered).diagram.transition (WithTop.coe_le_coe.mpr before) =
      run.diagram.transition before := rfl

theorem appendLast_transition_to_top (i : I) :
    (run.appendLast last greatest target step covered).diagram.transition
      (show (i : WithTop I) ≤ ⊤ from le_top) =
      (run.diagram.transition (greatest i)).comp pairing unions powers separation step := rfl

theorem appendLast_transition_last :
    (run.appendLast last greatest target step covered).diagram.transition
      (show (last : WithTop I) ≤ ⊤ from le_top) = step := by
  rw [run.appendLast_transition_to_top last greatest target step covered last,
    run.diagram.self, GroundChronologicalMainTransition.identity_comp]

theorem appendLast_stageGraph :
    (run.appendLast last greatest target step covered).stageGraph =
      insert (ZFSet.pair run.indices target.code) run.stageGraph :=
  run.appendStageGraph_eq target

theorem appendLast_row :
    ∃ row ∈ M.sets, FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row ∧
      (∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
        z = ((run.diagram.transition (greatest i)).comp pairing unions powers separation step).map.code) ∧
      (run.appendLast last greatest target step covered).transitionGraph =
        insert (ZFSet.pair (ZFSet.pair run.indices run.indices)
          (GroundChronologicalMainTransition.identity pairing unions powers separation target.main).map.code)
          (run.transitionGraph ∪ row) := by
  let witnesses := run.exists_appendRow last greatest target step
  have spec := Classical.choose_spec witnesses
  refine ⟨Classical.choose witnesses, spec.1, spec.2.1, spec.2.2, ?_⟩
  exact run.appendTransitionGraph_eq target (run.diagram.coneOfLast last greatest step) spec.2.1 spec.2.2

theorem appendLast_stageGraph_restrict :
    graphRestriction run.indices (run.appendLast last greatest target step covered).stageGraph = run.stageGraph := by
  rw [run.appendLast_stageGraph last greatest target step covered]
  rw [graphRestriction_insert_of_not_mem
    (fun h => (lt_irrefl _ (ZFSet.rank_lt_of_mem h)) : run.indices ∉ run.indices)]
  exact run.stageGraph_function.restriction_eq

theorem appendLast_transitionGraph_restrict :
    graphRestriction (chronologyPairs run.indices)
      (run.appendLast last greatest target step covered).transitionGraph = run.transitionGraph := by
  let extended := run.appendLast last greatest target step covered
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨key, keyMember, value, rfl, entry⟩ := mem_graphRestriction.1 hz
    obtain ⟨j, hj, i, hi, rfl, before⟩ := (mem_chronologyPairs run.indices key).1 keyMember
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 hj
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hi
    have ordered := (run.key_order i j).2 before
    have equal := (extended.transitionGraph_entry (WithTop.coe_le_coe.mpr ordered) value).1 entry
    exact (run.transitionGraph_entry ordered value).2 equal
  · intro hz
    obtain ⟨⟨⟨i, j⟩, before⟩, rfl⟩ := (mem_familyCodeGraph _ _ _).1 hz
    exact pair_mem_graphRestriction.2
      ⟨(extended.transitionGraph_entry (WithTop.coe_le_coe.mpr before) _).2 rfl,
        (pair_mem_chronologyPairs _ _ _).2 ⟨ZFSet.mem_range.2 ⟨j, rfl⟩,
          ZFSet.mem_range.2 ⟨i, rfl⟩, (run.key_order i j).1 before⟩⟩

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u v

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}

theorem field_rank_le_linkedCode (target : GroundLinkedMainStage M K Labels C D rD) (j : Fin 11) :
    ZFSet.rank (target.main.stage.field j) ≤ ZFSet.rank target.code := by
  have stageBound : ZFSet.rank target.main.stage.code ≤ ZFSet.rank target.code := by
    simpa only [code, linkedMainStageCode, Fin.cases_zero] using
      (rank_nonemptyTupleCode_field_le 2 (Fin.cases target.main.stage.code
        (Fin.cases target.main.cutoff (fun _ => target.serial.code))) 0)
  exact (rank_nonemptyTupleCode_field_le 10 target.main.stage.field j).trans stageBound

end GroundLinkedMainStage

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def appendSourceBound : ZFSet.{u} := by
  let V : ZFSet.{u} := ⋃₀ ⋃₀ run.transitionGraph
  let R : ZFSet.{u} := ⋃₀ ⋃₀ V
  exact ⋃₀ ⋃₀ ⋃₀ R

theorem appendSourceBound_rank_le : ZFSet.rank run.appendSourceBound ≤ ZFSet.rank run.code :=
  ((ZFSet.rank_sUnion_le _).trans ((ZFSet.rank_sUnion_le _).trans
    ((ZFSet.rank_sUnion_le _).trans ((ZFSet.rank_sUnion_le _).trans
      ((ZFSet.rank_sUnion_le _).trans ((ZFSet.rank_sUnion_le _).trans
        (ZFSet.rank_sUnion_le _))))))).trans run.transitionGraph_rank_le_code

variable (last : I) (greatest : ∀ i, i ≤ last)
variable (target : GroundLinkedMainStage M K Labels C D rD)
variable (step : GroundChronologicalMainTransition (run.diagram.stage last) target.main)

theorem appendRow_subset {row : ZFSet.{u}}
    (function : FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row)
    (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
      z = ((run.diagram.transition (greatest i)).comp pairing unions powers separation step).map.code) :
    row ⊆ ZFSet.prod (ZFSet.prod {run.indices} run.indices)
      (ZFSet.prod (ZFSet.powerset (ZFSet.prod run.appendSourceBound target.main.stage.carrier))
        (ZFSet.powerset (ZFSet.prod run.appendSourceBound target.main.stage.actors))) := by
  have pointBound (i : I) :
      ((run.diagram.transition (greatest i)).comp pairing unions powers separation step).map.points ⊆
        ZFSet.prod run.appendSourceBound target.main.stage.carrier := by
    intro z hz
    obtain ⟨x, _, y, _, w, hw, rfl, xy, _⟩ := (mem_relationCompose _ _ _ _ _ z).1 hz
    have old := (run.transitionGraph_entry (greatest i) _).2 rfl
    have mapMem := pair_first_mem_doubleUnion (pair_second_mem_doubleUnion old)
    exact ZFSet.pair_mem_prod.2
      ⟨pair_first_mem_doubleUnion (ZFSet.mem_sUnion.2 ⟨_, mapMem, xy⟩), hw⟩
  have actorBound (i : I) :
      ((run.diagram.transition (greatest i)).comp pairing unions powers separation step).map.actors ⊆
        ZFSet.prod run.appendSourceBound target.main.stage.actors := by
    intro z hz
    obtain ⟨x, _, y, _, w, hw, rfl, xy, _⟩ := (mem_relationCompose _ _ _ _ _ z).1 hz
    have old := (run.transitionGraph_entry (greatest i) _).2 rfl
    have mapMem := pair_second_mem_doubleUnion (pair_second_mem_doubleUnion old)
    exact ZFSet.pair_mem_prod.2
      ⟨pair_first_mem_doubleUnion (ZFSet.mem_sUnion.2 ⟨_, mapMem, xy⟩), hw⟩
  intro z hz
  obtain ⟨key, keyMember, value, rfl⟩ := function.shape _ hz
  obtain ⟨a, ha, x, hx, rfl⟩ := ZFSet.mem_prod.1 keyMember
  have equal := ZFSet.mem_singleton.1 ha
  subst a
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
  have valueEq := (entries i value).1 hz
  rw [valueEq]
  exact ZFSet.pair_mem_prod.2
    ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, ZFSet.mem_range.2 ⟨i, rfl⟩⟩,
      ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_powerset.2 (pointBound i), ZFSet.mem_powerset.2 (actorBound i)⟩⟩

theorem appendRow_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (oldRank : ZFSet.rank run.code < o) (targetRank : ZFSet.rank target.code < o)
    {row : ZFSet.{u}} (function : FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row)
    (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
      z = ((run.diagram.transition (greatest i)).comp pairing unions powers separation step).map.code) :
    ZFSet.rank row < o := by
  have indexRank := run.indices_rank_le_code.trans_lt oldRank
  have sourceRank := run.appendSourceBound_rank_le.trans_lt oldRank
  have pointRank : ZFSet.rank target.main.stage.carrier < o :=
    (target.field_rank_le_linkedCode 0).trans_lt targetRank
  have actorRank : ZFSet.rank target.main.stage.actors < o :=
    (target.field_rank_le_linkedCode 3).trans_lt targetRank
  have points : ZFSet.rank (ZFSet.powerset (ZFSet.prod run.appendSourceBound target.main.stage.carrier)) < o := by
    rw [ZFSet.rank_powerset]
    exact limit.succ_lt (rank_product_lt limit sourceRank pointRank)
  have actors : ZFSet.rank (ZFSet.powerset (ZFSet.prod run.appendSourceBound target.main.stage.actors)) < o := by
    rw [ZFSet.rank_powerset]
    exact limit.succ_lt (rank_product_lt limit sourceRank actorRank)
  exact (ZFSet.rank_mono (run.appendRow_subset last greatest target step function entries)).trans_lt
    (rank_product_lt limit (rank_product_lt limit (rank_singleton_lt limit indexRank) indexRank)
      (rank_product_lt limit points actors))

theorem appendLast_code_rank_lt (covered : step.CoversOldBirths)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (oldRank : ZFSet.rank run.code < o) (targetRank : ZFSet.rank target.code < o) :
    ZFSet.rank (run.appendLast last greatest target step covered).code < o := by
  let extended := run.appendLast last greatest target step covered
  have indexRank := run.indices_rank_le_code.trans_lt oldRank
  have newIndices : ZFSet.rank extended.indices < o := by
    rw [run.appendLast_indices last greatest target step covered, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt indexRank) indexRank
  have newStages : ZFSet.rank extended.stageGraph < o := by
    rw [run.appendLast_stageGraph last greatest target step covered, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt (rank_orderedPair_lt limit indexRank targetRank))
      (run.stageGraph_rank_le_code.trans_lt oldRank)
  have newTransitions : ZFSet.rank extended.transitionGraph < o := by
    obtain ⟨row, _, function, entries, equal⟩ := run.appendLast_row last greatest target step covered
    rw [equal, ZFSet.rank_insert, ZFSet.rank_union]
    have pointRank : ZFSet.rank target.main.stage.carrier < o :=
      (target.field_rank_le_linkedCode 0).trans_lt targetRank
    have actorRank : ZFSet.rank target.main.stage.actors < o :=
      (target.field_rank_le_linkedCode 3).trans_lt targetRank
    have identityRank := (GroundChronologicalMainTransition.identity pairing unions powers separation target.main).map.code_rank_lt
      limit pointRank pointRank actorRank actorRank
    exact max_lt (limit.succ_lt (rank_orderedPair_lt limit (rank_orderedPair_lt limit indexRank indexRank) identityRank))
      (max_lt (run.transitionGraph_rank_le_code.trans_lt oldRank)
        (run.appendRow_rank_lt last greatest target step limit oldRank targetRank function entries))
  exact rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases newIndices (Fin.cases newStages (fun _ => newTransitions)))

end GroundMainPrefix
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (target : GroundLinkedMainStage M K Labels C D rD) (cone : run.diagram.Cone target.main)
variable {row : ZFSet.{u}} (ground : row ∈ M.sets)
variable (function : FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row)
variable (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔ z = (cone.leg i).map.code)
variable (covered : cone.append.CoversOldBirths)

theorem appendCone_indices :
    (run.appendCone target cone ground function entries covered).indices = insert run.indices run.indices :=
  run.appendKey_range

theorem appendCone_stage_old (i : I) :
    (run.appendCone target cone ground function entries covered).diagram.stage (i : WithTop I) =
      run.diagram.stage i := rfl

theorem appendCone_stage_top :
    (run.appendCone target cone ground function entries covered).diagram.stage ⊤ = target.main := rfl

theorem appendCone_linked_old (i : I) :
    (run.appendCone target cone ground function entries covered).linked (i : WithTop I) = run.linked i := rfl

theorem appendCone_linked_top :
    (run.appendCone target cone ground function entries covered).linked ⊤ = target := rfl

theorem appendCone_transition_old {i j : I} (before : i ≤ j) :
    (run.appendCone target cone ground function entries covered).diagram.transition
      (WithTop.coe_le_coe.mpr before) = run.diagram.transition before := rfl

theorem appendCone_transition_to_top (i : I) :
    (run.appendCone target cone ground function entries covered).diagram.transition
      (show (i : WithTop I) ≤ ⊤ from le_top) = cone.leg i := rfl

theorem appendCone_transition_top :
    (run.appendCone target cone ground function entries covered).diagram.transition
      (show (⊤ : WithTop I) ≤ ⊤ from le_rfl) =
        GroundChronologicalMainTransition.identity pairing unions powers separation target.main := rfl

theorem appendCone_stageGraph :
    (run.appendCone target cone ground function entries covered).stageGraph =
      insert (ZFSet.pair run.indices target.code) run.stageGraph :=
  run.appendStageGraph_eq target

theorem appendCone_transitionGraph :
    (run.appendCone target cone ground function entries covered).transitionGraph =
      insert (ZFSet.pair (ZFSet.pair run.indices run.indices)
        (GroundChronologicalMainTransition.identity pairing unions powers separation target.main).map.code)
        (run.transitionGraph ∪ row) :=
  run.appendTransitionGraph_eq target cone function entries

theorem appendCone_stageGraph_restrict :
    graphRestriction run.indices (run.appendCone target cone ground function entries covered).stageGraph =
      run.stageGraph := by
  rw [run.appendCone_stageGraph target cone ground function entries covered]
  rw [graphRestriction_insert_of_not_mem (ZFSet.mem_irrefl run.indices)]
  exact run.stageGraph_function.restriction_eq

theorem appendCone_transitionGraph_restrict :
    graphRestriction (chronologyPairs run.indices)
      (run.appendCone target cone ground function entries covered).transitionGraph = run.transitionGraph := by
  let extended := run.appendCone target cone ground function entries covered
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨key, keyMember, value, rfl, entry⟩ := mem_graphRestriction.1 hz
    obtain ⟨j, hj, i, hi, rfl, before⟩ := (mem_chronologyPairs run.indices key).1 keyMember
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 hj
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hi
    have ordered := (run.key_order i j).2 before
    have equal := (extended.transitionGraph_entry (WithTop.coe_le_coe.mpr ordered) value).1 entry
    exact (run.transitionGraph_entry ordered value).2 equal
  · intro hz
    obtain ⟨⟨⟨i, j⟩, before⟩, rfl⟩ := (mem_familyCodeGraph _ _ _).1 hz
    exact pair_mem_graphRestriction.2
      ⟨(extended.transitionGraph_entry (WithTop.coe_le_coe.mpr before) _).2 rfl,
        (pair_mem_chronologyPairs _ _ _).2 ⟨ZFSet.mem_range.2 ⟨j, rfl⟩,
          ZFSet.mem_range.2 ⟨i, rfl⟩, (run.key_order i j).1 before⟩⟩

theorem appendCone_code_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (oldRank : ZFSet.rank run.code < o) (targetRank : ZFSet.rank target.code < o)
    (rowRank : ZFSet.rank row < o) :
    ZFSet.rank (run.appendCone target cone ground function entries covered).code < o := by
  let extended := run.appendCone target cone ground function entries covered
  have indexRank := run.indices_rank_le_code.trans_lt oldRank
  have newIndices : ZFSet.rank extended.indices < o := by
    rw [run.appendCone_indices target cone ground function entries covered, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt indexRank) indexRank
  have newStages : ZFSet.rank extended.stageGraph < o := by
    rw [run.appendCone_stageGraph target cone ground function entries covered, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt (rank_orderedPair_lt limit indexRank targetRank))
      (run.stageGraph_rank_le_code.trans_lt oldRank)
  have newTransitions : ZFSet.rank extended.transitionGraph < o := by
    rw [run.appendCone_transitionGraph target cone ground function entries covered,
      ZFSet.rank_insert, ZFSet.rank_union]
    have pointRank : ZFSet.rank target.main.stage.carrier < o :=
      (target.field_rank_le_linkedCode 0).trans_lt targetRank
    have actorRank : ZFSet.rank target.main.stage.actors < o :=
      (target.field_rank_le_linkedCode 3).trans_lt targetRank
    have identityRank := (GroundChronologicalMainTransition.identity pairing unions powers separation target.main).map.code_rank_lt
      limit pointRank pointRank actorRank actorRank
    exact max_lt (limit.succ_lt (rank_orderedPair_lt limit (rank_orderedPair_lt limit indexRank indexRank) identityRank))
      (max_lt (run.transitionGraph_rank_le_code.trans_lt oldRank) rowRank)
  exact rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases newIndices (Fin.cases newStages (fun _ => newTransitions)))

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
