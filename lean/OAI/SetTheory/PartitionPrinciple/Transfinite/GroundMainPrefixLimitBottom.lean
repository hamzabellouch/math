import OAI.SetTheory.PartitionPrinciple.Geometry.GroundIndexedOperationLifts
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixLimitGroupLaws

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix

section
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

def LimitLE (p q : ZFSet.{u}) : Prop :=
  ∃ i x y, x ∈ (run.diagram.stage i).stage.carrier ∧
    y ∈ (run.diagram.stage i).stage.carrier ∧
    p = run.pointPresentation.limitPoint i x ∧ q = run.pointPresentation.limitPoint i y ∧
    ZFSet.pair x y ∈ (run.diagram.stage i).stage.order

theorem point_order_congr {i j : I} {x y a b : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage i).stage.carrier)
    (ha : a ∈ (run.diagram.stage j).stage.carrier)
    (hb : b ∈ (run.diagram.stage j).stage.carrier)
    (first : run.pointPresentation.limitPoint i x = run.pointPresentation.limitPoint j a)
    (second : run.pointPresentation.limitPoint i y = run.pointPresentation.limitPoint j b) :
    ZFSet.pair x y ∈ (run.diagram.stage i).stage.order ↔
      ZFSet.pair a b ∈ (run.diagram.stage j).stage.order := by
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  obtain ⟨x', xx'⟩ := run.pointSystem.map_entry_total ik hx
  obtain ⟨y', yy'⟩ := run.pointSystem.map_entry_total ik hy
  obtain ⟨a', aa'⟩ := run.pointSystem.map_entry_total jk ha
  obtain ⟨b', bb'⟩ := run.pointSystem.map_entry_total jk hb
  have equalX := (run.pointSystem.related_iff_common_images ik jk xx' aa').1
    ((run.pointPresentation.limitPoint_eq_iff_related hx ha).1 first)
  have equalY := (run.pointSystem.related_iff_common_images ik jk yy' bb').1
    ((run.pointPresentation.limitPoint_eq_iff_related hy hb).1 second)
  subst a'
  subst b'
  exact ((run.diagram.transition ik).map.order_iff x y x' y' xx' yy').symm.trans
    ((run.diagram.transition jk).map.order_iff a b x' y' aa' bb')

theorem limitLE_bounds {p q : ZFSet.{u}} (lower : run.LimitLE p q) :
    p ∈ run.limitPoints ∧ q ∈ run.limitPoints := by
  obtain ⟨i, x, y, hx, hy, rfl, rfl, _⟩ := lower
  exact ⟨run.pointPresentation.limitPoint_mem hx, run.pointPresentation.limitPoint_mem hy⟩

theorem limitLE_at (i : I) {x y : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage i).stage.carrier) :
    run.LimitLE (run.pointPresentation.limitPoint i x) (run.pointPresentation.limitPoint i y) ↔
      ZFSet.pair x y ∈ (run.diagram.stage i).stage.order := by
  constructor
  · rintro ⟨j, a, b, ha, hb, first, second, lower⟩
    exact (run.point_order_congr hx hy ha hb first second).2 lower
  · intro lower
    exact ⟨i, x, y, hx, hy, rfl, rfl, lower⟩

theorem limitLE_refl {p : ZFSet.{u}} (member : p ∈ run.limitPoints) : run.LimitLE p p := by
  obtain ⟨i, x, hx, rfl⟩ := run.pointPresentation.limitPoint_coverage member
  exact (run.limitLE_at i hx hx).2 ((run.diagram.stage i).stage.meet.order.refl x hx)

theorem limitLE_antisymm {p q : ZFSet.{u}}
    (first : run.LimitLE p q) (second : run.LimitLE q p) : p = q := by
  obtain ⟨i, x, y, hx, hy, rfl, rfl⟩ := run.pointPresentation.pair_coverage
    (run.limitLE_bounds first).1 (run.limitLE_bounds first).2
  have equal := (run.diagram.stage i).stage.meet.order.antisymm x hx y hy
    ((run.limitLE_at i hx hy).1 first) ((run.limitLE_at i hy hx).1 second)
  exact congrArg (run.pointPresentation.limitPoint i) equal

theorem limitLE_trans {p q r : ZFSet.{u}}
    (first : run.LimitLE p q) (second : run.LimitLE q r) : run.LimitLE p r := by
  obtain ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl⟩ := run.pointPresentation.triple_coverage
    (run.limitLE_bounds first).1 (run.limitLE_bounds first).2 (run.limitLE_bounds second).2
  exact (run.limitLE_at i hx hz).2 ((run.diagram.stage i).stage.meet.order.trans x hx y hy z hz
    ((run.limitLE_at i hx hy).1 first) ((run.limitLE_at i hy hz).1 second))

end

section
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank run.code < o)
include limit rank

theorem limitPointLabels_rank_lt : ZFSet.rank run.limitPointLabels < o :=
  indexedCarrierLabels_rank_lt limit run.carrierFamily
    (run.indices_rank_le_code.trans_lt rank) (run.carrierUnion_rank_le_code.trans_lt rank)

theorem limitPointRelation_rank_lt : ZFSet.rank run.limitPointRelation < o :=
  directLimitRelation_rank_lt limit run.indices run.carrierUnion run.pointMapFamily
    (run.limitPointLabels_rank_lt limit rank)

theorem limitPoints_rank_lt : ZFSet.rank run.limitPoints < o :=
  equivalenceClasses_rank_lt limit run.limitPointRelation (run.limitPointLabels_rank_lt limit rank)

theorem limitPointMap_rank_lt (i : I) : ZFSet.rank (run.limitPointMap i) < o :=
  indexedClassInclusion_rank_lt limit run.limitPointRelation (run.key i)
    (run.carrierUnion_rank_le_code.trans_lt rank) (run.limitPointLabels_rank_lt limit rank)

theorem limitPointInclusions_rank_lt : ZFSet.rank run.limitPointInclusions < o :=
  M.indexedClassInclusions_rank_lt limit run.limitPointRelation
    (run.indices_rank_le_code.trans_lt rank) (run.carrierUnion_rank_le_code.trans_lt rank)
    (run.limitPointLabels_rank_lt limit rank)

theorem limitActorLabels_rank_lt : ZFSet.rank run.limitActorLabels < o :=
  indexedCarrierLabels_rank_lt limit run.actorFamily
    (run.indices_rank_le_code.trans_lt rank) (run.actorUnion_rank_le_code.trans_lt rank)

theorem limitActorRelation_rank_lt : ZFSet.rank run.limitActorRelation < o :=
  directLimitRelation_rank_lt limit run.indices run.actorUnion run.actorMapFamily
    (run.limitActorLabels_rank_lt limit rank)

theorem limitActors_rank_lt : ZFSet.rank run.limitActors < o :=
  equivalenceClasses_rank_lt limit run.limitActorRelation (run.limitActorLabels_rank_lt limit rank)

theorem limitActorMap_rank_lt (i : I) : ZFSet.rank (run.limitActorMap i) < o :=
  indexedClassInclusion_rank_lt limit run.limitActorRelation (run.key i)
    (run.actorUnion_rank_le_code.trans_lt rank) (run.limitActorLabels_rank_lt limit rank)

theorem limitActorInclusions_rank_lt : ZFSet.rank run.limitActorInclusions < o :=
  M.indexedClassInclusions_rank_lt limit run.limitActorRelation
    (run.indices_rank_le_code.trans_lt rank) (run.actorUnion_rank_le_code.trans_lt rank)
    (run.limitActorLabels_rank_lt limit rank)

end

section
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

def LimitMeet (p q r : ZFSet.{u}) : Prop :=
  ∃ i x y z, x ∈ (run.diagram.stage i).stage.carrier ∧
    y ∈ (run.diagram.stage i).stage.carrier ∧ z ∈ (run.diagram.stage i).stage.carrier ∧
    p = run.pointPresentation.limitPoint i x ∧ q = run.pointPresentation.limitPoint i y ∧
    r = run.pointPresentation.limitPoint i z ∧
    ZFSet.pair (ZFSet.pair x y) z ∈ (run.diagram.stage i).stage.meetGraph

theorem limitMeet_bounds {p q r : ZFSet.{u}} (meet : run.LimitMeet p q r) :
    p ∈ run.limitPoints ∧ q ∈ run.limitPoints ∧ r ∈ run.limitPoints := by
  obtain ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl, _⟩ := meet
  exact ⟨run.pointPresentation.limitPoint_mem hx, run.pointPresentation.limitPoint_mem hy,
    run.pointPresentation.limitPoint_mem hz⟩

theorem limitMeet_lower_left {p q r : ZFSet.{u}} (meet : run.LimitMeet p q r) :
    run.LimitLE r p := by
  obtain ⟨i, x, y, z, hx, _, hz, rfl, rfl, rfl, entry⟩ := meet
  exact (run.limitLE_at i hz hx).2 ((run.diagram.stage i).stage.meet.lower_left x y z entry)

theorem limitMeet_lower_right {p q r : ZFSet.{u}} (meet : run.LimitMeet p q r) :
    run.LimitLE r q := by
  obtain ⟨i, x, y, z, _, hy, hz, rfl, rfl, rfl, entry⟩ := meet
  exact (run.limitLE_at i hz hy).2 ((run.diagram.stage i).stage.meet.lower_right x y z entry)

theorem limitMeet_greatest {p q r w : ZFSet.{u}} (meet : run.LimitMeet p q r)
    (first : run.LimitLE w p) (second : run.LimitLE w q) : run.LimitLE w r := by
  obtain ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl, entry⟩ := meet
  obtain ⟨j, a, ha, rfl⟩ := run.pointPresentation.limitPoint_coverage (run.limitLE_bounds first).1
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  obtain ⟨x', xx'⟩ := run.pointSystem.map_entry_total ik hx
  obtain ⟨y', yy'⟩ := run.pointSystem.map_entry_total ik hy
  obtain ⟨z', zz'⟩ := run.pointSystem.map_entry_total ik hz
  obtain ⟨a', aa'⟩ := run.pointSystem.map_entry_total jk ha
  have hx' := (run.pointSystem.map_entry_bounds ik xx').2
  have hy' := (run.pointSystem.map_entry_bounds ik yy').2
  have hz' := (run.pointSystem.map_entry_bounds ik zz').2
  have ha' := (run.pointSystem.map_entry_bounds jk aa').2
  have mapped := (run.diagram.transition ik).map.point_embedding.map_meet
    x y z x' y' z' entry xx' yy' zz'
  have ax : run.LimitLE (run.pointPresentation.limitPoint k a')
      (run.pointPresentation.limitPoint k x') := by
    rw [← run.pointPresentation.limitPoint_transition jk aa',
      ← run.pointPresentation.limitPoint_transition ik xx']
    exact first
  have ay : run.LimitLE (run.pointPresentation.limitPoint k a')
      (run.pointPresentation.limitPoint k y') := by
    rw [← run.pointPresentation.limitPoint_transition jk aa',
      ← run.pointPresentation.limitPoint_transition ik yy']
    exact second
  rw [run.pointPresentation.limitPoint_transition jk aa',
    run.pointPresentation.limitPoint_transition ik zz']
  exact (run.limitLE_at k ha' hz').2 ((run.diagram.stage k).stage.meet.greatest
    x' y' z' a' ha' mapped ((run.limitLE_at k ha' hx').1 ax) ((run.limitLE_at k ha' hy').1 ay))

theorem limitMeet_total {p q : ZFSet.{u}} (hp : p ∈ run.limitPoints) (hq : q ∈ run.limitPoints) :
    ∃ r ∈ run.limitPoints, run.LimitMeet p q r := by
  obtain ⟨i, x, y, hx, hy, rfl, rfl⟩ := run.pointPresentation.pair_coverage hp hq
  obtain ⟨z, entry, _⟩ := (run.diagram.stage i).stage.meet.operation.2 (ZFSet.pair x y)
    (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
  have hz := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.meet.operation.1 entry)).2
  exact ⟨run.pointPresentation.limitPoint i z, run.pointPresentation.limitPoint_mem hz,
    i, x, y, z, hx, hy, hz, rfl, rfl, rfl, entry⟩

theorem limitMeet_unique {p q r s : ZFSet.{u}}
    (first : run.LimitMeet p q r) (second : run.LimitMeet p q s) : r = s :=
  run.limitLE_antisymm
    (run.limitMeet_greatest second (run.limitMeet_lower_left first) (run.limitMeet_lower_right first))
    (run.limitMeet_greatest first (run.limitMeet_lower_left second) (run.limitMeet_lower_right second))

theorem limitMeet_at (i : I) {x y z : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage i).stage.carrier)
    (hz : z ∈ (run.diagram.stage i).stage.carrier) :
    run.LimitMeet (run.pointPresentation.limitPoint i x) (run.pointPresentation.limitPoint i y)
      (run.pointPresentation.limitPoint i z) ↔
      ZFSet.pair (ZFSet.pair x y) z ∈ (run.diagram.stage i).stage.meetGraph := by
  constructor
  · intro meet
    obtain ⟨w, entry, _⟩ := (run.diagram.stage i).stage.meet.operation.2 (ZFSet.pair x y)
      (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    have hw := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.meet.operation.1 entry)).2
    have canonical : run.LimitMeet (run.pointPresentation.limitPoint i x)
        (run.pointPresentation.limitPoint i y) (run.pointPresentation.limitPoint i w) :=
      ⟨i, x, y, w, hx, hy, hw, rfl, rfl, rfl, entry⟩
    have equal := (run.pointPresentation.limitPoint_same_iff hz hw).1
      (run.limitMeet_unique meet canonical)
    subst w
    exact entry
  · intro entry
    exact ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl, entry⟩

noncomputable def limitMultiplication : ZFSet.{u} :=
  indexedBinaryLift run.indices run.actorUnion run.limitActors (run.stageFieldFamily 4) run.limitActorInclusions

noncomputable def limitInverse : ZFSet.{u} :=
  indexedRelationLift run.indices run.actorUnion run.limitActors (run.stageFieldFamily 5) run.limitActorInclusions

theorem limitMultiplication_ground : run.limitMultiplication ∈ M.sets :=
  M.indexedBinaryLift_mem pairing unions powers separation run.indices_ground run.actorUnion_ground
    run.limitActors_ground (run.stageFieldFamily_ground 4) run.limitActorInclusions_ground

theorem limitInverse_ground : run.limitInverse ∈ M.sets :=
  M.indexedRelationLift_mem pairing unions powers separation run.indices_ground run.actorUnion_ground
    run.limitActors_ground (run.stageFieldFamily_ground 5) run.limitActorInclusions_ground

theorem limitMultiplication_entry (g h k : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g h) k ∈ run.limitMultiplication ↔ run.LimitMul g h k := by
  rw [limitMultiplication, triple_mem_indexedBinaryLift]
  constructor
  · rintro ⟨_, _, _, j, hj, m, e, a, _, b, _, c, _, operation, inclusion, first, second, third, mul⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hj
    have em : m = (run.diagram.stage i).stage.multiplication := (run.stageFieldFamily_entry 4 i m).1 operation
    have ee := (run.limitActorInclusions_entry i e).1 inclusion
    subst m
    subst e
    obtain ⟨ha, eg⟩ := (run.actorPresentation.inclusion_entry i a g).1 first
    obtain ⟨hb, eh⟩ := (run.actorPresentation.inclusion_entry i b h).1 second
    obtain ⟨hc, ek⟩ := (run.actorPresentation.inclusion_entry i c k).1 third
    exact ⟨i, a, b, c, ha, hb, hc, eg, eh, ek, mul⟩
  · rintro ⟨i, a, b, c, ha, hb, hc, rfl, rfl, rfl, mul⟩
    exact ⟨run.actorPresentation.limitPoint_mem ha, run.actorPresentation.limitPoint_mem hb,
      run.actorPresentation.limitPoint_mem hc, run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩,
      (run.diagram.stage i).stage.multiplication, run.limitActorMap i,
      a, run.actorPresentation.carrier_bound i ha, b, run.actorPresentation.carrier_bound i hb,
      c, run.actorPresentation.carrier_bound i hc,
      (run.stageFieldFamily_entry 4 i _).2 rfl, (run.limitActorInclusions_entry i _).2 rfl,
      (run.actorPresentation.inclusion_entry i a _).2 ⟨ha, rfl⟩,
      (run.actorPresentation.inclusion_entry i b _).2 ⟨hb, rfl⟩,
      (run.actorPresentation.inclusion_entry i c _).2 ⟨hc, rfl⟩, mul⟩

theorem limitInverse_entry (g h : ZFSet.{u}) :
    ZFSet.pair g h ∈ run.limitInverse ↔ run.LimitInv g h := by
  rw [limitInverse, pair_mem_indexedRelationLift]
  constructor
  · rintro ⟨_, _, j, hj, r, e, a, _, b, _, operation, inclusion, first, second, inverse⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hj
    have er : r = (run.diagram.stage i).stage.inverse := (run.stageFieldFamily_entry 5 i r).1 operation
    have ee := (run.limitActorInclusions_entry i e).1 inclusion
    subst r
    subst e
    obtain ⟨ha, eg⟩ := (run.actorPresentation.inclusion_entry i a g).1 first
    obtain ⟨hb, eh⟩ := (run.actorPresentation.inclusion_entry i b h).1 second
    exact ⟨i, a, b, ha, hb, eg, eh, inverse⟩
  · rintro ⟨i, a, b, ha, hb, rfl, rfl, inverse⟩
    exact ⟨run.actorPresentation.limitPoint_mem ha, run.actorPresentation.limitPoint_mem hb,
      run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩, (run.diagram.stage i).stage.inverse,
      run.limitActorMap i, a, run.actorPresentation.carrier_bound i ha,
      b, run.actorPresentation.carrier_bound i hb,
      (run.stageFieldFamily_entry 5 i _).2 rfl, (run.limitActorInclusions_entry i _).2 rfl,
      (run.actorPresentation.inclusion_entry i a _).2 ⟨ha, rfl⟩,
      (run.actorPresentation.inclusion_entry i b _).2 ⟨hb, rfl⟩, inverse⟩

theorem limitMultiplication_function :
    ZFSet.IsFunc (ZFSet.prod run.limitActors run.limitActors) run.limitActors run.limitMultiplication := by
  refine ⟨indexedBinaryLift_subset _ _ _ _ _, ?_⟩
  intro p hp
  obtain ⟨g, hg, h, hh, rfl⟩ := ZFSet.mem_prod.1 hp
  obtain ⟨k, _, product⟩ := run.limitMul_total hg hh
  refine ⟨k, (run.limitMultiplication_entry g h k).2 product, ?_⟩
  intro l entry
  exact run.limitMul_unique ((run.limitMultiplication_entry g h l).1 entry) product

theorem limitInverse_function : ZFSet.IsFunc run.limitActors run.limitActors run.limitInverse := by
  refine ⟨indexedRelationLift_subset _ _ _ _ _, ?_⟩
  intro g hg
  obtain ⟨h, _, inverse⟩ := run.limitInv_total hg
  refine ⟨h, (run.limitInverse_entry g h).2 inverse, ?_⟩
  intro k entry
  exact run.limitInv_unique ((run.limitInverse_entry g k).1 entry) inverse

theorem limitMultiplication_at (i : I) {a b c : ZFSet.{u}}
    (ha : a ∈ (run.diagram.stage i).stage.actors) (hb : b ∈ (run.diagram.stage i).stage.actors)
    (hc : c ∈ (run.diagram.stage i).stage.actors) :
    ZFSet.pair (ZFSet.pair (run.actorPresentation.limitPoint i a) (run.actorPresentation.limitPoint i b))
      (run.actorPresentation.limitPoint i c) ∈ run.limitMultiplication ↔
      ZFSet.pair (ZFSet.pair a b) c ∈ (run.diagram.stage i).stage.multiplication :=
  (run.limitMultiplication_entry _ _ _).trans (run.limitMul_at i ha hb hc)

theorem limitInverse_at (i : I) {a b : ZFSet.{u}}
    (ha : a ∈ (run.diagram.stage i).stage.actors) (hb : b ∈ (run.diagram.stage i).stage.actors) :
    ZFSet.pair (run.actorPresentation.limitPoint i a) (run.actorPresentation.limitPoint i b) ∈
      run.limitInverse ↔ ZFSet.pair a b ∈ (run.diagram.stage i).stage.inverse :=
  (run.limitInverse_entry _ _).trans (run.limitInv_at i ha hb)

theorem limitMultiplication_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitMultiplication < o :=
  indexedBinaryLift_rank_lt limit _ _ _ _ (run.limitActors_rank_lt limit rank)

theorem limitInverse_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitInverse < o :=
  indexedRelationLift_rank_lt limit _ _ _ _ (run.limitActors_rank_lt limit rank)

end

section
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_limitTransitionRow {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) :
    ∃ row ∈ M.sets, FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row ∧
      (∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
        z = ZFSet.pair (run.limitPointMap i) (run.limitActorMap i)) ∧
      ZFSet.rank row < o := by
  let P := run.limitPointInclusions.sUnion.sUnion
  let A := run.limitActorInclusions.sUnion.sUnion
  let F := pairedGraph run.indices P A run.limitPointInclusions run.limitActorInclusions
  let T := ZFSet.prod {run.indices} run.indices
  let row := relationCompose T run.indices (ZFSet.prod P A)
    (productSecond {run.indices} run.indices) F
  have hP : P ∈ M.sets := M.union_mem unions (M.union_mem unions run.limitPointInclusions_ground)
  have hA : A ∈ M.sets := M.union_mem unions (M.union_mem unions run.limitActorInclusions_ground)
  have hPair := M.prod_mem pairing unions powers separation hP hA
  have hF : F ∈ M.sets := M.pairedGraph_mem pairing unions powers separation
    run.indices_ground hP hA run.limitPointInclusions_ground run.limitActorInclusions_ground
  have hSingleton : ({run.indices} : ZFSet.{u}) ∈ M.sets := by
    rw [← ZFSet.pair_eq_singleton]
    exact M.unorderedPair_mem pairing run.indices_ground run.indices_ground
  have hT : T ∈ M.sets := M.prod_mem pairing unions powers separation hSingleton run.indices_ground
  have funcF : ZFSet.IsFunc run.indices (ZFSet.prod P A) F :=
    pairedGraph_function_of_subset run.limitPointInclusions_function.to_isFunc
      run.limitActorInclusions_function.to_isFunc (fun _ h => h)
  have func : ZFSet.IsFunc T (ZFSet.prod P A) row :=
    relationCompose_function_of_subset (productSecond_function {run.indices} run.indices)
      funcF (fun _ h => h)
  refine ⟨row, M.relationCompose_mem pairing unions powers separation hT run.indices_ground hPair
    (M.productSecond_mem pairing unions powers separation hSingleton run.indices_ground) hF,
    ⟨_, func⟩, ?_, ?_⟩
  · intro i z
    have hi : run.key i ∈ run.indices := ZFSet.mem_range.2 ⟨i, rfl⟩
    have point := (run.limitPointInclusions_entry i _).2 rfl
    have actor := (run.limitActorInclusions_entry i _).2 rfl
    have value : ZFSet.pair (run.key i)
        (ZFSet.pair (run.limitPointMap i) (run.limitActorMap i)) ∈ F :=
      (pair_mem_pairedGraph _ _ _ _ _ _ _ _).2
        ⟨hi, pair_second_mem_doubleUnion point, pair_second_mem_doubleUnion actor, point, actor⟩
    have actual : ZFSet.pair (ZFSet.pair run.indices (run.key i))
        (ZFSet.pair (run.limitPointMap i) (run.limitActorMap i)) ∈ row :=
      (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hi⟩,
          (ZFSet.pair_mem_prod.1 (funcF.1 value)).2, run.key i, hi,
          (mem_productSecond _ _ _).2 ⟨run.indices, ZFSet.mem_singleton.2 rfl, run.key i, hi, rfl⟩,
          value⟩
    exact ⟨fun entry => (FunctionGraphOn.unique ⟨_, func⟩ entry actual), fun equal => equal.symm ▸ actual⟩
  · have indexRank := run.indices_rank_le_code.trans_lt rank
    have pointRank : ZFSet.rank P < o :=
      ((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _)).trans_lt
        (run.limitPointInclusions_rank_lt limit rank)
    have actorRank : ZFSet.rank A < o :=
      ((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _)).trans_lt
        (run.limitActorInclusions_rank_lt limit rank)
    exact (ZFSet.rank_mono func.1).trans_lt
      (rank_product_lt limit (rank_product_lt limit (rank_singleton_lt limit indexRank) indexRank)
        (rank_product_lt limit pointRank actorRank))

end

open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def limitOrder : ZFSet.{u} :=
  indexedRelationLift run.indices run.carrierUnion run.limitPoints
    (run.stageFieldFamily 1) run.limitPointInclusions

noncomputable def limitMeetGraph : ZFSet.{u} :=
  indexedBinaryLift run.indices run.carrierUnion run.limitPoints
    (run.stageFieldFamily 2) run.limitPointInclusions

theorem limitOrder_ground : run.limitOrder ∈ M.sets :=
  M.indexedRelationLift_mem pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.limitPoints_ground (run.stageFieldFamily_ground 1)
    run.limitPointInclusions_ground

theorem limitMeetGraph_ground : run.limitMeetGraph ∈ M.sets :=
  M.indexedBinaryLift_mem pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.limitPoints_ground (run.stageFieldFamily_ground 2)
    run.limitPointInclusions_ground

theorem limitOrder_entry (p q : ZFSet.{u}) :
    ZFSet.pair p q ∈ run.limitOrder ↔ run.LimitLE p q := by
  rw [limitOrder, pair_mem_indexedRelationLift]
  constructor
  · rintro ⟨_, _, k, hk, r, e, x, _, y, _, relation, inclusion, first, second, lower⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hk
    have er : r = (run.diagram.stage i).stage.order := (run.stageFieldFamily_entry 1 i r).1 relation
    have ee := (run.limitPointInclusions_entry i e).1 inclusion
    subst r
    subst e
    obtain ⟨hx, ep⟩ := (run.pointPresentation.inclusion_entry i x p).1 first
    obtain ⟨hy, eq⟩ := (run.pointPresentation.inclusion_entry i y q).1 second
    exact ⟨i, x, y, hx, hy, ep, eq, lower⟩
  · rintro ⟨i, x, y, hx, hy, rfl, rfl, lower⟩
    exact ⟨run.pointPresentation.limitPoint_mem hx, run.pointPresentation.limitPoint_mem hy,
      run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩, (run.diagram.stage i).stage.order,
      run.limitPointMap i, x, run.pointPresentation.carrier_bound i hx,
      y, run.pointPresentation.carrier_bound i hy,
      (run.stageFieldFamily_entry 1 i _).2 rfl, (run.limitPointInclusions_entry i _).2 rfl,
      (run.pointPresentation.inclusion_entry i x _).2 ⟨hx, rfl⟩,
      (run.pointPresentation.inclusion_entry i y _).2 ⟨hy, rfl⟩, lower⟩

theorem limitMeetGraph_entry (p q v : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair p q) v ∈ run.limitMeetGraph ↔ run.LimitMeet p q v := by
  rw [limitMeetGraph, triple_mem_indexedBinaryLift]
  constructor
  · rintro ⟨_, _, _, k, hk, b, e, x, _, y, _, z, _, operation, inclusion, first, second, third, meet⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hk
    have eb : b = (run.diagram.stage i).stage.meetGraph := (run.stageFieldFamily_entry 2 i b).1 operation
    have ee := (run.limitPointInclusions_entry i e).1 inclusion
    subst b
    subst e
    obtain ⟨hx, ep⟩ := (run.pointPresentation.inclusion_entry i x p).1 first
    obtain ⟨hy, eq⟩ := (run.pointPresentation.inclusion_entry i y q).1 second
    obtain ⟨hz, ev⟩ := (run.pointPresentation.inclusion_entry i z v).1 third
    exact ⟨i, x, y, z, hx, hy, hz, ep, eq, ev, meet⟩
  · rintro ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl, meet⟩
    exact ⟨run.pointPresentation.limitPoint_mem hx, run.pointPresentation.limitPoint_mem hy,
      run.pointPresentation.limitPoint_mem hz, run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩,
      (run.diagram.stage i).stage.meetGraph, run.limitPointMap i,
      x, run.pointPresentation.carrier_bound i hx, y, run.pointPresentation.carrier_bound i hy,
      z, run.pointPresentation.carrier_bound i hz,
      (run.stageFieldFamily_entry 2 i _).2 rfl, (run.limitPointInclusions_entry i _).2 rfl,
      (run.pointPresentation.inclusion_entry i x _).2 ⟨hx, rfl⟩,
      (run.pointPresentation.inclusion_entry i y _).2 ⟨hy, rfl⟩,
      (run.pointPresentation.inclusion_entry i z _).2 ⟨hz, rfl⟩, meet⟩

theorem limitOrder_code : PartialOrderCode run.limitPoints run.limitOrder where
  relation := indexedRelationLift_subset _ _ _ _ _
  refl x hx := (run.limitOrder_entry x x).2 (run.limitLE_refl hx)
  antisymm x _ y _ first second := run.limitLE_antisymm
    ((run.limitOrder_entry x y).1 first) ((run.limitOrder_entry y x).1 second)
  trans x _ y _ z _ first second := (run.limitOrder_entry x z).2
    (run.limitLE_trans ((run.limitOrder_entry x y).1 first) ((run.limitOrder_entry y z).1 second))

theorem limitMeet_code : MeetOrderCode run.limitPoints run.limitOrder run.limitMeetGraph where
  order := run.limitOrder_code
  operation := by
    refine ⟨indexedBinaryLift_subset _ _ _ _ _, ?_⟩
    intro w hw
    obtain ⟨p, hp, q, hq, rfl⟩ := ZFSet.mem_prod.1 hw
    obtain ⟨v, _, meet⟩ := run.limitMeet_total hp hq
    refine ⟨v, (run.limitMeetGraph_entry p q v).2 meet, ?_⟩
    intro v' entry
    exact run.limitMeet_unique ((run.limitMeetGraph_entry p q v').1 entry) meet
  lower_left p q v entry := (run.limitOrder_entry v p).2
    (run.limitMeet_lower_left ((run.limitMeetGraph_entry p q v).1 entry))
  lower_right p q v entry := (run.limitOrder_entry v q).2
    (run.limitMeet_lower_right ((run.limitMeetGraph_entry p q v).1 entry))
  greatest p q v w _ entry first second := (run.limitOrder_entry w v).2
    (run.limitMeet_greatest ((run.limitMeetGraph_entry p q v).1 entry)
      ((run.limitOrder_entry w p).1 first) ((run.limitOrder_entry w q).1 second))

theorem limitPointMap_order_iff (i : I) (x y p q : ZFSet.{u})
    (first : ZFSet.pair x p ∈ run.limitPointMap i)
    (second : ZFSet.pair y q ∈ run.limitPointMap i) :
    ZFSet.pair p q ∈ run.limitOrder ↔ ZFSet.pair x y ∈ (run.diagram.stage i).stage.order := by
  obtain ⟨hx, rfl⟩ := (run.pointPresentation.inclusion_entry i x p).1 first
  obtain ⟨hy, rfl⟩ := (run.pointPresentation.inclusion_entry i y q).1 second
  exact (run.limitOrder_entry _ _).trans (run.limitLE_at i hx hy)

theorem limitPointMap_meetEmbedding (i : I) :
    MeetEmbeddingCode (run.diagram.stage i).stage.carrier run.limitPoints
      (run.diagram.stage i).stage.order run.limitOrder
      (run.diagram.stage i).stage.meetGraph run.limitMeetGraph (run.limitPointMap i) where
  injection := run.limitPointMap_injection i
  monotone x y p q lower first second := (run.limitPointMap_order_iff i x y p q first second).2 lower
  map_meet x y z p q v meet first second third := by
    obtain ⟨hx, rfl⟩ := (run.pointPresentation.inclusion_entry i x p).1 first
    obtain ⟨hy, rfl⟩ := (run.pointPresentation.inclusion_entry i y q).1 second
    obtain ⟨hz, rfl⟩ := (run.pointPresentation.inclusion_entry i z v).1 third
    exact (run.limitMeetGraph_entry _ _ _).2 ((run.limitMeet_at i hx hy hz).2 meet)

theorem limitOrder_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitOrder < o :=
  indexedRelationLift_rank_lt limit _ _ _ _ (run.limitPoints_rank_lt limit rank)

theorem limitMeetGraph_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitMeetGraph < o :=
  indexedBinaryLift_rank_lt limit _ _ _ _ (run.limitPoints_rank_lt limit rank)

noncomputable def limitBottom (i : I) : ZFSet.{u} :=
  run.pointPresentation.limitPoint i (run.diagram.stage i).stage.bottom

theorem limitBottom_mem (i : I) : run.limitBottom i ∈ run.limitPoints :=
  run.pointPresentation.limitPoint_mem (run.diagram.stage i).stage.bottom_mem

theorem limitBottom_ground (i : I) : run.limitBottom i ∈ M.sets :=
  M.transitive run.limitPoints_ground (run.limitBottom_mem i)

theorem limitBottom_eq (i j : I) : run.limitBottom i = run.limitBottom j := by
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  exact (run.pointPresentation.limitPoint_transition ik (run.diagram.transition ik).map.bottom).trans
    (run.pointPresentation.limitPoint_transition jk (run.diagram.transition jk).map.bottom).symm

theorem limitBottom_least (i : I) (q : ZFSet.{u}) (member : q ∈ run.limitPoints) :
    ZFSet.pair (run.limitBottom i) q ∈ run.limitOrder := by
  obtain ⟨j, x, hx, rfl⟩ := run.pointPresentation.limitPoint_coverage member
  rw [run.limitBottom_eq i j]
  exact (run.limitOrder_entry _ _).2 ((run.limitLE_at j (run.diagram.stage j).stage.bottom_mem hx).2
    ((run.diagram.stage j).stage.least x hx))

theorem limitPointMap_bottom (i₀ i : I) :
    ZFSet.pair (run.diagram.stage i).stage.bottom (run.limitBottom i₀) ∈ run.limitPointMap i :=
  (run.pointPresentation.inclusion_entry i _ _).2
    ⟨(run.diagram.stage i).stage.bottom_mem, run.limitBottom_eq i₀ i⟩

theorem limitBottom_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) (i : I) : ZFSet.rank (run.limitBottom i) < o :=
  (ZFSet.rank_lt_of_mem (run.limitBottom_mem i)).trans (run.limitPoints_rank_lt limit rank)

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
