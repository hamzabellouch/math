import OAI.SetTheory.PartitionPrinciple.Geometry.GroundIndexedMixedOperationLifts
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixLimitBottom

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

def LimitAct (g p q : ZFSet.{u}) : Prop :=
  ∃ i a x y, a ∈ (run.diagram.stage i).stage.actors ∧
    x ∈ (run.diagram.stage i).stage.carrier ∧ y ∈ (run.diagram.stage i).stage.carrier ∧
    g = run.actorPresentation.limitPoint i a ∧ p = run.pointPresentation.limitPoint i x ∧
    q = run.pointPresentation.limitPoint i y ∧ ZFSet.pair (ZFSet.pair a x) y ∈ (run.diagram.stage i).stage.action

theorem limitAct_bounds {g p q : ZFSet.{u}} (act : run.LimitAct g p q) :
    g ∈ run.limitActors ∧ p ∈ run.limitPoints ∧ q ∈ run.limitPoints := by
  obtain ⟨i, a, x, y, ha, hx, hy, rfl, rfl, rfl, _⟩ := act
  exact ⟨run.actorPresentation.limitPoint_mem ha,
    run.pointPresentation.limitPoint_mem hx, run.pointPresentation.limitPoint_mem hy⟩

theorem limitAct_total {g p : ZFSet.{u}} (hg : g ∈ run.limitActors) (hp : p ∈ run.limitPoints) :
    ∃ q ∈ run.limitPoints, run.LimitAct g p q := by
  obtain ⟨i, a, x, ha, hx, rfl, rfl⟩ := run.actorPresentation.mixed_pair_coverage run.pointPresentation hg hp
  obtain ⟨y, entry, _⟩ := (run.diagram.stage i).stage.action_code.function.2
    (ZFSet.pair a x) (ZFSet.pair_mem_prod.2 ⟨ha, hx⟩)
  have hy := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.action_code.function.1 entry)).2
  exact ⟨run.pointPresentation.limitPoint i y, run.pointPresentation.limitPoint_mem hy,
    i, a, x, y, ha, hx, hy, rfl, rfl, rfl, entry⟩

theorem limitAct_unique {g p q r : ZFSet.{u}}
    (first : run.LimitAct g p q) (second : run.LimitAct g p r) : q = r := by
  obtain ⟨i, a, x, y, ha, hx, hy, rfl, rfl, rfl, act⟩ := first
  obtain ⟨j, b, u, v, hb, hu, hv, equalActor, equalPoint, rfl, act'⟩ := second
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  obtain ⟨a', aa⟩ := run.actorSystem.map_entry_total ik ha
  obtain ⟨b', bb⟩ := run.actorSystem.map_entry_total jk hb
  obtain ⟨x', xx⟩ := run.pointSystem.map_entry_total ik hx
  obtain ⟨u', uu⟩ := run.pointSystem.map_entry_total jk hu
  obtain ⟨y', yy⟩ := run.pointSystem.map_entry_total ik hy
  obtain ⟨v', vv⟩ := run.pointSystem.map_entry_total jk hv
  have actorEqual := (run.actorSystem.related_iff_common_images ik jk aa bb).1
    ((run.actorPresentation.limitPoint_eq_iff_related ha hb).1 equalActor)
  have pointEqual := (run.pointSystem.related_iff_common_images ik jk xx uu).1
    ((run.pointPresentation.limitPoint_eq_iff_related hx hu).1 equalPoint)
  subst b'
  subst u'
  have left := (run.diagram.transition ik).map.equivariant a a' x y x' y' aa xx yy act
  have right := (run.diagram.transition jk).map.equivariant b a' u v x' v' bb uu vv act'
  have function : FunctionGraphOn
      (ZFSet.prod (run.diagram.stage k).stage.actors (run.diagram.stage k).stage.carrier)
      (run.diagram.stage k).stage.action := ⟨_, (run.diagram.stage k).stage.action_code.function⟩
  have equal := function.unique left right
  exact (run.pointPresentation.limitPoint_transition ik yy).trans
    ((congrArg (run.pointPresentation.limitPoint k) equal).trans
      (run.pointPresentation.limitPoint_transition jk vv).symm)

theorem limitAct_at (i : I) {a x y : ZFSet.{u}}
    (ha : a ∈ (run.diagram.stage i).stage.actors)
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage i).stage.carrier) :
    run.LimitAct (run.actorPresentation.limitPoint i a)
      (run.pointPresentation.limitPoint i x) (run.pointPresentation.limitPoint i y) ↔
      ZFSet.pair (ZFSet.pair a x) y ∈ (run.diagram.stage i).stage.action := by
  constructor
  · intro act
    obtain ⟨z, entry, _⟩ := (run.diagram.stage i).stage.action_code.function.2
      (ZFSet.pair a x) (ZFSet.pair_mem_prod.2 ⟨ha, hx⟩)
    have hz := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.action_code.function.1 entry)).2
    have equal := (run.pointPresentation.limitPoint_same_iff hy hz).1
      (run.limitAct_unique act ⟨i, a, x, z, ha, hx, hz, rfl, rfl, rfl, entry⟩)
    subst z
    exact entry
  · intro entry
    exact ⟨i, a, x, y, ha, hx, hy, rfl, rfl, rfl, entry⟩

theorem limitAct_monotone {g p q r s : ZFSet.{u}}
    (first : run.LimitAct g p r) (second : run.LimitAct g q s) (lower : run.LimitLE p q) :
    run.LimitLE r s := by
  obtain ⟨i, a, x, y, ha, hx, hy, rfl, rfl, rfl⟩ :=
    run.actorPresentation.mixed_triple_coverage run.pointPresentation run.pointPresentation
      (run.limitAct_bounds first).1 (run.limitAct_bounds first).2.1 (run.limitAct_bounds second).2.1
  obtain ⟨z, left, _⟩ := (run.diagram.stage i).stage.action_code.function.2
    (ZFSet.pair a x) (ZFSet.pair_mem_prod.2 ⟨ha, hx⟩)
  obtain ⟨w, right, _⟩ := (run.diagram.stage i).stage.action_code.function.2
    (ZFSet.pair a y) (ZFSet.pair_mem_prod.2 ⟨ha, hy⟩)
  have hz := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.action_code.function.1 left)).2
  have hw := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.action_code.function.1 right)).2
  have er := run.limitAct_unique first ((run.limitAct_at i ha hx hz).2 left)
  have es := run.limitAct_unique second ((run.limitAct_at i ha hy hw).2 right)
  rw [er, es]
  exact (run.limitLE_at i hz hw).2 ((run.diagram.stage i).stage.action_code.monotone
    a ha x hx y hy z hz w hw left right ((run.limitLE_at i hx hy).1 lower))

noncomputable def limitAction : ZFSet.{u} :=
  indexedMixedBinaryLift run.indices run.actorUnion run.carrierUnion run.limitActors run.limitPoints
    (run.stageFieldFamily 7) run.limitActorInclusions run.limitPointInclusions

theorem limitAction_ground : run.limitAction ∈ M.sets :=
  M.indexedMixedBinaryLift_mem pairing unions powers separation run.indices_ground
    run.actorUnion_ground run.carrierUnion_ground run.limitActors_ground run.limitPoints_ground
    (run.stageFieldFamily_ground 7) run.limitActorInclusions_ground run.limitPointInclusions_ground

theorem limitAction_entry (g p q : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g p) q ∈ run.limitAction ↔ run.LimitAct g p q := by
  rw [limitAction, triple_mem_indexedMixedBinaryLift]
  constructor
  · rintro ⟨_, _, _, k, hk, a, eG, eP, u, _, x, _, y, _,
      action, actors, points, actor, first, second, source⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hk
    have ea : a = (run.diagram.stage i).stage.action := (run.stageFieldFamily_entry 7 i a).1 action
    have eg := (run.limitActorInclusions_entry i eG).1 actors
    have ep := (run.limitPointInclusions_entry i eP).1 points
    subst a
    subst eG
    subst eP
    obtain ⟨hu, equalG⟩ := (run.actorPresentation.inclusion_entry i u g).1 actor
    obtain ⟨hx, equalP⟩ := (run.pointPresentation.inclusion_entry i x p).1 first
    obtain ⟨hy, equalQ⟩ := (run.pointPresentation.inclusion_entry i y q).1 second
    exact ⟨i, u, x, y, hu, hx, hy, equalG, equalP, equalQ, source⟩
  · rintro ⟨i, u, x, y, hu, hx, hy, rfl, rfl, rfl, source⟩
    exact ⟨run.actorPresentation.limitPoint_mem hu, run.pointPresentation.limitPoint_mem hx,
      run.pointPresentation.limitPoint_mem hy, run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩,
      (run.diagram.stage i).stage.action, run.limitActorMap i, run.limitPointMap i,
      u, run.actorPresentation.carrier_bound i hu, x, run.pointPresentation.carrier_bound i hx,
      y, run.pointPresentation.carrier_bound i hy,
      (run.stageFieldFamily_entry 7 i _).2 rfl, (run.limitActorInclusions_entry i _).2 rfl,
      (run.limitPointInclusions_entry i _).2 rfl,
      (run.actorPresentation.inclusion_entry i u _).2 ⟨hu, rfl⟩,
      (run.pointPresentation.inclusion_entry i x _).2 ⟨hx, rfl⟩,
      (run.pointPresentation.inclusion_entry i y _).2 ⟨hy, rfl⟩, source⟩

theorem limitAction_function :
    ZFSet.IsFunc (ZFSet.prod run.limitActors run.limitPoints) run.limitPoints run.limitAction := by
  refine ⟨indexedMixedBinaryLift_subset _ _ _ _ _ _ _ _, ?_⟩
  intro w hw
  obtain ⟨g, hg, p, hp, rfl⟩ := ZFSet.mem_prod.1 hw
  obtain ⟨q, _, action⟩ := run.limitAct_total hg hp
  refine ⟨q, (run.limitAction_entry g p q).2 action, ?_⟩
  intro q' entry
  exact run.limitAct_unique ((run.limitAction_entry g p q').1 entry) action

theorem limitAction_at (i : I) {a x y : ZFSet.{u}}
    (ha : a ∈ (run.diagram.stage i).stage.actors)
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage i).stage.carrier) :
    ZFSet.pair (ZFSet.pair (run.actorPresentation.limitPoint i a)
      (run.pointPresentation.limitPoint i x)) (run.pointPresentation.limitPoint i y) ∈ run.limitAction ↔
      ZFSet.pair (ZFSet.pair a x) y ∈ (run.diagram.stage i).stage.action :=
  (run.limitAction_entry _ _ _).trans (run.limitAct_at i ha hx hy)

theorem limitMaps_action_iff (i : I) (a g x y p q : ZFSet.{u})
    (actor : ZFSet.pair a g ∈ run.limitActorMap i)
    (first : ZFSet.pair x p ∈ run.limitPointMap i)
    (second : ZFSet.pair y q ∈ run.limitPointMap i) :
    ZFSet.pair (ZFSet.pair g p) q ∈ run.limitAction ↔
      ZFSet.pair (ZFSet.pair a x) y ∈ (run.diagram.stage i).stage.action := by
  obtain ⟨ha, rfl⟩ := (run.actorPresentation.inclusion_entry i a g).1 actor
  obtain ⟨hx, rfl⟩ := (run.pointPresentation.inclusion_entry i x p).1 first
  obtain ⟨hy, rfl⟩ := (run.pointPresentation.inclusion_entry i y q).1 second
  exact run.limitAction_at i ha hx hy

theorem limitMaps_equivariant (i : I) (a g x y p q : ZFSet.{u})
    (actor : ZFSet.pair a g ∈ run.limitActorMap i)
    (first : ZFSet.pair x p ∈ run.limitPointMap i)
    (second : ZFSet.pair y q ∈ run.limitPointMap i)
    (action : ZFSet.pair (ZFSet.pair a x) y ∈ (run.diagram.stage i).stage.action) :
    ZFSet.pair (ZFSet.pair g p) q ∈ run.limitAction :=
  (run.limitMaps_action_iff i a g x y p q actor first second).2 action

theorem limitAction_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitAction < o :=
  indexedMixedBinaryLift_rank_lt limit _ _ _ _ _ _
    (run.limitActors_rank_lt limit rank) (run.limitPoints_rank_lt limit rank)

theorem limitMaps_agreement (i : I) (g h g' h' v v' : ZFSet.{u})
    (first : ZFSet.pair g g' ∈ run.limitActorMap i)
    (second : ZFSet.pair h h' ∈ run.limitActorMap i)
    (point : ZFSet.pair v v' ∈ run.limitPointMap i)
    (agree : ActionAgreementBelow (run.diagram.stage i).stage.carrier
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.action g h v) :
    ActionAgreementBelow run.limitPoints run.limitOrder run.limitAction g' h' v' := by
  obtain ⟨hg, rfl⟩ := (run.actorPresentation.inclusion_entry i g g').1 first
  obtain ⟨hh, rfl⟩ := (run.actorPresentation.inclusion_entry i h h').1 second
  obtain ⟨hv, rfl⟩ := (run.pointPresentation.inclusion_entry i v v').1 point
  intro x hx y hy lower
  obtain ⟨j, a, b, ha, hb, rfl, rfl⟩ := run.pointPresentation.pair_coverage hx hy
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  obtain ⟨G, gG⟩ := run.actorSystem.map_entry_total ik hg
  obtain ⟨H, hH⟩ := run.actorSystem.map_entry_total ik hh
  obtain ⟨V, vV⟩ := run.pointSystem.map_entry_total ik hv
  obtain ⟨A, aA⟩ := run.pointSystem.map_entry_total jk ha
  obtain ⟨B, bB⟩ := run.pointSystem.map_entry_total jk hb
  have hG := (run.actorSystem.map_entry_bounds ik gG).2
  have Hmem := (run.actorSystem.map_entry_bounds ik hH).2
  have hV := (run.pointSystem.map_entry_bounds ik vV).2
  have hA := (run.pointSystem.map_entry_bounds jk aA).2
  have hB := (run.pointSystem.map_entry_bounds jk bB).2
  have equalA := run.pointPresentation.limitPoint_transition jk aA
  have equalV := run.pointPresentation.limitPoint_transition ik vV
  rw [equalA, equalV] at lower
  have sourceLower := (run.limitLE_at k hA hV).1 ((run.limitOrder_entry _ _).1 lower)
  have later := (run.diagram.transition ik).map.agreement g h G H v V gG hH vV agree
  rw [run.actorPresentation.limitPoint_transition ik gG,
    run.actorPresentation.limitPoint_transition ik hH,
    equalA, run.pointPresentation.limitPoint_transition jk bB]
  exact (run.limitAction_at k hG hA hB).trans
    ((later A hA B hB sourceLower).trans (run.limitAction_at k Hmem hA hB).symm)

theorem limitAct_mul {g h k p q r : ZFSet.{u}}
    (product : run.LimitMul g h k) (first : run.LimitAct h p q) (second : run.LimitAct g q r) :
    run.LimitAct k p r := by
  obtain ⟨i, a, b, x, ha, hb, hx, rfl, rfl, rfl⟩ :=
    run.actorPresentation.mixed_triple_coverage run.actorPresentation run.pointPresentation
      (run.limitMul_bounds product).1 (run.limitMul_bounds product).2.1 (run.limitAct_bounds first).2.1
  obtain ⟨c, mul, _⟩ := (run.diagram.stage i).stage.group_code.mul_function.2
    (ZFSet.pair a b) (ZFSet.pair_mem_prod.2 ⟨ha, hb⟩)
  have hc := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.mul_function.1 mul)).2
  obtain ⟨y, left, _⟩ := (run.diagram.stage i).stage.action_code.function.2
    (ZFSet.pair b x) (ZFSet.pair_mem_prod.2 ⟨hb, hx⟩)
  have hy := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.action_code.function.1 left)).2
  obtain ⟨z, right, _⟩ := (run.diagram.stage i).stage.action_code.function.2
    (ZFSet.pair a y) (ZFSet.pair_mem_prod.2 ⟨ha, hy⟩)
  have hz := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.action_code.function.1 right)).2
  have ek := run.limitMul_unique product ((run.limitMul_at i ha hb hc).2 mul)
  have eq := run.limitAct_unique first ((run.limitAct_at i hb hx hy).2 left)
  rw [eq] at second
  have er := run.limitAct_unique second ((run.limitAct_at i ha hy hz).2 right)
  rw [ek, er]
  exact (run.limitAct_at i hc hx hz).2
    ((run.diagram.stage i).stage.action_code.mul a ha b hb c hc x hx y hy z hz mul left right)

theorem limitAction_one (i₀ : I) (p : ZFSet.{u}) (hp : p ∈ run.limitPoints) :
    ZFSet.pair (ZFSet.pair (run.limitIdentity i₀) p) p ∈ run.limitAction := by
  obtain ⟨i, x, hx, rfl⟩ := run.pointPresentation.limitPoint_coverage hp
  rw [run.limitIdentity_eq i₀ i]
  exact (run.limitAction_at i (run.diagram.stage i).stage.group_code.identity_mem hx hx).2
    ((run.diagram.stage i).stage.action_code.one x hx)

theorem limitAction_code (i₀ : I) :
    PosetActionCode run.limitActors run.limitPoints run.limitMultiplication
      (run.limitIdentity i₀) run.limitOrder run.limitAction where
  function := run.limitAction_function
  one := run.limitAction_one i₀
  mul g _ h _ k _ p _ q _ r _ product first second :=
    (run.limitAction_entry k p r).2 (run.limitAct_mul
      ((run.limitMultiplication_entry g h k).1 product)
      ((run.limitAction_entry h p q).1 first) ((run.limitAction_entry g q r).1 second))
  monotone g _ p _ q _ r _ s _ first second lower :=
    (run.limitOrder_entry r s).2 (run.limitAct_monotone
      ((run.limitAction_entry g p r).1 first) ((run.limitAction_entry g q s).1 second)
      ((run.limitOrder_entry p q).1 lower))

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
