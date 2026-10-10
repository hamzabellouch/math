import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainPrefixLimitActionLaws
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainPrefixPriorLayerWitnesses
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialPreservedMainPrefix
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixLimitSizes
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixTopColumns

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitIdentity_ground (i : I) : run.limitIdentity i ∈ M.sets :=
  M.transitive run.limitActors_ground (run.limitIdentity_mem i)

theorem limitIdentity_rank_lt (i : I) {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank (run.limitIdentity i) < o :=
  (ZFSet.rank_lt_of_mem (run.limitIdentity_mem i)).trans (run.limitActors_rank_lt limit rank)

theorem limitGroup_code (i₀ : I) :
    GroupCode run.limitActors run.limitMultiplication run.limitInverse (run.limitIdentity i₀) where
  mul_function := run.limitMultiplication_function
  inv_function := run.limitInverse_function
  identity_mem := run.limitIdentity_mem i₀
  one_mul g hg := by
    obtain ⟨i, a, ha, rfl⟩ := run.actorPresentation.limitPoint_coverage hg
    rw [run.limitIdentity_eq i₀ i]
    exact (run.limitMultiplication_at i (run.diagram.stage i).stage.group_code.identity_mem ha ha).2
      ((run.diagram.stage i).stage.group_code.one_mul a ha)
  mul_one g hg := by
    obtain ⟨i, a, ha, rfl⟩ := run.actorPresentation.limitPoint_coverage hg
    rw [run.limitIdentity_eq i₀ i]
    exact (run.limitMultiplication_at i ha (run.diagram.stage i).stage.group_code.identity_mem ha).2
      ((run.diagram.stage i).stage.group_code.mul_one a ha)
  inv_mul g hg h hh inverse := by
    obtain ⟨i, a, b, ha, hb, rfl, rfl⟩ := run.actorPresentation.pair_coverage hg hh
    rw [run.limitIdentity_eq i₀ i]
    exact (run.limitMultiplication_at i hb ha (run.diagram.stage i).stage.group_code.identity_mem).2
      ((run.diagram.stage i).stage.group_code.inv_mul a ha b hb ((run.limitInverse_at i ha hb).1 inverse))
  mul_assoc g hg h hh k hk a _ b _ c _ first second third := by
    obtain ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl⟩ := run.actorPresentation.triple_coverage hg hh hk
    obtain ⟨u, xy, _⟩ := (run.diagram.stage i).stage.group_code.mul_function.2
      (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    obtain ⟨v, yz, _⟩ := (run.diagram.stage i).stage.group_code.mul_function.2
      (ZFSet.pair y z) (ZFSet.pair_mem_prod.2 ⟨hy, hz⟩)
    have hu := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.mul_function.1 xy)).2
    have hv := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.mul_function.1 yz)).2
    obtain ⟨w, uz, _⟩ := (run.diagram.stage i).stage.group_code.mul_function.2
      (ZFSet.pair u z) (ZFSet.pair_mem_prod.2 ⟨hu, hz⟩)
    have hw := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.mul_function.1 uz)).2
    have function : FunctionGraphOn (ZFSet.prod run.limitActors run.limitActors) run.limitMultiplication :=
      ⟨_, run.limitMultiplication_function⟩
    have equalA : a = run.actorPresentation.limitPoint i u :=
      function.unique first ((run.limitMultiplication_at i hx hy hu).2 xy)
    have equalB : b = run.actorPresentation.limitPoint i v :=
      function.unique second ((run.limitMultiplication_at i hy hz hv).2 yz)
    subst a
    subst b
    have equalC : c = run.actorPresentation.limitPoint i w :=
      function.unique third ((run.limitMultiplication_at i hu hz hw).2 uz)
    subst c
    exact (run.limitMultiplication_at i hx hv hw).2
      ((run.diagram.stage i).stage.group_code.mul_assoc x hx y hy z hz u hu v hv w hw xy yz uz)

theorem limitActorMap_multiplication_iff (i : I) (a b c g h k : ZFSet.{u})
    (first : ZFSet.pair a g ∈ run.limitActorMap i)
    (second : ZFSet.pair b h ∈ run.limitActorMap i)
    (third : ZFSet.pair c k ∈ run.limitActorMap i) :
    ZFSet.pair (ZFSet.pair g h) k ∈ run.limitMultiplication ↔
      ZFSet.pair (ZFSet.pair a b) c ∈ (run.diagram.stage i).stage.multiplication := by
  obtain ⟨ha, rfl⟩ := (run.actorPresentation.inclusion_entry i a g).1 first
  obtain ⟨hb, rfl⟩ := (run.actorPresentation.inclusion_entry i b h).1 second
  obtain ⟨hc, rfl⟩ := (run.actorPresentation.inclusion_entry i c k).1 third
  exact run.limitMultiplication_at i ha hb hc

theorem limitActorMap_groupEmbedding (i₀ i : I) :
    GroupEmbeddingCode (run.diagram.stage i).stage.actors run.limitActors
      (run.diagram.stage i).stage.multiplication run.limitMultiplication
      (run.diagram.stage i).stage.identity (run.limitIdentity i₀) (run.limitActorMap i) where
  injection := run.limitActorMap_injection i
  one := (run.actorPresentation.inclusion_entry i _ _).2
    ⟨(run.diagram.stage i).stage.group_code.identity_mem, run.limitIdentity_eq i₀ i⟩
  mul a b c g h k product first second third :=
    (run.limitActorMap_multiplication_iff i a b c g h k first second third).2 product

theorem limitActorMap_inverse_iff (i : I) (a b g h : ZFSet.{u})
    (first : ZFSet.pair a g ∈ run.limitActorMap i)
    (second : ZFSet.pair b h ∈ run.limitActorMap i) :
    ZFSet.pair g h ∈ run.limitInverse ↔ ZFSet.pair a b ∈ (run.diagram.stage i).stage.inverse := by
  obtain ⟨ha, rfl⟩ := (run.actorPresentation.inclusion_entry i a g).1 first
  obtain ⟨hb, rfl⟩ := (run.actorPresentation.inclusion_entry i b h).1 second
  exact run.limitInverse_at i ha hb

structure FixedTopStage (i₀ : I) where
  column : ZFSet.{u}
  coordinate : ZFSet.{u}
  column_mem : column ∈ C
  coordinate_mem : coordinate ∈ D
  stage : GroundMainStage M C D rD
  carrier_eq : stage.carrier = fixedTopCarrier run.limitPoints
  order_eq : stage.order = fixedTopOrder run.limitPoints run.limitOrder
  meet_eq : stage.meetGraph = fixedTopMeet run.limitPoints run.limitOrder
  actors_eq : stage.actors = run.limitActors
  multiplication_eq : stage.multiplication = run.limitMultiplication
  inverse_eq : stage.inverse = run.limitInverse
  identity_eq : stage.identity = run.limitIdentity i₀
  action_eq : stage.action = fixedTopAction run.limitActors run.limitPoints run.limitAction
  bottom_eq : stage.bottom = run.limitBottom i₀
  top_eq : stage.top = run.limitPoints
  height_eq : stage.height = fixedTopHeightGraph run.limitPoints run.limitHeight column coordinate
  column_above : ∀ c ∈ heightColumns run.limitPoints C D run.limitHeight, c ∈ column

theorem exists_fixedTopMainStage (i₀ : I)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (indices : M.groundEmbeddable run.indices ZFSet.omega) :
    Nonempty (run.FixedTopStage i₀) := by
  subst C
  have nonempty : D.Nonempty := by
    obtain ⟨value, entry, _⟩ := (run.diagram.stage i₀).stage.height_code.function.2
      (run.diagram.stage i₀).stage.bottom (run.diagram.stage i₀).stage.bottom_mem
    have member := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i₀).stage.height_code.function.1 entry)).2
    obtain ⟨_, _, q, hq, _⟩ := ZFSet.mem_prod.1 member
    exact ⟨q, hq⟩
  obtain ⟨b, hb, q, hq, hL, hR, hMu, _, hAction, hHeight, meet, _, action, height,
      _, _, _, _, _, _, _, above, _, _, hRange, smallRange, _, _⟩ :=
    M.exists_fixedTopExtension pairing unions powers separation collection infinite choice
      run.limitPoints_ground run.limitOrder_ground run.limitActors_ground run.limitAction_ground
      (run.diagram.stage i₀).stage.coordinates_ground run.limitHeight_ground
      run.limitMeet_code (run.limitAction_code i₀) (run.limitIdentity_mem i₀) nonempty
      run.limitHeight_code (run.limitHeight_relationImage_countable infinite choice indices)
  let stage : GroundMainStage M (M.groundOmegaOne pairing unions powers separation collection infinite) D rD := {
    carrier := fixedTopCarrier run.limitPoints
    order := fixedTopOrder run.limitPoints run.limitOrder
    meetGraph := fixedTopMeet run.limitPoints run.limitOrder
    actors := run.limitActors
    multiplication := run.limitMultiplication
    inverse := run.limitInverse
    identity := run.limitIdentity i₀
    action := fixedTopAction run.limitActors run.limitPoints run.limitAction
    bottom := run.limitBottom i₀
    top := run.limitPoints
    height := fixedTopHeightGraph run.limitPoints run.limitHeight b q
    carrier_ground := hL
    order_ground := hR
    meet_ground := hMu
    actors_ground := run.limitActors_ground
    multiplication_ground := run.limitMultiplication_ground
    inverse_ground := run.limitInverse_ground
    action_ground := hAction
    height_ground := hHeight
    columns_ground := (run.diagram.stage i₀).stage.columns_ground
    coordinates_ground := (run.diagram.stage i₀).stage.coordinates_ground
    coordinate_order_ground := (run.diagram.stage i₀).stage.coordinate_order_ground
    meet := meet
    group_code := run.limitGroup_code i₀
    action_code := action
    bottom_mem := fixedTopCarrier_old (run.limitBottom_mem i₀)
    least := fixedTopOrder_bottom (run.limitBottom_mem i₀) (run.limitBottom_least i₀)
    top_mem := fixedTopCarrier_top run.limitPoints
    greatest := fun _ hx => fixedTopOrder_greatest hx
    height_code := height
    height_range_ground := hRange
    height_range_countable := smallRange }
  exact ⟨{
    column := b
    coordinate := q
    column_mem := hb
    coordinate_mem := hq
    stage := stage
    carrier_eq := rfl
    order_eq := rfl
    meet_eq := rfl
    actors_eq := rfl
    multiplication_eq := rfl
    inverse_eq := rfl
    identity_eq := rfl
    action_eq := rfl
    bottom_eq := rfl
    top_eq := rfl
    height_eq := rfl
    column_above := above }⟩

end GroundMainPrefix

namespace GroundMainPrefix.FixedTopStage
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} (data : run.FixedTopStage i₀)

theorem carrier_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank data.stage.carrier < o := by
  rw [data.carrier_eq]
  exact rank_fixedTopCarrier_lt limit (run.limitPoints_rank_lt limit rank)

theorem actors_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank data.stage.actors < o := by
  rw [data.actors_eq]
  exact run.limitActors_rank_lt limit rank

theorem carrier_below (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) : GroundBelow M data.stage.carrier K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  rw [data.carrier_eq, fixedTopCarrier]
  exact GroundBelow.insert pairing unions powers separation infinite choice
    run.limitPoints_ground run.limitPoints_ground hK conditions.2.1 conditions.1
    conditions.2.2.1 conditions.2.2.2 (run.limitPoints_below choice hK standard indices)

theorem actors_below (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) : GroundBelow M data.stage.actors K := by
  rw [data.actors_eq]
  exact run.limitActors_below choice hK standard indices

theorem height_rank_lt (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (rank : ZFSet.rank run.code < ZFSet.rank K) : ZFSet.rank data.stage.height < ZFSet.rank K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  exact rank_functionGraph_lt limit data.stage.height_code.function (data.carrier_rank_lt limit rank)
    (rank_product_lt limit (run.linked i₀).invariant.columns_rank (run.linked i₀).invariant.coordinates_rank)

theorem code_rank_lt (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (rank : ZFSet.rank run.code < ZFSet.rank K) : ZFSet.rank data.stage.code < ZFSet.rank K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  exact data.stage.code_rank_lt limit (data.carrier_rank_lt limit rank) (data.actors_rank_lt limit rank)
    (run.linked i₀).invariant.columns_rank (run.linked i₀).invariant.coordinates_rank

theorem invariant_inputs (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) (rank : ZFSet.rank run.code < ZFSet.rank K) :
    GroundBelow M data.stage.carrier K ∧ GroundBelow M data.stage.actors K ∧
      GroundBelow M Labels K ∧ ZFSet.rank data.stage.carrier < ZFSet.rank K ∧
      ZFSet.rank data.stage.actors < ZFSet.rank K ∧ ZFSet.rank Labels < ZFSet.rank K ∧
      run.cutoffLimit ∈ K ∧ ZFSet.rank C < ZFSet.rank K ∧ ZFSet.rank D < ZFSet.rank K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  exact ⟨data.carrier_below infinite choice hK standard indices, data.actors_below choice hK standard indices,
    (run.linked i₀).invariant.labels_small, data.carrier_rank_lt limit rank, data.actors_rank_lt limit rank,
    (run.linked i₀).invariant.labels_rank, run.cutoffLimit_mem_inaccessible hK standard indices,
    (run.linked i₀).invariant.columns_rank, (run.linked i₀).invariant.coordinates_rank⟩

end GroundMainPrefix.FixedTopStage

namespace GroundMainPrefix.FixedTopStage
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} (data : run.FixedTopStage i₀)

noncomputable def transition (i : I) : GroundMainTransition (run.diagram.stage i).stage data.stage where
  points := run.limitPointMap i
  actors := run.limitActorMap i
  points_ground := run.limitPointMap_ground i
  actors_ground := run.limitActorMap_ground i
  point_embedding := by
    rw [data.carrier_eq, data.order_eq, data.meet_eq]
    have original := run.limitPointMap_meetEmbedding i
    refine ⟨original.injection.retarget (fixedTopCarrier_subset run.limitPoints), ?_, ?_⟩
    · intro x y p q lower first second
      exact fixedTopOrder_subset _ _ (original.monotone x y p q lower first second)
    · intro x y z p q v meet first second third
      exact fixedTopMeet_subset run.limitMeet_code (original.map_meet x y z p q v meet first second third)
  order_iff := by
    intro x y p q first second
    have hq := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 second)).2
    rw [data.order_eq, fixedTopOrder_old_iff hq]
    exact run.limitPointMap_order_iff i x y p q first second
  group_embedding := by
    rw [data.actors_eq, data.multiplication_eq, data.identity_eq]
    exact run.limitActorMap_groupEmbedding i₀ i
  equivariant := by
    intro a g x y p q actor first second action
    have hp := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 first)).2
    rw [data.action_eq]
    exact (fixedTopAction_old_iff hp).2 (run.limitMaps_equivariant i a g x y p q actor first second action)
  bottom := by
    rw [data.bottom_eq]
    exact run.limitPointMap_bottom i₀ i
  height := by
    intro x p value entry
    have hp := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).2
    rw [data.height_eq, fixedTopHeightGraph_old_iff hp]
    exact run.limitPointMap_height i entry value
  agreement := by
    intro g h g' h' v v' first second point agree
    have hv := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 point)).2
    rw [data.carrier_eq, data.order_eq, data.action_eq]
    exact (run.limitMaps_agreement i g h g' h' v v' first second point agree).fixedTop
      run.limitOrder_code (run.limitAction_code i₀) hv

theorem transition_points (i : I) : (data.transition i).points = run.limitPointMap i := rfl

theorem transition_actors (i : I) : (data.transition i).actors = run.limitActorMap i := rfl

theorem point_strict_top (i : I) {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ run.limitPointMap i) :
    ZFSet.pair y data.stage.top ∈ data.stage.order ∧
      ZFSet.pair data.stage.top y ∉ data.stage.order := by
  rw [data.top_eq, data.order_eq]
  exact fixedTopOrder_strict_top run.limitOrder_code
    (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).2

end GroundMainPrefix.FixedTopStage

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitChronology_source_entries (i : I) (j : Fin 5) {t : ZFSet.{u}}
    (before : t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff) :
    ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ (run.linked i).serial.fields.graph j ↔
      ZFSet.pair s y ∈ run.limitChronologyFields.graph j := by
  intro s hs y
  have earlier : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff := by
    right
    rcases before with rfl | before
    · exact hs
    · exact (run.diagram.stage i).cutoff_ordinal.1 _ before _ hs
  exact (run.limitChronologyFields_source_entries i j earlier y).symm

theorem limitChronology_raw_witnesses (hOmega : ZFSet.omega ∈ M.sets)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank run.code < o)
    (numbers : ZFSet.rank ZFSet.omega < o) :
    ∀ s ∈ insert run.cutoffLimit run.cutoffLimit,
      ∀ t ∈ insert run.cutoffLimit run.cutoffLimit, t = s ∨ t ∈ s →
      ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode
        (run.limitChronologyFields.graph 0) (run.limitChronologyFields.graph 1)
        (run.limitChronologyFields.graph 2) (run.limitChronologyFields.value 0 s)
        (run.limitChronologyFields.value 1 s) (run.limitChronologyFields.value 2 s)
        (run.limitChronologyFields.value 3 s) t ZFSet.omega z := by
  intro s hs t _ before
  rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
  · rw [run.limitChronologyFields_terminal 0, run.limitChronologyFields_terminal 1,
      run.limitChronologyFields_terminal 2, run.limitChronologyFields_terminal 3]
    change ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode _ _ _
      run.limitPoints run.limitOrder run.limitMeetGraph run.limitBirth t ZFSet.omega z
    rcases before with rfl | before
    · have hEmpty := M.empty_mem ⟨run.cutoffLimit, run.cutoffLimit_ground⟩
      have emptyRank : ZFSet.rank (∅ : ZFSet.{u}) < o := by
        simpa only [ZFSet.rank_empty] using limit.pos
      refine ⟨countableLayerWitness ∅ ∅, M.countableLayerWitness_mem pairing hEmpty hEmpty,
        countableLayerWitness_rank_lt limit emptyRank emptyRank,
        Or.inl ⟨∅, ∅, rfl, ⟨InjectionCode.empty ZFSet.omega, ?_⟩⟩⟩
      intro x _ birth
      exact (ZFSet.mem_irrefl _ (ZFSet.pair_mem_prod.1 (run.limitBirth_function.1 birth)).2).elim
    · obtain ⟨i, old⟩ := (run.cutoffLimit_mem t).1 before
      obtain ⟨z, hz, code, ranked⟩ := run.limitTerminal_raw_witness_rank_lt i old
        (run.limitChronology_source_entries i 0 old) (run.limitChronology_source_entries i 1 old)
        (run.limitChronology_source_entries i 2 old) hOmega limit rank numbers
      exact ⟨z, hz, ranked, code⟩
  · obtain ⟨i, old⟩ := (run.cutoffLimit_mem s).1 hs
    have oldT : t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff := by
      rcases before with rfl | before
      · exact old
      · right
        rcases old with rfl | old
        · exact before
        · exact (run.diagram.stage i).cutoff_ordinal.1 _ old _ before
    obtain ⟨z, hz, code, ranked⟩ := run.prior_raw_witness_rank_lt i old before
      (run.limitChronology_source_entries i 0 oldT) (run.limitChronology_source_entries i 1 oldT)
      (run.limitChronology_source_entries i 2 oldT) rank
    rw [run.limitChronologyFields_values i 0 old, run.limitChronologyFields_values i 1 old,
      run.limitChronologyFields_values i 2 old, run.limitChronologyFields_values i 3 old]
    exact ⟨z, hz, ranked, code⟩

end GroundMainPrefix

section
open SetFormula
universe u v

theorem relationCompose_enlargeCodomain {A B C D f g : ZFSet.{u}}
    (bound : g ⊆ ZFSet.prod B C) (subset : C ⊆ D) :
    relationCompose A B D f g = relationCompose A B C f g := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, hx, y, hy, w, _, rfl, first, second⟩ :=
      (mem_relationCompose _ _ _ _ _ z).1 entry
    exact (mem_relationCompose _ _ _ _ _ _).2
      ⟨x, hx, y, hy, w, (ZFSet.pair_mem_prod.1 (bound second)).2, rfl, first, second⟩
  · intro entry
    obtain ⟨x, hx, y, hy, w, hw, rfl, first, second⟩ :=
      (mem_relationCompose _ _ _ _ _ z).1 entry
    exact (mem_relationCompose _ _ _ _ _ _).2
      ⟨x, hx, y, hy, w, subset hw, rfl, first, second⟩

namespace GroundMainPrefix.FixedTopStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} (data : run.FixedTopStage i₀)

theorem transition_comp {i j : I} (before : i ≤ j) :
    (run.diagram.transition before).map.comp pairing unions powers separation
      (data.transition j) = data.transition i := by
  apply GroundMainTransition.ext
  · change relationCompose _ _ data.stage.carrier _ (run.limitPointMap j) = run.limitPointMap i
    rw [data.carrier_eq, relationCompose_enlargeCodomain
      (run.limitPointMap_injection j).function.1 (fixedTopCarrier_subset run.limitPoints)]
    exact run.limitPointMap_comp before
  · change relationCompose _ _ data.stage.actors _ (run.limitActorMap j) = run.limitActorMap i
    rw [data.actors_eq]
    exact run.limitActorMap_comp before

end GroundMainPrefix.FixedTopStage

end

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_limitSerialization
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) (rank : ZFSet.rank run.code < ZFSet.rank K)
    (level : GroundMainCandidateLevel M K) :
    ∃ serial : GroundSerializedChronology M (insert run.cutoffLimit run.cutoffLimit) C D rD,
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
        serial.code ∈ level.validChronologies C D rD ∧
        serial.fields.graph = run.limitChronologyFields.graph ∧
        (∀ j s, serial.fields.value j s = run.limitChronologyFields.value j s) ∧
        serial.layerBound = functionGraphRange
          (chronologyPairs (insert run.cutoffLimit run.cutoffLimit)) serial.layers := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have numbers := standard.omega_mem pairing unions powers separation hK
  exact run.limitChronologyFields.exists_rankedSerialization
    pairing unions powers separation collection infinite choice hK conditions
    (conditions.successor_mem pairing unions powers separation infinite hK
      (run.cutoffLimit_mem_inaccessible hK standard indices))
    level (ordinalSetProperty_succ run.cutoffLimit_ordinal) run.limitChronologyCore
    (run.limitChronologyFields_graph_rank_lt limit rank)
    (run.limitChronology_raw_witnesses (M.transitive hK numbers) limit rank
      (ZFSet.rank_lt_of_mem numbers))

end GroundMainPrefix

namespace GroundMainPrefix.FixedTopStage
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} (data : run.FixedTopStage i₀)

noncomputable def chronologyValues : Fin 5 → ZFSet.{u} :=
  Fin.cases data.stage.carrier (Fin.cases data.stage.order
    (Fin.cases data.stage.meetGraph
      (Fin.cases (fixedTopBirth run.limitPoints run.limitBirth run.cutoffLimit)
        (fun _ => data.stage.height))))

structure RankedChronology (level : GroundMainCandidateLevel M K) where
  serial : GroundSerializedChronology M (insert run.cutoffLimit run.cutoffLimit) C D rD
  code_ground : serial.code ∈ M.sets
  code_rank : ZFSet.rank serial.code < ZFSet.rank K
  code_member : serial.code ∈ level.validChronologies C D rD
  graphs : ∀ j, serial.fields.graph j =
    terminalChronologyGraph run.cutoffLimit (run.limitChronologyFields.graph j) (data.chronologyValues j)
  terminal : ∀ j, serial.fields.value j run.cutoffLimit = data.chronologyValues j
  old_values : ∀ j s, s ∈ run.cutoffLimit →
    serial.fields.value j s = run.limitChronologyFields.value j s

theorem exists_rankedChronology
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) (rank : ZFSet.rank run.code < ZFSet.rank K)
    (level : GroundMainCandidateLevel M K) : Nonempty (data.RankedChronology level) := by
  obtain ⟨prior, _, priorRank, _, priorGraphs, priorValues, _⟩ :=
    run.exists_limitSerialization collection infinite choice hK standard indices rank level
  have terminal (j : Fin 5) : prior.fields.value j run.cutoffLimit = run.limitTerminalFields j :=
    (priorValues j run.cutoffLimit).trans (run.limitChronologyFields_terminal j)
  have newValues : prior.fixedTopValues data.stage.height = data.chronologyValues := by
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun _ => rfl)))) j
    · change fixedTopCarrier (prior.fields.value 0 run.cutoffLimit) = data.stage.carrier
      rw [terminal 0]
      exact data.carrier_eq.symm
    · change fixedTopOrder (prior.fields.value 0 run.cutoffLimit)
        (prior.fields.value 1 run.cutoffLimit) = data.stage.order
      rw [terminal 0, terminal 1]
      exact data.order_eq.symm
    · change fixedTopMeet (prior.fields.value 0 run.cutoffLimit)
        (prior.fields.value 1 run.cutoffLimit) = data.stage.meetGraph
      rw [terminal 0, terminal 1]
      exact data.meet_eq.symm
    · change fixedTopBirth (prior.fields.value 0 run.cutoffLimit)
        (prior.fields.value 3 run.cutoffLimit) run.cutoffLimit = _
      rw [terminal 0, terminal 3]
      rfl
  have conditions := standard.to_conditions pairing unions powers separation hK
  have earlier : ∀ x t, ZFSet.pair x t ∈ prior.fields.value 3 run.cutoffLimit → t ∈ run.cutoffLimit := by
    intro x t entry
    rw [terminal 3] at entry
    exact (ZFSet.pair_mem_prod.1 (run.limitBirth_function.1 entry)).2
  have height : StrictLexHeightCode (fixedTopCarrier (prior.fields.value 0 run.cutoffLimit)) C D
      (fixedTopOrder (prior.fields.value 0 run.cutoffLimit) (prior.fields.value 1 run.cutoffLimit))
      data.stage.height rD := by
    rw [terminal 0, terminal 1]
    change StrictLexHeightCode (fixedTopCarrier run.limitPoints) C D
      (fixedTopOrder run.limitPoints run.limitOrder) data.stage.height rD
    rw [← data.carrier_eq, ← data.order_eq]
    exact data.stage.height_code
  obtain ⟨extended, ground, extendedRank, member, graphs, values⟩ :=
    prior.exists_rankedFixedTopSerialization pairing unions powers separation collection infinite choice
      hK conditions (conditions.successor_mem pairing unions powers separation infinite hK
        (run.cutoffLimit_mem_inaccessible hK standard indices)) level priorRank
      data.stage.height data.stage.height_ground (data.height_rank_lt infinite hK standard rank)
      run.cutoffLimit_ordinal earlier height
  refine ⟨⟨extended, ground, extendedRank, member, ?_, ?_, ?_⟩⟩
  · intro j
    rw [congrFun graphs j]
    change terminalChronologyGraph run.cutoffLimit (prior.fields.graph j)
      (prior.fixedTopValues data.stage.height j) = _
    rw [priorGraphs, newValues]
  · intro j
    rw [values j run.cutoffLimit (ZFSet.mem_insert _ _), appendHistoryValue_at, newValues]
  · intro j s hs
    rw [values j s (ZFSet.mem_insert_of_mem _ hs), appendHistoryValue_old hs, priorValues]

namespace RankedChronology
variable {data} {level : GroundMainCandidateLevel M K} (chronology : data.RankedChronology level)

noncomputable def main : GroundChronologicalMainStage M C D rD where
  stage := data.stage
  cutoff := run.cutoffLimit
  cutoff_ground := run.cutoffLimit_ground
  cutoff_ordinal := run.cutoffLimit_ordinal
  history := chronology.serial.toHistory
  carrier_eq := chronology.terminal 0
  order_eq := chronology.terminal 1
  meet_eq := chronology.terminal 2
  height_eq := chronology.terminal 4

theorem main_stage : chronology.main.stage = data.stage := rfl

theorem main_cutoff : chronology.main.cutoff = run.cutoffLimit := rfl

theorem main_birth : chronology.main.birth = fixedTopBirth run.limitPoints run.limitBirth run.cutoffLimit :=
  chronology.terminal 3

theorem agreement (j : Fin 5) (s : ZFSet.{u}) :
    chronology.serial.fields.value j s = chronology.main.history.fieldValue j s := by
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j

theorem history_values (i : I) (j : Fin 5) {s : ZFSet.{u}}
    (before : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) :
    chronology.main.history.fieldValue j s = (run.diagram.stage i).history.fieldValue j s := by
  rw [← chronology.agreement, chronology.old_values j s ((run.cutoffLimit_mem s).2 ⟨i, before⟩)]
  exact run.limitChronologyFields_values i j before

end RankedChronology

end GroundMainPrefix.FixedTopStage

namespace GroundMainPrefix.FixedTopStage.RankedChronology
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} {data : run.FixedTopStage i₀} {level : GroundMainCandidateLevel M K}
variable (chronology : data.RankedChronology level)

noncomputable def transition (i : I) :
    GroundChronologicalMainTransition (run.diagram.stage i) chronology.main where
  map := data.transition i
  cutoff_le := Or.inr (run.cutoff_mem_cutoffLimit i)
  birth := by
    intro x y t entry
    have hy := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).2
    rw [chronology.main_birth, fixedTopBirth_old_iff hy]
    exact run.limitPointMap_birth_iff i x y t entry
  history_prefix := by
    intro s before
    exact ⟨chronology.history_values i 0 before, chronology.history_values i 1 before,
      chronology.history_values i 2 before, chronology.history_values i 3 before,
      chronology.history_values i 4 before⟩

theorem transition_map (i : I) : (chronology.transition i).map = data.transition i := rfl

theorem transition_points (i : I) : (chronology.transition i).map.points = run.limitPointMap i := rfl

theorem transition_actors (i : I) : (chronology.transition i).map.actors = run.limitActorMap i := rfl

theorem coversOldBirths (i : I) : (chronology.transition i).CoversOldBirths := by
  intro y t entry before
  rw [chronology.main_birth] at entry
  have strict : t ∈ run.cutoffLimit := (run.cutoffLimit_mem t).2 ⟨i, before⟩
  have old := (fixedTopBirth_earlier_iff strict).1 entry
  obtain ⟨x, hx, _, image⟩ := (run.limitBirth_old_fiber i y t before).1 old
  exact ⟨x, hx, image⟩

end GroundMainPrefix.FixedTopStage.RankedChronology

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}

namespace FixedTopStage.RankedChronology
variable {i₀ : I} {data : run.FixedTopStage i₀} {level : GroundMainCandidateLevel M K}
variable (chronology : data.RankedChronology level)

theorem invariant (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) (rank : ZFSet.rank run.code < ZFSet.rank K) :
    chronology.main.Invariant K Labels := by
  have bounds := data.invariant_inputs infinite choice hK standard indices rank
  exact ⟨bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2.1, bounds.2.2.2.2.1,
    bounds.2.2.2.2.2.1, bounds.2.2.2.2.2.2.1, bounds.2.2.2.2.2.2.2.1,
    bounds.2.2.2.2.2.2.2.2⟩

noncomputable def linked (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) (rank : ZFSet.rank run.code < ZFSet.rank K) :
    GroundLinkedMainStage M K Labels C D rD :=
  ⟨chronology.main, chronology.serial, fun j s _ => chronology.agreement j s,
    chronology.invariant infinite choice hK standard indices rank, chronology.code_rank⟩

noncomputable def cone : run.diagram.Cone chronology.main where
  leg := chronology.transition
  coherent := by
    intro i j before
    apply GroundChronologicalMainTransition.ext
    change (run.diagram.transition before).map.comp pairing unions powers separation
      (data.transition j) = data.transition i
    exact data.transition_comp before

theorem cone_coverage : chronology.cone.append.CoversOldBirths :=
  chronology.cone.append_coverage run.coverage chronology.coversOldBirths

end FixedTopStage.RankedChronology

variable (run)

theorem exists_rankedAppendLimit (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (indices : M.groundEmbeddable run.indices ZFSet.omega)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (level : GroundMainCandidateLevel M K) :
    ∃ data : run.FixedTopStage i₀,
      ∃ target : GroundLinkedMainStage M K Labels C D rD,
        ∃ extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I),
          target.main.stage = data.stage ∧ target.main.cutoff = run.cutoffLimit ∧
          target.main.birth = fixedTopBirth run.limitPoints run.limitBirth run.cutoffLimit ∧
          target.serial.code ∈ level.validChronologies C D rD ∧
          extended.indices = insert run.indices run.indices ∧
          extended.code ∈ M.sets ∧ ZFSet.rank extended.code < ZFSet.rank K ∧
          extended.code ∈ level.validMainPrefixes Labels C D rD ∧
          (∀ i : I, extended.linked (i : WithTop I) = run.linked i) ∧
          extended.linked ⊤ = target ∧
          extended.stageGraph = insert (ZFSet.pair run.indices target.code) run.stageGraph ∧
          graphRestriction run.indices extended.stageGraph = run.stageGraph ∧
          graphRestriction (chronologyPairs run.indices) extended.transitionGraph = run.transitionGraph ∧
          (∀ (i j : I) (before : i ≤ j),
            (extended.diagram.transition (WithTop.coe_le_coe.mpr before)).map.code =
              (run.diagram.transition before).map.code) ∧
          (∀ i : I,
            (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.points = run.limitPointMap i ∧
            (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.actors = run.limitActorMap i) ∧
          (∀ (i : I) (x y : ZFSet.{u}), ZFSet.pair x y ∈ run.limitPointMap i →
            ZFSet.pair y target.main.stage.top ∈ target.main.stage.order ∧
              ZFSet.pair target.main.stage.top y ∉ target.main.stage.order) := by
  have below : GroundBelow M run.indices K :=
    ⟨ZFSet.omega, standard.omega_mem pairing unions powers separation hK, indices⟩
  obtain ⟨data⟩ := run.exists_fixedTopMainStage i₀ collection infinite choice columns_eq indices
  obtain ⟨chronology⟩ := data.exists_rankedChronology collection infinite choice hK standard below oldRank level
  let target := chronology.linked infinite choice hK standard below oldRank
  have conditions := standard.to_conditions pairing unions powers separation hK
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  obtain ⟨row, ground, function, entries, rowRank⟩ := run.exists_limitTransitionRow limit oldRank
  have rowEntries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
      z = (chronology.cone.leg i).map.code := entries
  let extended := run.appendCone target chronology.cone ground function rowEntries chronology.cone_coverage
  have rank : ZFSet.rank extended.code < ZFSet.rank K :=
    run.appendCone_code_rank_lt target chronology.cone ground function rowEntries chronology.cone_coverage
      limit oldRank (target.code_rank_lt pairing unions powers separation infinite hK conditions) rowRank
  refine ⟨data, target, extended, rfl, rfl, chronology.main_birth, chronology.code_member,
    run.appendCone_indices target chronology.cone ground function rowEntries chronology.cone_coverage,
    extended.code_ground, rank, level.prefix_mem_validMainPrefixes extended rank,
    run.appendCone_linked_old target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_linked_top target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_stageGraph target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_stageGraph_restrict target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_transitionGraph_restrict target chronology.cone ground function rowEntries chronology.cone_coverage,
    ?_, ?_, ?_⟩
  · intro i j before
    rfl
  · intro i
    exact ⟨rfl, rfl⟩
  · intro i x y entry
    exact data.point_strict_top i entry

end GroundMainPrefix

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitPointMap_coverage_iff (x : ZFSet.{u}) :
    x ∈ run.limitPoints ↔ ∃ i y, y ∈ (run.diagram.stage i).stage.carrier ∧
      ZFSet.pair y x ∈ run.limitPointMap i := by
  constructor
  · intro member
    obtain ⟨i, y, hy, equal⟩ := run.pointPresentation.limitPoint_coverage member
    exact ⟨i, y, hy, (run.pointPresentation.inclusion_entry i y x).2 ⟨hy, equal⟩⟩
  · rintro ⟨i, y, _, entry⟩
    exact (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).2

theorem limitActorMap_coverage_iff (g : ZFSet.{u}) :
    g ∈ run.limitActors ↔ ∃ i h, h ∈ (run.diagram.stage i).stage.actors ∧
      ZFSet.pair h g ∈ run.limitActorMap i := by
  constructor
  · intro member
    obtain ⟨i, h, hh, equal⟩ := run.actorPresentation.limitPoint_coverage member
    exact ⟨i, h, hh, (run.actorPresentation.inclusion_entry i h g).2 ⟨hh, equal⟩⟩
  · rintro ⟨i, h, _, entry⟩
    exact (ZFSet.pair_mem_prod.1 ((run.limitActorMap_injection i).function.1 entry)).2

namespace FixedTopStage.RankedChronology
variable {run} {i₀ : I} {data : run.FixedTopStage i₀} {level : GroundMainCandidateLevel M K}
variable (chronology : data.RankedChronology level)

theorem limitCoverage : run.LimitCoverage chronology.main chronology.cone := by
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · intro x
    change (x ∈ data.stage.carrier ∧ x ≠ data.stage.top) ↔
      ∃ i y, y ∈ (run.diagram.stage i).stage.carrier ∧ ZFSet.pair y x ∈ run.limitPointMap i
    rw [data.carrier_eq, data.top_eq, ← run.limitPointMap_coverage_iff]
    constructor
    · rintro ⟨member, different⟩
      exact ((mem_fixedTopCarrier run.limitPoints x).1 member).resolve_left different
    · intro member
      exact ⟨fixedTopCarrier_old member, fun equal => ZFSet.mem_irrefl _ (equal ▸ member)⟩
  · intro g
    change g ∈ data.stage.actors ↔
      ∃ i h, h ∈ (run.diagram.stage i).stage.actors ∧ ZFSet.pair h g ∈ run.limitActorMap i
    rw [data.actors_eq]
    exact run.limitActorMap_coverage_iff g
  · intro i x y entry
    exact data.point_strict_top i entry
  · intro x
    rw [chronology.main_birth]
    change ZFSet.pair x run.cutoffLimit ∈ fixedTopBirth run.limitPoints run.limitBirth run.cutoffLimit ↔
      x = data.stage.top
    rw [data.top_eq]
    exact fixedTopBirth_new_time_iff (fun _ _ entry =>
      (ZFSet.pair_mem_prod.1 (run.limitBirth_function.1 entry)).2)

end FixedTopStage.RankedChronology
end GroundMainPrefix

end PartitionPilot.Forcing

end OAI
