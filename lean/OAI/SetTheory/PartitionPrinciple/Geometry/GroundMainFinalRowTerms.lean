import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainFinalChronology

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

namespace TransitiveGround
variable (M)

theorem groundOmegaOne_member_countable {A : ZFSet.{u}}
    (member : A ∈ M.groundOmegaOne pairing unions powers separation collection infinite) :
    M.groundEmbeddable A ZFSet.omega :=
  ((M.groundOmegaOne_spec pairing unions powers separation collection infinite).2.2.1 A).1 member |>.2.2

end TransitiveGround

namespace GroundStandardInaccessible
variable {K : ZFSet.{u}} (standard : GroundStandardInaccessible M K)
include standard

theorem groundOmegaOne_mem (hK : K ∈ M.sets) :
    M.groundOmegaOne pairing unions powers separation collection infinite ∈ K :=
  (standard.to_conditions pairing unions powers separation hK).groundOmegaOne_mem
    pairing unions powers separation collection infinite hK

theorem groundOmegaOne_rank_lt (hK : K ∈ M.sets) :
    ZFSet.rank (M.groundOmegaOne pairing unions powers separation collection infinite) < ZFSet.rank K :=
  ZFSet.rank_lt_of_mem (standard.groundOmegaOne_mem pairing unions powers separation collection infinite hK)

end GroundStandardInaccessible
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem rowPositionSequences_below {L r I mu K : ZFSet.{u}}
    (hL : L ∈ M.sets) (hr : r ∈ M.sets) (hI : I ∈ M.sets)
    (hmu : mu ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (muSmall : GroundBelow M mu K) (positionsSmall : GroundBelow M I K) :
    GroundBelow M (M.rowPositionSequences L r I mu) K :=
  (GroundBelow.relations pairing unions powers separation hmu hI hK ordinal strong
    muSmall positionsSmall).restrict separation
    (M.rowPositionSequences_mem pairing unions powers separation hL hr hI hmu) hK
    (fun _ member => (ZFSet.mem_sep.1 member).1)

theorem exists_infiniteGroundCardinal_bound
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {I K : ZFSet.{u}} (hI : I ∈ M.sets) (hK : K ∈ M.sets)
    (standard : GroundStandardInaccessible M K) (small : GroundBelow M I K) :
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable I mu := by
  let Omega := M.groundOmegaOne pairing unions powers separation collection infinite
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have hOmega : Omega ∈ M.sets := spec.1
  have omegaBelow : GroundBelow M Omega K := GroundBelow.of_member pairing unions powers
    separation hK (standard.groundOmegaOne_mem pairing unions powers separation collection infinite hK)
  obtain ⟨gamma, hgammaK, first, second⟩ := small.common_bound omegaBelow standard.1.1
  have hgamma := M.transitive hK hgammaK
  obtain ⟨mu, hmu, cardinal, bound, f, hf, forward, _, _⟩ :=
    M.exists_groundCardinalRepresentative pairing unions powers separation hgamma
      (ordinalSetProperty_member standard.1.1 hgammaK)
  have hmuK : mu ∈ K := bound.elim (fun equal => equal ▸ hgammaK)
    (fun member => standard.1.1.1 gamma hgammaK mu member)
  obtain ⟨g, hg, intoGamma⟩ := first
  have positions : M.groundEmbeddable I mu :=
    ⟨relationCompose I gamma mu g f,
      M.relationCompose_mem pairing unions powers separation hI hgamma hmu hg hf,
      intoGamma.compose forward⟩
  obtain ⟨e, he, omegaIntoGamma⟩ := second
  have omegaIntoMu : M.groundEmbeddable Omega mu :=
    ⟨relationCompose Omega gamma mu e f,
      M.relationCompose_mem pairing unions powers separation hOmega hgamma hmu he hf,
      omegaIntoGamma.compose forward⟩
  have uncountable : ¬ M.groundEmbeddable mu ZFSet.omega := by
    rintro ⟨b, hb, intoOmega⟩
    obtain ⟨a, ha, intoMu⟩ := omegaIntoMu
    exact spec.2.2.2 ⟨relationCompose Omega mu ZFSet.omega a b,
      M.relationCompose_mem pairing unions powers separation hOmega hmu
        (M.omega_mem separation infinite) ha hb, intoMu.compose intoOmega⟩
  have infiniteBound : ZFSet.omega ⊆ mu := by
    obtain ⟨o, equal⟩ := (ordinalSetProperty_iff mu).1 cardinal.1
    by_cases lower : Ordinal.omega0 ≤ o
    · rw [equal, ← ordinalCode_omega, ordinalCode_subset_iff]
      exact lower
    · have subset : mu ⊆ ZFSet.omega := by
        rw [equal, ← ordinalCode_omega, ordinalCode_subset_iff]
        exact le_of_lt (lt_of_not_ge lower)
      exact False.elim (uncountable ⟨identityFunctionGraph mu,
        M.identityFunctionGraph_mem pairing unions powers separation hmu,
        (identityFunctionGraph_injection mu).retarget subset⟩)
  exact ⟨mu, hmu, hmuK, cardinal, infiniteBound, positions⟩

theorem exists_smallRowPositionSequences
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {L r I K : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets)
    (hI : I ∈ M.sets) (hK : K ∈ M.sets)
    (standard : GroundStandardInaccessible M K) (small : GroundBelow M I K) :
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable I mu ∧ M.rowPositionSequences L r I mu ∈ M.sets ∧
      GroundBelow M (M.rowPositionSequences L r I mu) K := by
  obtain ⟨mu, hmu, hmuK, cardinal, infiniteBound, positions⟩ :=
    M.exists_infiniteGroundCardinal_bound pairing unions powers separation collection infinite
      hI hK standard small
  have conditions := standard.to_conditions pairing unions powers separation hK
  exact ⟨mu, hmu, hmuK, cardinal, infiniteBound, positions,
    M.rowPositionSequences_mem pairing unions powers separation hL hr hI hmu,
    M.rowPositionSequences_below pairing unions powers separation hL hr hI hmu hK
      conditions.1 conditions.2.2.2
      (GroundBelow.of_member pairing unions powers separation hK hmuK) small⟩

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]

structure GroundMainFinalInclusions
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (geometry : GroundMainFinalGeometry M C D rD) where
  pointMap : I → ZFSet.{u}
  actorMap : I → ZFSet.{u}
  pointFamily : ZFSet.{u}
  actorFamily : ZFSet.{u}
  pointMap_ground : ∀ i, pointMap i ∈ M.sets
  actorMap_ground : ∀ i, actorMap i ∈ M.sets
  pointFamily_ground : pointFamily ∈ M.sets
  actorFamily_ground : actorFamily ∈ M.sets
  pointFamily_function : FunctionGraphOn run.indices pointFamily
  actorFamily_function : FunctionGraphOn run.indices actorFamily
  pointFamily_entry : ∀ i f, ZFSet.pair (run.key i) f ∈ pointFamily ↔ f = pointMap i
  actorFamily_entry : ∀ i f, ZFSet.pair (run.key i) f ∈ actorFamily ↔ f = actorMap i
  point_embedding : ∀ i, MeetEmbeddingCode (run.diagram.stage i).stage.carrier geometry.carrier
    (run.diagram.stage i).stage.order geometry.order (run.diagram.stage i).stage.meetGraph
    geometry.meetGraph (pointMap i)
  order_iff : ∀ i x y p q, ZFSet.pair x p ∈ pointMap i → ZFSet.pair y q ∈ pointMap i →
    (ZFSet.pair p q ∈ geometry.order ↔ ZFSet.pair x y ∈ (run.diagram.stage i).stage.order)
  actor_embedding : ∀ i, GroupEmbeddingCode (run.diagram.stage i).stage.actors geometry.actors
    (run.diagram.stage i).stage.multiplication geometry.multiplication
    (run.diagram.stage i).stage.identity geometry.identity (actorMap i)
  inverse_iff : ∀ i a b g h, ZFSet.pair a g ∈ actorMap i → ZFSet.pair b h ∈ actorMap i →
    (ZFSet.pair g h ∈ geometry.inverse ↔ ZFSet.pair a b ∈ (run.diagram.stage i).stage.inverse)
  action_iff : ∀ i a g x y p q, ZFSet.pair a g ∈ actorMap i →
    ZFSet.pair x p ∈ pointMap i → ZFSet.pair y q ∈ pointMap i →
    (ZFSet.pair (ZFSet.pair g p) q ∈ geometry.action ↔
      ZFSet.pair (ZFSet.pair a x) y ∈ (run.diagram.stage i).stage.action)
  bottom : ∀ i, ZFSet.pair (run.diagram.stage i).stage.bottom geometry.bottom ∈ pointMap i
  height : ∀ i x p, ZFSet.pair x p ∈ pointMap i → ∀ t,
    (ZFSet.pair p t ∈ geometry.height ↔ ZFSet.pair x t ∈ (run.diagram.stage i).stage.height)
  birth : ∀ i x p t, ZFSet.pair x p ∈ pointMap i →
    (ZFSet.pair p t ∈ geometry.birth ↔ ZFSet.pair x t ∈ (run.diagram.stage i).birth)
  old_fiber : ∀ i p t, (t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff) →
    (ZFSet.pair p t ∈ geometry.birth ↔ ∃ x ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair x t ∈ (run.diagram.stage i).birth ∧ ZFSet.pair x p ∈ pointMap i)
  point_comp : ∀ {i j} (before : i ≤ j), relationCompose (run.diagram.stage i).stage.carrier
    (run.diagram.stage j).stage.carrier geometry.carrier (run.diagram.transition before).map.points
    (pointMap j) = pointMap i
  actor_comp : ∀ {i j} (before : i ≤ j), relationCompose (run.diagram.stage i).stage.actors
    (run.diagram.stage j).stage.actors geometry.actors (run.diagram.transition before).map.actors
    (actorMap j) = actorMap i
  point_coverage : ∀ p ∈ geometry.carrier, ∃ i x, x ∈ (run.diagram.stage i).stage.carrier ∧
    ZFSet.pair x p ∈ pointMap i
  actor_coverage : ∀ g ∈ geometry.actors, ∃ i a, a ∈ (run.diagram.stage i).stage.actors ∧
    ZFSet.pair a g ∈ actorMap i
  agreement : ∀ i g h g' h' x x', ZFSet.pair g g' ∈ actorMap i →
    ZFSet.pair h h' ∈ actorMap i → ZFSet.pair x x' ∈ pointMap i →
    ActionAgreementBelow (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.order
      (run.diagram.stage i).stage.action g h x →
    ActionAgreementBelow geometry.carrier geometry.order geometry.action g' h' x'

namespace GroundMainPrefix
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def finalInclusions (i₀ : I) : GroundMainFinalInclusions run (run.finalGeometry i₀) where
  pointMap := run.limitPointMap
  actorMap := run.limitActorMap
  pointFamily := run.limitPointInclusions
  actorFamily := run.limitActorInclusions
  pointMap_ground := run.limitPointMap_ground
  actorMap_ground := run.limitActorMap_ground
  pointFamily_ground := run.limitPointInclusions_ground
  actorFamily_ground := run.limitActorInclusions_ground
  pointFamily_function := run.limitPointInclusions_function
  actorFamily_function := run.limitActorInclusions_function
  pointFamily_entry := run.limitPointInclusions_entry
  actorFamily_entry := run.limitActorInclusions_entry
  point_embedding := run.limitPointMap_meetEmbedding
  order_iff := run.limitPointMap_order_iff
  actor_embedding := run.limitActorMap_groupEmbedding i₀
  inverse_iff := run.limitActorMap_inverse_iff
  action_iff := run.limitMaps_action_iff
  bottom := run.limitPointMap_bottom i₀
  height := fun i _ _ image t => run.limitPointMap_height i image t
  birth := run.limitPointMap_birth_iff
  old_fiber := run.limitBirth_old_fiber
  point_comp := run.limitPointMap_comp
  actor_comp := run.limitActorMap_comp
  point_coverage := by
    intro p hp
    obtain ⟨i, x, hx, rfl⟩ := run.pointPresentation.limitPoint_coverage hp
    exact ⟨i, x, hx, (run.pointPresentation.inclusion_entry i x _).2 ⟨hx, rfl⟩⟩
  actor_coverage := by
    intro g hg
    obtain ⟨i, a, ha, rfl⟩ := run.actorPresentation.limitPoint_coverage hg
    exact ⟨i, a, ha, (run.actorPresentation.inclusion_entry i a _).2 ⟨ha, rfl⟩⟩
  agreement := run.limitMaps_agreement

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

theorem finalGeometry_fields_rank_lt (i₀ : I) {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ∀ j, ZFSet.rank ((run.finalGeometry i₀).fields j) < o :=
  Fin.cases (run.limitPoints_rank_lt limit rank) (Fin.cases (run.limitOrder_rank_lt limit rank)
    (Fin.cases (run.limitMeetGraph_rank_lt limit rank) (Fin.cases (run.limitActors_rank_lt limit rank)
      (Fin.cases (run.limitMultiplication_rank_lt limit rank) (Fin.cases (run.limitInverse_rank_lt limit rank)
        (Fin.cases (run.limitIdentity_rank_lt i₀ limit rank) (Fin.cases (run.limitAction_rank_lt limit rank)
          (Fin.cases (run.limitBottom_rank_lt limit rank i₀) (Fin.cases (run.limitHeight_rank_lt limit rank)
            (Fin.cases (run.limitBirth_rank_lt limit rank) (fun _ => run.cutoffLimit_rank_le_code.trans_lt rank)))))))))))

theorem finalGeometry_code_rank_lt (i₀ : I) {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank (run.finalGeometry i₀).code < o :=
  rank_nonemptyTupleCode_lt limit 11 _ (run.finalGeometry_fields_rank_lt i₀ limit rank)

theorem finalInclusions_rank_lt (i₀ : I) {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) :
    ZFSet.rank (run.finalInclusions i₀).pointFamily < o ∧
    ZFSet.rank (run.finalInclusions i₀).actorFamily < o ∧
    ∀ i, ZFSet.rank ((run.finalInclusions i₀).pointMap i) < o ∧
      ZFSet.rank ((run.finalInclusions i₀).actorMap i) < o :=
  ⟨run.limitPointInclusions_rank_lt limit rank, run.limitActorInclusions_rank_lt limit rank,
    fun i => ⟨run.limitPointMap_rank_lt limit rank i, run.limitActorMap_rank_lt limit rank i⟩⟩

theorem finalGeometry_below (i₀ : I) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) :
    GroundBelow M (run.finalGeometry i₀).carrier K ∧ GroundBelow M (run.finalGeometry i₀).actors K :=
  ⟨run.limitPoints_below choice hK standard indices, run.limitActors_below choice hK standard indices⟩

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u v

namespace GroundMainFinalGeometry
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

theorem exists_rowPositionSequences
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (small : GroundBelow M geometry.carrier K) :
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let positions := (SetMembers.presentation geometry.carrier).nonbottom.carrier
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable positions mu ∧
      M.rowPositionSequences geometry.carrier geometry.order positions mu ∈ M.sets ∧
      GroundBelow M (M.rowPositionSequences geometry.carrier geometry.order positions mu) K ∧
      (∅ : ZFSet.{u}) ∈ M.rowPositionSequences geometry.carrier geometry.order positions mu := by
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  have hPositions := M.nonbottom_carrier_mem s separation geometry.carrier_ground
  have positionsSmall : GroundBelow M s.nonbottom.carrier K :=
    small.restrict separation hPositions hK (fun z member => (s.mem_nonbottom_carrier z).1 member |>.1)
  obtain ⟨mu, hmu, hmuK, cardinal, infiniteBound, positions, ground, below⟩ :=
    M.exists_smallRowPositionSequences pairing unions powers separation collection infinite
      geometry.carrier_ground geometry.order_ground hPositions hK standard positionsSmall
  exact ⟨mu, hmu, hmuK, cardinal, infiniteBound, positions, ground, below,
    M.empty_mem_rowPositionSequences hmu cardinal.1 ⟨geometry.bottom, geometry.bottom_mem⟩⟩

end GroundMainFinalGeometry

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_finalRowPositionSequences (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) :
    let geometry := run.finalGeometry i₀
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let positions := (SetMembers.presentation geometry.carrier).nonbottom.carrier
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable positions mu ∧
      M.rowPositionSequences geometry.carrier geometry.order positions mu ∈ M.sets ∧
      GroundBelow M (M.rowPositionSequences geometry.carrier geometry.order positions mu) K ∧
      (∅ : ZFSet.{u}) ∈ M.rowPositionSequences geometry.carrier geometry.order positions mu :=
  (run.finalGeometry i₀).exists_rowPositionSequences pairing unions powers separation
    collection infinite hK standard (run.finalGeometry_below i₀ choice hK standard indices).1

end GroundMainPrefix
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundMainFinalGeometry
open SetFormula SetRealization
open scoped ZFSet
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

theorem exists_smallRowTupleTerms
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (small : GroundBelow M geometry.carrier K) :
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let positions := (SetMembers.presentation geometry.carrier).nonbottom.carrier
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable positions mu ∧
      let S := M.rowPositionSequences geometry.carrier geometry.order positions mu
      S ∈ M.sets ∧ GroundBelow M S K ∧ (∅ : ZFSet.{u}) ∈ S ∧
      ∀ one : SetMembers (M.smallPartialFunctions (ZFSet.prod positions C) (natSetCode 2) ZFSet.omega),
        let rows := M.binaryRowNameGraph positions C one
        let family := rowTupleFamily (SetMembers.raw one) mu positions (⋃₀ ⋃₀ rows) rows S
        let T := rowTupleTerms (SetMembers.raw one) mu positions (⋃₀ ⋃₀ rows) rows S
        family ∈ M.sets ∧ T ∈ M.sets ∧ ZFSet.IsFunc S T family ∧ GroundBelow M T K := by
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  obtain ⟨mu, hmu, hmuK, cardinal, infiniteBound, positions, hS, smallS, empty⟩ :=
    geometry.exists_rowPositionSequences pairing unions powers separation collection infinite hK standard small
  refine ⟨mu, hmu, hmuK, cardinal, infiniteBound, positions, hS, smallS, empty, ?_⟩
  intro one
  exact M.binaryRowTupleTerms_mem_below pairing unions powers separation collection infinite choice
    geometry.carrier_ground geometry.order_ground
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) geometry.columns_ground hmu hK smallS one

end PartitionPilot.Forcing.GroundMainFinalGeometry

end OAI
