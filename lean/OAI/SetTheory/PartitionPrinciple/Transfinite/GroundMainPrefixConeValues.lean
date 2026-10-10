import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixLimitCoverageConstruction

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
variable {target : GroundChronologicalMainStage M C D rD} (cone : run.diagram.Cone target)

noncomputable def pointCone : run.pointSystem.InjectiveCone target.stage.carrier where
  map i := (cone.leg i).map.points
  injection i := (cone.leg i).map.point_embedding.injection
  coherence := by
    intro i j before
    exact congrArg (fun t => t.map.points) (cone.coherent before).symm

noncomputable def actorCone : run.actorSystem.InjectiveCone target.stage.actors where
  map i := (cone.leg i).map.actors
  injection i := (cone.leg i).map.group_embedding.injection
  coherence := by
    intro i j before
    exact congrArg (fun t => t.map.actors) (cone.coherent before).symm

theorem pointCone_kernel {i j : I} {x y a b : ZFSet.{u}}
    (xa : ZFSet.pair x a ∈ (cone.leg i).map.points)
    (yb : ZFSet.pair y b ∈ (cone.leg j).map.points) :
    a = b ↔ run.pointSystem.Related i x j y :=
  (run.pointCone cone).entry_eq_iff_related xa yb

theorem actorCone_kernel {i j : I} {x y a b : ZFSet.{u}}
    (xa : ZFSet.pair x a ∈ (cone.leg i).map.actors)
    (yb : ZFSet.pair y b ∈ (cone.leg j).map.actors) :
    a = b ↔ run.actorSystem.Related i x j y :=
  (run.actorCone cone).entry_eq_iff_related xa yb

namespace LimitCoverage
variable {run cone} (coverage : run.LimitCoverage target cone)
include coverage

theorem point_quotient_bijection :
    InjectionCode run.limitPoints (ZFSet.sep (fun x => x ≠ target.stage.top) target.stage.carrier)
      (run.pointPresentation.coneMap (run.pointCone cone)) ∧
    ∀ y, y ∈ target.stage.carrier → y ≠ target.stage.top →
      ∃ q ∈ run.limitPoints, ZFSet.pair q y ∈ run.pointPresentation.coneMap (run.pointCone cone) := by
  have bound (i : I) (x y : ZFSet.{u}) (entry : ZFSet.pair x y ∈ (run.pointCone cone).map i) :
      y ∈ ZFSet.sep (fun z => z ≠ target.stage.top) target.stage.carrier := by
    exact ZFSet.mem_sep.2 ((coverage.points y).2
      ⟨i, x, ((run.pointCone cone).entry_bounds entry).1, entry⟩)
  refine ⟨run.pointPresentation.coneMap_injection_into (run.pointCone cone) bound, ?_⟩
  intro y member different
  exact (run.pointPresentation.coneMap_range (run.pointCone cone) y).2
    ((coverage.points y).1 ⟨member, different⟩)

theorem actor_quotient_bijection :
    InjectionCode run.limitActors target.stage.actors
      (run.actorPresentation.coneMap (run.actorCone cone)) ∧
    ∀ g ∈ target.stage.actors, ∃ q ∈ run.limitActors,
      ZFSet.pair q g ∈ run.actorPresentation.coneMap (run.actorCone cone) := by
  refine ⟨run.actorPresentation.coneMap_injection (run.actorCone cone), ?_⟩
  intro g member
  exact (run.actorPresentation.coneMap_range (run.actorCone cone) g).2 ((coverage.actors g).1 member)

end LimitCoverage

theorem pointConeMap_order_iff {p q a b : ZFSet.{u}}
    (pa : ZFSet.pair p a ∈ run.pointPresentation.coneMap (run.pointCone cone))
    (qb : ZFSet.pair q b ∈ run.pointPresentation.coneMap (run.pointCone cone)) :
    ZFSet.pair a b ∈ target.stage.order ↔ ZFSet.pair p q ∈ run.limitOrder := by
  have hp := (ZFSet.pair_mem_prod.1 (run.pointPresentation.coneMap_subset (run.pointCone cone) pa)).1
  have hq := (ZFSet.pair_mem_prod.1 (run.pointPresentation.coneMap_subset (run.pointCone cone) qb)).1
  obtain ⟨i, x, y, hx, hy, rfl, rfl⟩ := run.pointPresentation.pair_coverage hp hq
  have xa := (run.pointPresentation.coneMap_at (run.pointCone cone) i hx a).1 pa
  have yb := (run.pointPresentation.coneMap_at (run.pointCone cone) i hy b).1 qb
  exact ((cone.leg i).map.order_iff x y a b xa yb).trans
    ((run.limitOrder_entry _ _).trans (run.limitLE_at i hx hy)).symm

theorem pointConeMap_map_meet {p q r a b c : ZFSet.{u}}
    (meet : ZFSet.pair (ZFSet.pair p q) r ∈ run.limitMeetGraph)
    (pa : ZFSet.pair p a ∈ run.pointPresentation.coneMap (run.pointCone cone))
    (qb : ZFSet.pair q b ∈ run.pointPresentation.coneMap (run.pointCone cone))
    (rc : ZFSet.pair r c ∈ run.pointPresentation.coneMap (run.pointCone cone)) :
    ZFSet.pair (ZFSet.pair a b) c ∈ target.stage.meetGraph := by
  obtain ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl, entry⟩ :=
    (run.limitMeetGraph_entry p q r).1 meet
  exact (cone.leg i).map.point_embedding.map_meet x y z a b c entry
    ((run.pointPresentation.coneMap_at (run.pointCone cone) i hx a).1 pa)
    ((run.pointPresentation.coneMap_at (run.pointCone cone) i hy b).1 qb)
    ((run.pointPresentation.coneMap_at (run.pointCone cone) i hz c).1 rc)

theorem pointConeMap_meetEmbedding :
    MeetEmbeddingCode run.limitPoints target.stage.carrier run.limitOrder target.stage.order
      run.limitMeetGraph target.stage.meetGraph
      (run.pointPresentation.coneMap (run.pointCone cone)) where
  injection := run.pointPresentation.coneMap_injection (run.pointCone cone)
  monotone _ _ _ _ lower first second := (run.pointConeMap_order_iff cone first second).2 lower
  map_meet _ _ _ _ _ _ meet first second third := run.pointConeMap_map_meet cone meet first second third

theorem pointConeMap_meet_iff {p q r a b c : ZFSet.{u}}
    (pa : ZFSet.pair p a ∈ run.pointPresentation.coneMap (run.pointCone cone))
    (qb : ZFSet.pair q b ∈ run.pointPresentation.coneMap (run.pointCone cone))
    (rc : ZFSet.pair r c ∈ run.pointPresentation.coneMap (run.pointCone cone)) :
    ZFSet.pair (ZFSet.pair a b) c ∈ target.stage.meetGraph ↔
      ZFSet.pair (ZFSet.pair p q) r ∈ run.limitMeetGraph := by
  constructor
  · intro meet
    have hp := (ZFSet.pair_mem_prod.1 (run.pointPresentation.coneMap_subset (run.pointCone cone) pa)).1
    have hq := (ZFSet.pair_mem_prod.1 (run.pointPresentation.coneMap_subset (run.pointCone cone) qb)).1
    obtain ⟨s, hs, value⟩ := run.limitMeet_total hp hq
    have source := (run.limitMeetGraph_entry p q s).2 value
    obtain ⟨d, sd, _⟩ := (run.pointPresentation.coneMap_function (run.pointCone cone)).2 s hs
    have mapped := run.pointConeMap_map_meet cone source pa qb sd
    have equal : d = c :=
      (show FunctionGraphOn (ZFSet.prod target.stage.carrier target.stage.carrier) target.stage.meetGraph from
        ⟨target.stage.carrier, target.stage.meet.operation⟩).unique mapped meet
    have same : s = r := (run.pointPresentation.coneMap_injection (run.pointCone cone)).injective
      s r c (equal ▸ sd) rc
    exact same ▸ source
  · exact fun meet => run.pointConeMap_map_meet cone meet pa qb rc

theorem actorConeMap_mul {g h k a b c : ZFSet.{u}}
    (product : ZFSet.pair (ZFSet.pair g h) k ∈ run.limitMultiplication)
    (ga : ZFSet.pair g a ∈ run.actorPresentation.coneMap (run.actorCone cone))
    (hb : ZFSet.pair h b ∈ run.actorPresentation.coneMap (run.actorCone cone))
    (kc : ZFSet.pair k c ∈ run.actorPresentation.coneMap (run.actorCone cone)) :
    ZFSet.pair (ZFSet.pair a b) c ∈ target.stage.multiplication := by
  obtain ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl, entry⟩ :=
    (run.limitMultiplication_entry g h k).1 product
  exact (cone.leg i).map.group_embedding.mul x y z a b c entry
    ((run.actorPresentation.coneMap_at (run.actorCone cone) i hx a).1 ga)
    ((run.actorPresentation.coneMap_at (run.actorCone cone) i hy b).1 hb)
    ((run.actorPresentation.coneMap_at (run.actorCone cone) i hz c).1 kc)

theorem actorConeMap_groupEmbedding (i₀ : I) :
    GroupEmbeddingCode run.limitActors target.stage.actors run.limitMultiplication target.stage.multiplication
      (run.limitIdentity i₀) target.stage.identity (run.actorPresentation.coneMap (run.actorCone cone)) where
  injection := run.actorPresentation.coneMap_injection (run.actorCone cone)
  one := (run.actorPresentation.coneMap_at (run.actorCone cone) i₀
    (run.diagram.stage i₀).stage.group_code.identity_mem target.stage.identity).2
      (cone.leg i₀).map.group_embedding.one
  mul _ _ _ _ _ _ product first second third := run.actorConeMap_mul cone product first second third

theorem actorConeMap_inv {g h a b : ZFSet.{u}}
    (inverse : ZFSet.pair g h ∈ run.limitInverse)
    (ga : ZFSet.pair g a ∈ run.actorPresentation.coneMap (run.actorCone cone))
    (hb : ZFSet.pair h b ∈ run.actorPresentation.coneMap (run.actorCone cone)) :
    ZFSet.pair a b ∈ target.stage.inverse := by
  obtain ⟨i, x, y, hx, hy, rfl, rfl, entry⟩ := (run.limitInverse_entry g h).1 inverse
  exact (cone.leg i).map.group_embedding.map_inv (run.diagram.stage i).stage.group_code target.stage.group_code
    entry ((run.actorPresentation.coneMap_at (run.actorCone cone) i hx a).1 ga)
    ((run.actorPresentation.coneMap_at (run.actorCone cone) i hy b).1 hb)

theorem coneMaps_equivariant {g p q a x y : ZFSet.{u}}
    (action : ZFSet.pair (ZFSet.pair g p) q ∈ run.limitAction)
    (ga : ZFSet.pair g a ∈ run.actorPresentation.coneMap (run.actorCone cone))
    (px : ZFSet.pair p x ∈ run.pointPresentation.coneMap (run.pointCone cone))
    (qy : ZFSet.pair q y ∈ run.pointPresentation.coneMap (run.pointCone cone)) :
    ZFSet.pair (ZFSet.pair a x) y ∈ target.stage.action := by
  obtain ⟨i, h, v, w, hh, hv, hw, rfl, rfl, rfl, entry⟩ := (run.limitAction_entry g p q).1 action
  exact (cone.leg i).map.equivariant h a v w x y
    ((run.actorPresentation.coneMap_at (run.actorCone cone) i hh a).1 ga)
    ((run.pointPresentation.coneMap_at (run.pointCone cone) i hv x).1 px)
    ((run.pointPresentation.coneMap_at (run.pointCone cone) i hw y).1 qy) entry

theorem pointConeMap_bottom (i₀ : I) :
    ZFSet.pair (run.limitBottom i₀) target.stage.bottom ∈
      run.pointPresentation.coneMap (run.pointCone cone) :=
  (run.pointPresentation.coneMap_at (run.pointCone cone) i₀
    (run.diagram.stage i₀).stage.bottom_mem target.stage.bottom).2 (cone.leg i₀).map.bottom

theorem pointConeMap_height {p q : ZFSet.{u}}
    (entry : ZFSet.pair p q ∈ run.pointPresentation.coneMap (run.pointCone cone)) (t : ZFSet.{u}) :
    ZFSet.pair q t ∈ target.stage.height ↔ ZFSet.pair p t ∈ run.limitHeight := by
  obtain ⟨i, x, hx, rfl, image⟩ := (run.pointPresentation.coneMap_entry (run.pointCone cone) p q).1 entry
  exact ((cone.leg i).map.height x q t image).trans (run.limitHeight_at i hx t).symm

theorem pointConeMap_birth {p q : ZFSet.{u}}
    (entry : ZFSet.pair p q ∈ run.pointPresentation.coneMap (run.pointCone cone)) (t : ZFSet.{u}) :
    ZFSet.pair q t ∈ target.birth ↔ ZFSet.pair p t ∈ run.limitBirth := by
  obtain ⟨i, x, hx, rfl, image⟩ := (run.pointPresentation.coneMap_entry (run.pointCone cone) p q).1 entry
  exact ((cone.leg i).birth x q t image).trans (run.limitBirth_at i hx t).symm

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
