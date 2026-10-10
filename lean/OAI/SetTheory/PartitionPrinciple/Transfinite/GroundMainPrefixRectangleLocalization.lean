import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainPrefixLimitActionLaws
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundTaskBearingRectangles

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem rectangle_data_coverage {c b d X g h : ZFSet.{u}}
    (hc : c ∈ run.limitPoints) (hb : b ∈ run.limitPoints)
    (hd : d ∈ run.limitPoints) (hX : X ∈ run.limitPoints)
    (hg : g ∈ run.limitActors) (hh : h ∈ run.limitActors) :
    ∃ i c₀ b₀ d₀ X₀ g₀ h₀,
      c₀ ∈ (run.diagram.stage i).stage.carrier ∧ b₀ ∈ (run.diagram.stage i).stage.carrier ∧
      d₀ ∈ (run.diagram.stage i).stage.carrier ∧ X₀ ∈ (run.diagram.stage i).stage.carrier ∧
      g₀ ∈ (run.diagram.stage i).stage.actors ∧ h₀ ∈ (run.diagram.stage i).stage.actors ∧
      c = run.pointPresentation.limitPoint i c₀ ∧ b = run.pointPresentation.limitPoint i b₀ ∧
      d = run.pointPresentation.limitPoint i d₀ ∧ X = run.pointPresentation.limitPoint i X₀ ∧
      g = run.actorPresentation.limitPoint i g₀ ∧ h = run.actorPresentation.limitPoint i h₀ := by
  obtain ⟨i, c₀, b₀, d₀, hc₀, hb₀, hd₀, rfl, rfl, rfl⟩ :=
    run.pointPresentation.triple_coverage hc hb hd
  obtain ⟨j, X₀, g₀, h₀, hX₀, hg₀, hh₀, rfl, rfl, rfl⟩ :=
    run.pointPresentation.mixed_triple_coverage run.actorPresentation run.actorPresentation hX hg hh
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  obtain ⟨c', cc⟩ := run.pointSystem.map_entry_total ik hc₀
  obtain ⟨b', bb⟩ := run.pointSystem.map_entry_total ik hb₀
  obtain ⟨d', dd⟩ := run.pointSystem.map_entry_total ik hd₀
  obtain ⟨X', XX⟩ := run.pointSystem.map_entry_total jk hX₀
  obtain ⟨g', gg⟩ := run.actorSystem.map_entry_total jk hg₀
  obtain ⟨h', hhhh⟩ := run.actorSystem.map_entry_total jk hh₀
  exact ⟨k, c', b', d', X', g', h', (run.pointSystem.map_entry_bounds ik cc).2,
    (run.pointSystem.map_entry_bounds ik bb).2, (run.pointSystem.map_entry_bounds ik dd).2,
    (run.pointSystem.map_entry_bounds jk XX).2, (run.actorSystem.map_entry_bounds jk gg).2,
    (run.actorSystem.map_entry_bounds jk hhhh).2, run.pointPresentation.limitPoint_transition ik cc,
    run.pointPresentation.limitPoint_transition ik bb, run.pointPresentation.limitPoint_transition ik dd,
    run.pointPresentation.limitPoint_transition jk XX, run.actorPresentation.limitPoint_transition jk gg,
    run.actorPresentation.limitPoint_transition jk hhhh⟩

theorem limitMaps_agreement_reflect (i : I) {g h v : ZFSet.{u}}
    (hg : g ∈ (run.diagram.stage i).stage.actors)
    (hh : h ∈ (run.diagram.stage i).stage.actors)
    (hv : v ∈ (run.diagram.stage i).stage.carrier)
    (agree : ActionAgreementBelow run.limitPoints run.limitOrder run.limitAction
      (run.actorPresentation.limitPoint i g) (run.actorPresentation.limitPoint i h)
      (run.pointPresentation.limitPoint i v)) :
    ActionAgreementBelow (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.order
      (run.diagram.stage i).stage.action g h v := by
  intro x hx y hy lower
  have finalLower := (run.limitOrder_entry _ _).2 ((run.limitLE_at i hx hv).2 lower)
  exact (run.limitAction_at i hg hx hy).symm.trans
    ((agree _ (run.pointPresentation.limitPoint_mem hx) _ (run.pointPresentation.limitPoint_mem hy)
      finalLower).trans (run.limitAction_at i hh hx hy))

theorem limitRectangle_reflect (i : I) {c b d g h : ZFSet.{u}}
    (hc : c ∈ (run.diagram.stage i).stage.carrier)
    (hb : b ∈ (run.diagram.stage i).stage.carrier)
    (hd : d ∈ (run.diagram.stage i).stage.carrier)
    (hg : g ∈ (run.diagram.stage i).stage.actors)
    (hh : h ∈ (run.diagram.stage i).stage.actors)
    (rectangle : ExternalRectangleCode run.limitPoints run.limitActors run.limitOrder
      run.limitMeetGraph run.limitAction (run.pointPresentation.limitPoint i c)
      (run.pointPresentation.limitPoint i b) (run.pointPresentation.limitPoint i d)
      (run.actorPresentation.limitPoint i g) (run.actorPresentation.limitPoint i h)) :
    ExternalRectangleCode (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.actors
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph
      (run.diagram.stage i).stage.action c b d g h := by
  obtain ⟨_, _, _, _, _, cd, bd, W, _, meetW, agree, separated⟩ := rectangle
  obtain ⟨w, meetw, _⟩ := (run.diagram.stage i).stage.meet.operation.2
    (ZFSet.pair c b) (ZFSet.pair_mem_prod.2 ⟨hc, hb⟩)
  have hw := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.meet.operation.1 meetw)).2
  have equal : W = run.pointPresentation.limitPoint i w := run.limitMeet_unique
    ((run.limitMeetGraph_entry _ _ _).1 meetW) ((run.limitMeet_at i hc hb hw).2 meetw)
  rw [equal] at agree separated
  refine ⟨hc, hb, hd, hg, hh, (run.limitLE_at i hc hd).1 ((run.limitOrder_entry _ _).1 cd),
    (run.limitLE_at i hb hd).1 ((run.limitOrder_entry _ _).1 bd), w, hw, meetw,
    run.limitMaps_agreement_reflect i hg hh hw agree, ?_⟩
  intro y hy z hz v hv actions
  exact (run.limitMeet_at i hy hz hv).1 ((run.limitMeetGraph_entry _ _ _).1
    (separated _ (run.pointPresentation.limitPoint_mem hy) _ (run.pointPresentation.limitPoint_mem hz)
      _ (run.pointPresentation.limitPoint_mem hv)
      ⟨(run.limitAction_at i hg hd hy).2 actions.1, (run.limitAction_at i hh hd hz).2 actions.2.1,
        (run.limitAction_at i hg hw hv).2 actions.2.2⟩))

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
