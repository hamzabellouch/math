import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixRectangleLocalization

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

theorem limitRectangleAtBound (i : I) {c b d g h X k l : ZFSet.{u}}
    (hc : c ∈ (run.diagram.stage i).stage.carrier)
    (hb : b ∈ (run.diagram.stage i).stage.carrier)
    (hd : d ∈ (run.diagram.stage i).stage.carrier)
    (hX : X ∈ (run.diagram.stage i).stage.carrier)
    (hg : g ∈ (run.diagram.stage i).stage.actors)
    (hh : h ∈ (run.diagram.stage i).stage.actors)
    (hk : k ∈ (run.diagram.stage i).stage.actors)
    (hl : l ∈ (run.diagram.stage i).stage.actors)
    (code : RectangleAtBoundCode (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.order
      (run.diagram.stage i).stage.meetGraph (run.diagram.stage i).stage.action c b d g h X k l) :
    RectangleAtBoundCode run.limitPoints run.limitOrder run.limitMeetGraph run.limitAction
      (run.pointPresentation.limitPoint i c) (run.pointPresentation.limitPoint i b)
      (run.pointPresentation.limitPoint i d) (run.actorPresentation.limitPoint i g)
      (run.actorPresentation.limitPoint i h) (run.pointPresentation.limitPoint i X)
      (run.actorPresentation.limitPoint i k) (run.actorPresentation.limitPoint i l) := by
  have imageC := (run.pointPresentation.inclusion_entry i c _).2 ⟨hc, rfl⟩
  have imageB := (run.pointPresentation.inclusion_entry i b _).2 ⟨hb, rfl⟩
  have imageG := (run.actorPresentation.inclusion_entry i g _).2 ⟨hg, rfl⟩
  have imageH := (run.actorPresentation.inclusion_entry i h _).2 ⟨hh, rfl⟩
  have imageK := (run.actorPresentation.inclusion_entry i k _).2 ⟨hk, rfl⟩
  have imageL := (run.actorPresentation.inclusion_entry i l _).2 ⟨hl, rfl⟩
  refine ⟨run.limitMaps_agreement i _ _ _ _ _ _ imageK imageG imageC code.first_agreement,
    run.limitMaps_agreement i _ _ _ _ _ _ imageL imageH imageC code.second_agreement,
    run.limitMaps_agreement i _ _ _ _ _ _ imageK imageL imageB code.common_agreement, ?_⟩
  obtain ⟨v, hv, w, hw, y, hy, z, hz, t, ht, gv, hwAct, ky, lz, kt, lt, rootK, rootL, cross⟩ := code.values
  exact ⟨run.pointPresentation.limitPoint i v, run.pointPresentation.limitPoint_mem hv,
    run.pointPresentation.limitPoint i w, run.pointPresentation.limitPoint_mem hw,
    run.pointPresentation.limitPoint i y, run.pointPresentation.limitPoint_mem hy,
    run.pointPresentation.limitPoint i z, run.pointPresentation.limitPoint_mem hz,
    run.pointPresentation.limitPoint i t, run.pointPresentation.limitPoint_mem ht,
    (run.limitAction_at i hg hc hv).2 gv, (run.limitAction_at i hh hc hw).2 hwAct,
    (run.limitAction_at i hk hd hy).2 ky, (run.limitAction_at i hl hd hz).2 lz,
    (run.limitAction_at i hk hb ht).2 kt, (run.limitAction_at i hl hb ht).2 lt,
    (run.limitMeetGraph_entry _ _ _).2 ((run.limitMeet_at i hy hX hv).2 rootK),
    (run.limitMeetGraph_entry _ _ _).2 ((run.limitMeet_at i hz hX hw).2 rootL),
    (run.limitMeetGraph_entry _ _ _).2 ((run.limitMeet_at i hy hz ht).2 cross)⟩

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
