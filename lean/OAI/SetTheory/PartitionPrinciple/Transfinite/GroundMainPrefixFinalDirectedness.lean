import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixLimitBottom

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

theorem limitPoints_directed {x y : ZFSet.{u}}
    (hx : x ∈ run.limitPoints) (hy : y ∈ run.limitPoints) :
    ∃ z ∈ run.limitPoints, ZFSet.pair x z ∈ run.limitOrder ∧
      ZFSet.pair y z ∈ run.limitOrder := by
  obtain ⟨i, a, b, ha, hb, rfl, rfl⟩ := run.pointPresentation.pair_coverage hx hy
  have ht := (run.diagram.stage i).stage.top_mem
  refine ⟨run.pointPresentation.limitPoint i (run.diagram.stage i).stage.top,
    run.pointPresentation.limitPoint_mem ht, ?_, ?_⟩
  · exact (run.limitOrder_entry _ _).2 ((run.limitLE_at i ha ht).2
      ((run.diagram.stage i).stage.greatest a ha))
  · exact (run.limitOrder_entry _ _).2 ((run.limitLE_at i hb ht).2
      ((run.diagram.stage i).stage.greatest b hb))

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
