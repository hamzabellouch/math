import OAI.SetTheory.PartitionPrinciple.Definability.CodedFilterImages

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

def actionImageFormula {n} (y A g F : Fin n) : BoundedFormula n :=
  exMem F (tripleMembershipFormula g.succ 0 y.succ A.succ)

theorem truth_actionImageFormula {n} (y A g F : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (actionImageFormula y A g F) env ↔
      ∃ x ∈ env F, ZFSet.pair (ZFSet.pair (env g) x) (env y) ∈ env A := by
  simp only [actionImageFormula, truth_exMem, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem actionImage_mem (separation : SeparationSchema M.sets)
    {P A g F : ZFSet.{u}} (hP : P ∈ M.sets) (hA : A ∈ M.sets)
    (hg : g ∈ M.sets) (hF : F ∈ M.sets) : actionImage P A g F ∈ M.sets := by
  let params := extend A (extend g (extend F Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.actionImageFormula 0 1 2 3) params
    (Fin.cases hA (Fin.cases hg (Fin.cases hF (fun i => Fin.elim0 i)))) hP
  have equal : ZFSet.sep (fun y => BoundedFormula.Truth
      (BoundedFormula.actionImageFormula 0 1 2 3) (extend y params)) P =
      actionImage P A g F := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep, mem_actionImage, BoundedFormula.truth_actionImageFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
