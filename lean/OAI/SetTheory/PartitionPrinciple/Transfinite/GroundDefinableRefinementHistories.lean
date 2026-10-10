import OAI.SetTheory.PartitionPrinciple.Definability.RefinementDataHistoryEntryFormulas

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

noncomputable def refinementDataHistoryIndicesSetFormula {n : Nat}
    (output stages history : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.refinementDataHistoryIndicesEntryFormula stages.succ history.succ 0).toFormula

noncomputable def refinementDataHistoryLevelsSetFormula {n : Nat}
    (output stages history T : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.refinementDataHistoryLevelsEntryFormula stages.succ history.succ T.succ 0).toFormula

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_refinementDataHistoryIndicesSetFormula {n : Nat}
    (output stages history : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (refinementDataHistoryIndicesSetFormula output stages history) env ↔
      env output = refinementDataHistoryIndices (env stages) (env history) := by
  have ground := M.refinementDataHistoryIndices_mem pairing unions powers separation
    (members stages) (members history)
  apply M.realize_exactSetFormula output _ env (members output)
    (fun _ member => M.transitive ground member)
  intro z hz
  exact (BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members)).trans
    (BoundedFormula.truth_refinementDataHistoryIndicesEntryFormula stages.succ history.succ 0 _)

theorem realize_refinementDataHistoryLevelsSetFormula {n : Nat}
    (output stages history T : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (refinementDataHistoryLevelsSetFormula output stages history T) env ↔
      env output = refinementDataHistoryLevels (env stages) (env history) (env T) := by
  have ground := M.refinementDataHistoryLevels_mem pairing unions powers separation
    (members stages) (members history) (members T)
  apply M.realize_exactSetFormula output _ env (members output)
    (fun _ member => M.transitive ground member)
  intro z hz
  exact (BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members)).trans
    (BoundedFormula.truth_refinementDataHistoryLevelsEntryFormula stages.succ history.succ T.succ 0 _)

noncomputable def definable_refinementDataHistoryIndices : GroundDefinableFunction M
    (fun env : Fin 2 → ZFSet.{u} => refinementDataHistoryIndices (env 0) (env 1)) where
  formula := refinementDataHistoryIndicesSetFormula 0 1 2
  closed := fun _ members => M.refinementDataHistoryIndices_mem pairing unions powers separation
    (members 0) (members 1)
  correct := fun env members z hz => M.realize_refinementDataHistoryIndicesSetFormula
    pairing unions powers separation 0 1 2 (extend z env) (Fin.cases hz members)

noncomputable def definable_refinementDataHistoryLevels : GroundDefinableFunction M
    (fun env : Fin 3 → ZFSet.{u} => refinementDataHistoryLevels (env 0) (env 1) (env 2)) where
  formula := refinementDataHistoryLevelsSetFormula 0 1 2 3
  closed := fun _ members => M.refinementDataHistoryLevels_mem pairing unions powers separation
    (members 0) (members 1) (members 2)
  correct := fun env members z hz => M.realize_refinementDataHistoryLevelsSetFormula
    pairing unions powers separation 0 1 2 3 (extend z env) (Fin.cases hz members)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
