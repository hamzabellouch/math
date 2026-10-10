import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialCompressionHistory

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets)

noncomputable def compressionHistoryFormula : SetFormula 8 :=
  ordinalRecursionTraceFormula
    (naturalStepFormula (M.compressionSuccessorFormula pairing unions powers separation))

theorem realize_compressionHistoryFormula
    {N history initial I Sources Reps G T : ZFSet.{u}}
    (hN : N ∈ M.sets) (hHistory : history ∈ M.sets) (hInitial : initial ∈ M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    Realize M.sets (M.compressionHistoryFormula pairing unions powers separation)
      (extend N (extend history (extend initial
        (extend I (extend Sources (extend Reps (extend G (extend T Fin.elim0)))))))) ↔
      OrdinalRecursionTrace
        (groundRecursionStep M
          (naturalStepFormula (M.compressionSuccessorFormula pairing unions powers separation))
          (extend initial (extend I (extend Sources (extend Reps (extend G (extend T Fin.elim0)))))))
        N history :=
  M.realize_ordinalRecursionTraceFormula unions _ _
    (Fin.cases hInitial (Fin.cases hI (Fin.cases hSources (Fin.cases hReps
      (Fin.cases hG (Fin.cases hT (fun i => Fin.elim0 i))))))) hN hHistory

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
