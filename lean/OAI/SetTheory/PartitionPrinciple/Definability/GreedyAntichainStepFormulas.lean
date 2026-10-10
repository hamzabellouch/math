import OAI.SetTheory.PartitionPrinciple.Forcing.GreedyAntichainTraces
import OAI.SetTheory.PartitionPrinciple.Models.GroundChoiceEnumerationSteps

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def antichainBlockedFormula {n} (q Q order D alpha prior : Fin n) : BoundedFormula n :=
  exMem alpha (exMem D.succ (.conj (pairMembershipFormula 1 0 prior.succ.succ)
    (exMem Q.succ.succ (.conj (pairMembershipFormula 0 q.succ.succ.succ order.succ.succ.succ)
      (pairMembershipFormula 0 1 order.succ.succ.succ)))))

theorem truth_antichainBlockedFormula {n} (q Q order D alpha prior : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (antichainBlockedFormula q Q order D alpha prior) env ↔
      ∃ beta ∈ env alpha, ∃ p ∈ env D, ZFSet.pair beta p ∈ env prior ∧
        ∃ r ∈ env Q, ZFSet.pair r (env q) ∈ env order ∧ ZFSet.pair r p ∈ env order := by
  simp only [antichainBlockedFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  rfl

def antichainEligibleFormula {n} (E Q order D alpha prior : Fin n) : BoundedFormula n :=
  .conj (.allMem E (.mem 0 D.succ)) (.allMem D
    (.conj (imp (.mem 0 E.succ)
      (.neg (antichainBlockedFormula 0 Q.succ order.succ D.succ alpha.succ prior.succ)))
      (imp (.neg (antichainBlockedFormula 0 Q.succ order.succ D.succ alpha.succ prior.succ))
        (.mem 0 E.succ))))

theorem truth_antichainEligibleFormula {n} (E Q order D alpha prior : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (antichainEligibleFormula E Q order D alpha prior) env ↔
      env E = antichainEligible (env Q) (env order) (env D) (env alpha) (env prior) := by
  simp only [antichainEligibleFormula, Truth, truth_imp, truth_antichainBlockedFormula, ← iff_def]
  change ((∀ q ∈ env E, q ∈ env D) ∧ ∀ q ∈ env D,
    q ∈ env E ↔ ¬ ∃ beta ∈ env alpha, ∃ p ∈ env D,
      ZFSet.pair beta p ∈ env prior ∧ ∃ r ∈ env Q,
        ZFSet.pair r q ∈ env order ∧ ZFSet.pair r p ∈ env order) ↔ _
  constructor
  · rintro ⟨subset, spec⟩
    apply ZFSet.ext
    intro q
    rw [mem_antichainEligible]
    exact ⟨fun hq => ⟨subset q hq, (spec q (subset q hq)).1 hq⟩,
      fun ⟨hq, fresh⟩ => (spec q hq).2 fresh⟩
  · intro equal
    rw [equal]
    exact ⟨fun _ hq => (mem_antichainEligible _ _ _ _ _ _).1 hq |>.1,
      fun q hq => by rw [mem_antichainEligible]; exact and_iff_right hq⟩

def greedyAntichainStepFormula {n} (Q order D F c alpha prior y : Fin n) : BoundedFormula n :=
  disj (exMem F (.conj (antichainEligibleFormula 0 Q.succ order.succ D.succ alpha.succ prior.succ)
    (pairMembershipFormula 0 y.succ c.succ)))
    (.conj (.neg (exMem D (.neg
      (antichainBlockedFormula 0 Q.succ order.succ D.succ alpha.succ prior.succ)))) (.equal y D))

theorem truth_greedyAntichainStepFormula {n} (Q order D F c alpha prior y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (greedyAntichainStepFormula Q order D F c alpha prior y) env ↔
      GreedyAntichainStep (env Q) (env order) (env D) (env F) (env c)
        (env alpha) (env prior) (env y) := by
  simp only [greedyAntichainStepFormula, truth_disj, truth_exMem, Truth,
    truth_antichainEligibleFormula, truth_pairMembershipFormula, truth_antichainBlockedFormula]
  change ((∃ E ∈ env F, E = antichainEligible (env Q) (env order) (env D) (env alpha) (env prior) ∧
    ZFSet.pair E (env y) ∈ env c) ∨
    (¬ (∃ q ∈ env D, ¬ ∃ beta ∈ env alpha, ∃ p ∈ env D,
      ZFSet.pair beta p ∈ env prior ∧ ∃ r ∈ env Q,
        ZFSet.pair r q ∈ env order ∧ ZFSet.pair r p ∈ env order) ∧ env y = env D)) ↔ _
  have nonempty : (antichainEligible (env Q) (env order) (env D) (env alpha) (env prior)).Nonempty ↔
      ∃ q ∈ env D, ¬ ∃ beta ∈ env alpha, ∃ p ∈ env D,
        ZFSet.pair beta p ∈ env prior ∧ ∃ r ∈ env Q,
          ZFSet.pair r q ∈ env order ∧ ZFSet.pair r p ∈ env order := by
    change (∃ q, q ∈ antichainEligible (env Q) (env order) (env D) (env alpha) (env prior)) ↔ _
    simp only [mem_antichainEligible]
  simp only [GreedyAntichainStep, nonempty]

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
