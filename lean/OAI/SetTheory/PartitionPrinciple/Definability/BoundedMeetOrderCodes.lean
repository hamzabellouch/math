import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainStageFromCodes

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def meetOrderFormula {n} (P r μ : Fin n) : BoundedFormula n :=
  .conj (partialOrderFormula P r) (.conj (binaryFunctionFormula P μ)
    (.allMem P (.allMem P.succ (.allMem P.succ.succ
      (imp (tripleMembershipFormula 2 1 0 μ.succ.succ.succ)
        (.conj (pairMembershipFormula 0 2 r.succ.succ.succ)
          (.conj (pairMembershipFormula 0 1 r.succ.succ.succ)
            (.allMem P.succ.succ.succ (imp
              (.conj (pairMembershipFormula 0 3 r.succ.succ.succ.succ)
                (pairMembershipFormula 0 2 r.succ.succ.succ.succ))
              (pairMembershipFormula 0 1 r.succ.succ.succ.succ))))))))))

theorem truth_meetOrderFormula {n} (P r μ : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (meetOrderFormula P r μ) env ↔ MeetOrderCode (env P) (env r) (env μ) := by
  simp only [meetOrderFormula, Truth, truth_partialOrderFormula,
    truth_binaryFunctionFormula, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  constructor
  · rintro ⟨order, operation, laws⟩
    have bounds (x y z : ZFSet.{u}) (entry : ZFSet.pair (ZFSet.pair x y) z ∈ env μ) :
        x ∈ env P ∧ y ∈ env P ∧ z ∈ env P := by
      have shape := ZFSet.pair_mem_prod.1 (operation.1 entry)
      exact ⟨(ZFSet.pair_mem_prod.1 shape.1).1,
        (ZFSet.pair_mem_prod.1 shape.1).2, shape.2⟩
    refine ⟨order, operation, ?_, ?_, ?_⟩
    · intro x y z entry
      have h := bounds x y z entry
      exact (laws x h.1 y h.2.1 z h.2.2 entry).1
    · intro x y z entry
      have h := bounds x y z entry
      exact (laws x h.1 y h.2.1 z h.2.2 entry).2.1
    · intro x y z w hw entry wx wy
      have h := bounds x y z entry
      exact (laws x h.1 y h.2.1 z h.2.2 entry).2.2 w hw ⟨wx, wy⟩
  · intro meet
    exact ⟨meet.order, meet.operation, fun x _ y _ z _ entry =>
      ⟨meet.lower_left x y z entry, meet.lower_right x y z entry,
        fun w hw ⟨wx, wy⟩ => meet.greatest x y z w hw entry wx wy⟩⟩

theorem realize_meetOrderFormula (M : TransitiveGround.{u}) {n}
    (P r μ : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (meetOrderFormula P r μ).toFormula env ↔
      MeetOrderCode (env P) (env r) (env μ) :=
  (realize_toFormula M _ env members).trans (truth_meetOrderFormula P r μ env)

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
