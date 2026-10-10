import OAI.SetTheory.PartitionPrinciple.Geometry.GroundContainmentOrders

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def upwardDirectedFormula {n} (l r : Fin n) : BoundedFormula n :=
  .allMem l (.allMem l.succ (exMem l.succ.succ
    (.conj (pairMembershipFormula 2 0 r.succ.succ.succ)
      (pairMembershipFormula 1 0 r.succ.succ.succ))))

theorem truth_upwardDirectedFormula {n} (l r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (upwardDirectedFormula l r) env ↔
      ∀ x ∈ env l, ∀ y ∈ env l, ∃ z ∈ env l,
        ZFSet.pair x z ∈ env r ∧ ZFSet.pair y z ∈ env r := by
  simp only [upwardDirectedFormula, Truth, truth_exMem, truth_pairMembershipFormula]
  rfl

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_upwardDirectedCode {L R : ZFSet.{u}} (hL : L ∈ M.sets) (hR : R ∈ M.sets) :
    Realize M.sets (BoundedFormula.upwardDirectedFormula 0 1).toFormula
      (extend L (extend R Fin.elim0)) ↔
        ∀ x ∈ L, ∀ y ∈ L, ∃ z ∈ L, ZFSet.pair x z ∈ R ∧ ZFSet.pair y z ∈ R :=
  (BoundedFormula.realize_toFormula M _ _
    (Fin.cases hL (Fin.cases hR (fun j => Fin.elim0 j)))).trans
      (BoundedFormula.truth_upwardDirectedFormula 0 1 _)

theorem decoded_upward_directed {L R : ZFSet.{u}} (order : PartialOrderCode L R)
    (hL : L ∈ M.sets) (hR : R ∈ M.sets)
    (laws : Realize M.sets (BoundedFormula.upwardDirectedFormula 0 1).toFormula
      (extend L (extend R Fin.elim0))) :
    letI := order.toPartialOrder
    ∀ C D : SetMembers L, ∃ E, C ≤ E ∧ D ≤ E := by
  let := order.toPartialOrder
  intro C D
  obtain ⟨z, hz, cz, dz⟩ := (M.realize_upwardDirectedCode hL hR).1 laws
    _ (SetMembers.raw_mem C) _ (SetMembers.raw_mem D)
  refine ⟨SetMembers.ofMem z hz, ?_, ?_⟩
  · change ZFSet.pair (SetMembers.raw C) (SetMembers.raw (SetMembers.ofMem z hz)) ∈ R
    rw [SetMembers.raw_ofMem]
    exact cz
  · change ZFSet.pair (SetMembers.raw D) (SetMembers.raw (SetMembers.ofMem z hz)) ∈ R
    rw [SetMembers.raw_ofMem]
    exact dz

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
