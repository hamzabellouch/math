import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionHeightSteps

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def rowAssignmentOrder (Q C B r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ q ∈ C, ∃ A ∈ B, ∃ p ∈ C, ∃ D ∈ B,
    z = ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∧ ZFSet.pair q p ∈ r ∧ D ⊆ A)
    (ZFSet.prod Q Q)

theorem mem_rowAssignmentOrder (Q C B r z : ZFSet.{u}) :
    z ∈ rowAssignmentOrder Q C B r ↔ z ∈ ZFSet.prod Q Q ∧
      ∃ q ∈ C, ∃ A ∈ B, ∃ p ∈ C, ∃ D ∈ B,
        z = ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∧ ZFSet.pair q p ∈ r ∧ D ⊆ A :=
  ZFSet.mem_sep

theorem pair_mem_rowAssignmentOrder (Q C B r q A p D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈ rowAssignmentOrder Q C B r ↔
      ZFSet.pair q A ∈ Q ∧ ZFSet.pair p D ∈ Q ∧
        q ∈ C ∧ A ∈ B ∧ p ∈ C ∧ D ∈ B ∧ ZFSet.pair q p ∈ r ∧ D ⊆ A := by
  rw [mem_rowAssignmentOrder, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hqQ,hpQ⟩,q',hq,A',hA,p',hp,D',hD,equal,rows,subset⟩
    obtain ⟨left,right⟩ := ZFSet.pair_injective equal
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective left
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective right
    exact ⟨hqQ,hpQ,hq,hA,hp,hD,rows,subset⟩
  · rintro ⟨hqQ,hpQ,hq,hA,hp,hD,rows,subset⟩
    exact ⟨⟨hqQ,hpQ⟩,q,hq,A,hA,p,hp,D,hD,rfl,rows,subset⟩

namespace BoundedFormula

def rowAssignmentOrderFormula {n} (z C B r : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  exMem C (exMem B.succ (exMem C.succ.succ (exMem B.succ.succ.succ
    (.conj (pairOfPairsFormula (lift z) 3 2 1 0)
      (.conj (pairMembershipFormula 3 1 (lift r)) (subsetFormula 0 2))))))

theorem truth_rowAssignmentOrderFormula {n} (z C B r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (rowAssignmentOrderFormula z C B r) env ↔
      ∃ q ∈ env C, ∃ A ∈ env B, ∃ p ∈ env C, ∃ D ∈ env B,
        env z = ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∧
          ZFSet.pair q p ∈ env r ∧ D ⊆ A := by
  simp only [rowAssignmentOrderFormula, truth_exMem, Truth,
    truth_pairOfPairsFormula, truth_pairMembershipFormula, truth_subsetFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

theorem rowAssignmentOrder_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q C B r : ZFSet.{u}} (hQ : Q ∈ M.sets) (hC : C ∈ M.sets)
    (hB : B ∈ M.sets) (hr : r ∈ M.sets) : rowAssignmentOrder Q C B r ∈ M.sets := by
  let params := extend C (extend B (extend r Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.rowAssignmentOrderFormula 0 1 2 3) params
    (Fin.cases hC (Fin.cases hB (Fin.cases hr (fun j => Fin.elim0 j))))
    (M.prod_mem pairing unions powers separation hQ hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.rowAssignmentOrderFormula 0 1 2 3) (extend z params))
      (ZFSet.prod Q Q) = rowAssignmentOrder Q C B r := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mem_rowAssignmentOrder]
    exact and_congr Iff.rfl (BoundedFormula.truth_rowAssignmentOrderFormula 0 1 2 3 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
