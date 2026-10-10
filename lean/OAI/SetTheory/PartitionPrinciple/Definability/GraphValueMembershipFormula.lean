import OAI.SetTheory.PartitionPrinciple.Forcing.UniqueFiberForcing

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def graphValueMemberFormula {n} (x z beta : Fin n) : BoundedFormula n :=
  exMem z (exMem 0 (exMem 0
    (.conj (pairMembershipFormula beta.succ.succ.succ 0 z.succ.succ.succ)
      (.mem x.succ.succ.succ 0))))

theorem truth_graphValueMemberFormula {n} (x z beta : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (graphValueMemberFormula x z beta) env ↔
      ∃ A, ZFSet.pair (env beta) A ∈ env z ∧ env x ∈ A := by
  simp only [graphValueMemberFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  change (∃ pair ∈ env z, ∃ unordered ∈ pair, ∃ A ∈ unordered,
    ZFSet.pair (env beta) A ∈ env z ∧ env x ∈ A) ↔ _
  constructor
  · rintro ⟨pair, _pairMember, unordered, _unorderedMember, A, _valueMember, edge, member⟩
    exact ⟨A, edge, member⟩
  · rintro ⟨A, edge, member⟩
    exact ⟨ZFSet.pair (env beta) A, edge, {env beta, A}, ZFSet.mem_pair.2 (Or.inr rfl),
      A, ZFSet.mem_pair.2 (Or.inr rfl), edge, member⟩

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.SetFormula
open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem realize_graphValueMember_values (D : Name.NameDomain s) (H : Set P)
    {n} (x z beta : Fin n) (env : Assignment D n) :
    Realize (D.values H) (BoundedFormula.graphValueMemberFormula x z beta).toFormula
      (evalAssignment H env) ↔
      ∃ A, ZFSet.pair (Name.eval H (env beta).val) A ∈ Name.eval H (env z).val ∧
        Name.eval H (env x).val ∈ A := by
  let N : TransitiveGround := ⟨D.values H, D.values_transitive H⟩
  exact (BoundedFormula.realize_toFormula N _ _ (fun i => ⟨env i, rfl⟩)).trans
    (BoundedFormula.truth_graphValueMemberFormula x z beta (evalAssignment H env))

end PartitionPilot.Forcing.SetFormula

end

end OAI
