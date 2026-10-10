import OAI.SetTheory.PartitionPrinciple.Models.GroundSuccessorInjections

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem finiteBirthHistory_extend (k : Nat) {E history e : ZFSet.{u}}
    (function : ZFSet.IsFunc (natSetCode k) E history) (value : e ∈ E) :
    let next := insert (ZFSet.pair (natSetCode k) e) history
    ZFSet.IsFunc (natSetCode (k + 1)) E next ∧ history ⊆ next ∧
      graphRestriction (natSetCode k) next = history ∧
      ∀ y, ZFSet.pair (natSetCode k) y ∈ next ↔ y = e := by
  let graph : FunctionGraphOn (natSetCode k) history := ⟨E, function⟩
  have extended := graph.successor e
  refine ⟨?_, fun _ member => ZFSet.mem_insert_of_mem _ member, ?_, ?_⟩
  · rw [natSetCode_succ]
    refine ⟨?_, extended.to_isFunc.2⟩
    intro z member
    rcases ZFSet.mem_insert_iff.1 member with rfl | member
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert _ _, value⟩
    · obtain ⟨i, hi, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert_of_mem _ hi, hy⟩
  · exact (graphRestriction_insert_of_not_mem (ZFSet.mem_irrefl (natSetCode k))).trans
      graph.restriction_eq
  · intro y
    constructor
    · intro member
      rcases ZFSet.mem_insert_iff.1 member with equal | old
      · exact (ZFSet.pair_inj.1 equal).2
      · exact False.elim (ZFSet.mem_irrefl (natSetCode k) (graph.pair_source old))
    · intro equal
      exact equal.symm ▸ ZFSet.mem_insert _ _

theorem finiteBirthHistory_initial {E e : ZFSet.{u}} (value : e ∈ E) :
    ZFSet.IsFunc (natSetCode 1) E {ZFSet.pair ∅ e} ∧
      ∀ y, ZFSet.pair ∅ y ∈ ({ZFSet.pair ∅ e} : ZFSet.{u}) ↔ y = e := by
  have empty : ZFSet.IsFunc (natSetCode 0) E (∅ : ZFSet.{u}) :=
    ⟨ZFSet.empty_subset _, fun i hi => False.elim (ZFSet.notMem_empty i hi)⟩
  have first := finiteBirthHistory_extend 0 empty value
  exact ⟨first.1, first.2.2.2⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem finiteBirthHistory_extend_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (k : Nat) {history e : ZFSet.{u}} (ground : history ∈ M.sets) (value : e ∈ M.sets) :
    insert (ZFSet.pair (natSetCode k) e) history ∈ M.sets :=
  M.insert_mem pairing unions
    (M.orderedPair_mem pairing (M.natSetCode_mem separation infinite k) value) ground

theorem finiteBirthHistory_initial_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {e : ZFSet.{u}} (value : e ∈ M.sets) :
    ({ZFSet.pair ∅ e} : ZFSet.{u}) ∈ M.sets := by
  have empty := M.empty_mem ⟨e, value⟩
  have entry := M.orderedPair_mem pairing empty value
  simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing entry entry

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
