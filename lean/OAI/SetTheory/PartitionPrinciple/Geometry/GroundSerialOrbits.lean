import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundNaturalRecursion

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundSerialOrbit
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {W R initial : ZFSet.{u}} (hW : W ∈ M.sets) (hR : R ∈ M.sets)
    (hInitial : initial ∈ W)
    (serial : ∀ x ∈ W, ∃ y ∈ W, ZFSet.pair x y ∈ R) :
    ∃ history ∈ M.sets, ZFSet.IsFunc ZFSet.omega W history ∧
      (∀ y, ZFSet.pair ∅ y ∈ history ↔ y = initial) ∧
      ∀ n ∈ ZFSet.omega, ∀ x y,
        ZFSet.pair n x ∈ history → ZFSet.pair (insert n n) y ∈ history → ZFSet.pair x y ∈ R := by
  obtain ⟨step, hStep, function, selected⟩ :=
    M.uniformize_relation pairing unions powers separation choice hW hW hR serial
  let s := SetMembers.presentation W
  let f := s.decodeFunction s step function
  let b := SetMembers.ofMem initial hInitial
  have graphGround : s.graph s f ∈ M.sets :=
    M.decoded_function_graph_mem s s hStep function
  let history := natPresentation.graph s (fun n => natIterate f b n.down)
  have historyGround : history ∈ M.sets :=
    M.natural_recursion_graph_mem pairing unions powers separation infinite s f b hW graphGround
  have historyFunction : ZFSet.IsFunc ZFSet.omega W history := natPresentation.graph_isFunc s _
  have canonical (n : Nat) :
      ZFSet.pair (natSetCode n) (s.encode (natIterate f b n)) ∈ history :=
    (natPresentation.pair_mem_graph s (fun n => natIterate f b n.down) ⟨n⟩ _).2 rfl
  have entryValue (n : Nat) (y : ZFSet.{u})
      (entry : ZFSet.pair (natSetCode n) y ∈ history) : y = s.encode (natIterate f b n) := by
    obtain ⟨_, _, unique⟩ := historyFunction.2 (natSetCode n) (natSetCode_mem_omega n)
    exact (unique y entry).trans (unique _ (canonical n)).symm
  refine ⟨history, historyGround, historyFunction, ?_, ?_⟩
  · intro y
    constructor
    · intro entry
      exact (entryValue 0 y entry).trans (SetMembers.raw_ofMem initial hInitial)
    · intro equal
      exact equal.symm ▸ (SetMembers.raw_ofMem initial hInitial ▸ canonical 0)
  · intro n hn x y first second
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have firstValue := entryValue k x first
    have secondValue := entryValue (k + 1) y second
    rw [firstValue, secondValue]
    exact selected (s.decodeFunction_mem s step function (natIterate f b k))

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
