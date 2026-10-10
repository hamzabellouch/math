import OAI.SetTheory.PartitionPrinciple.Forcing.GroundSizeWitnesses

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def smallPartialFunctions (X Y N : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => M.groundEmbeddable p N) (M.partialFunctions X Y)

theorem mem_smallPartialFunctions (X Y N p : ZFSet.{u}) :
    p ∈ M.smallPartialFunctions X Y N ↔
      p ∈ M.sets ∧ PartialFunctionCode X Y p ∧ M.groundEmbeddable p N := by
  rw [smallPartialFunctions, ZFSet.mem_sep, M.mem_partialFunctions]
  exact and_assoc

theorem smallPartialFunctions_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {X Y N : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) (hN : N ∈ M.sets) :
    M.smallPartialFunctions X Y N ∈ M.sets := by
  have space := M.partialFunctions_mem pairing unions powers separation hX hY
  let params := extend N Fin.elim0
  have selected := M.separation_mem separation (hasInjectionFormula 0 1)
    params (Fin.cases hN (fun j => Fin.elim0 j)) space
  have eq : ZFSet.sep (fun p => Realize M.sets (hasInjectionFormula 0 1) (extend p params))
      (M.partialFunctions X Y) = M.smallPartialFunctions X Y N := by
    apply ZFSet.ext
    intro p
    rw [ZFSet.mem_sep, smallPartialFunctions, ZFSet.mem_sep]
    constructor
    · rintro ⟨hp, rel⟩
      exact ⟨hp, (M.realize_hasInjectionFormula 0 1 (extend p params)
        (Fin.cases (M.transitive space hp) (Fin.cases hN (fun j => Fin.elim0 j)))).1 rel⟩
    · rintro ⟨hp, small⟩
      exact ⟨hp, (M.realize_hasInjectionFormula 0 1 (extend p params)
        (Fin.cases (M.transitive space hp) (Fin.cases hN (fun j => Fin.elim0 j)))).2 small⟩
  exact eq ▸ selected

theorem empty_mem_smallPartialFunctions (X Y N : ZFSet.{u}) (nonempty : M.sets.Nonempty) :
    (∅ : ZFSet.{u}) ∈ M.smallPartialFunctions X Y N :=
  (M.mem_smallPartialFunctions X Y N ∅).2
    ⟨M.empty_mem nonempty, PartialFunctionCode.empty X Y, M.empty_groundEmbeddable N nonempty⟩

theorem smallPartialFunction_countable {X Y N p : ZFSet.{u}}
    (hp : p ∈ M.smallPartialFunctions X Y N) [Countable (SetMembers N)] : Countable (SetMembers p) :=
  M.groundEmbeddable_countable ((M.mem_smallPartialFunctions X Y N p).1 hp).2.2

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
