import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNaturalNumbers

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem countablePartialFunctions_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    M.smallPartialFunctions X Y ZFSet.omega ∈ M.sets :=
  M.smallPartialFunctions_mem pairing unions powers separation hX hY
    (M.omega_mem separation infinite)

theorem countablePartialFunction_countable {X Y p : ZFSet.{u}}
    (hp : p ∈ M.smallPartialFunctions X Y ZFSet.omega) : Countable (SetMembers p) :=
  M.smallPartialFunction_countable hp

theorem countableFunctionOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)).conditionOrder ∈ M.sets :=
  M.smallFunctionOrder_mem pairing unions powers separation hX hY
    (M.omega_mem separation infinite)

theorem countablePartialFunctions_restrict (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {X Y p q : ZFSet.{u}} (hp : p ∈ M.smallPartialFunctions X Y ZFSet.omega)
    (hq : q ∈ M.sets) (subset : q ⊆ p) : q ∈ M.smallPartialFunctions X Y ZFSet.omega :=
  M.smallPartialFunctions_restrict separation hp hq (M.omega_mem separation infinite) subset

theorem exists_countableFunction_generic
    (small : M.sets.Countable)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets)
    (p : SetMembers (M.smallPartialFunctions X Y ZFSet.omega)) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∃ H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega)), H.mem p ∧
      H.GenericFor (M.codedFamily (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega))) ∧
      H.GenericFor (formulaFamily (M.nameDomain
        (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)))) :=
  M.exists_smallFunction_generic small pairing unions powers separation hX hY
    (M.omega_mem separation infinite) p

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
