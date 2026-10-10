import OAI.SetTheory.PartitionPrinciple.Geometry.GroundOrdinarySubmodelReflection

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable)

include pairing unions powers separation collection infinite choice small in
theorem countableFunction_sequenceReflection
    {X Y U : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) (hU : U ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    let s := SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega)),
      H.GenericFor (M.codedFamily s) → H.GenericFor (formulaFamily (M.nameDomain s)) →
        GroundSequenceReflection M (M.ordinaryExtension s H) U := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  let := M.smallFunctionTop X Y ZFSet.omega ⟨X, hX⟩
  let s := SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)
  dsimp only
  intro H genericCoded genericFormula
  exact M.ordinaryExtension_sequenceReflection s pairing unions powers separation collection infinite
    choice (M.countablePartialFunctions_mem pairing unions powers separation infinite hX hY)
    (M.countableFunctionOrder_mem pairing unions powers separation infinite hX hY) small hU
    (M.countable_function_internally_closed pairing unions powers separation infinite choice hX hY)
    H genericCoded genericFormula

include pairing unions powers separation collection infinite choice small in
theorem exists_countableFunction_generic_sequenceReflection
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets)
    (p : SetMembers (M.smallPartialFunctions X Y ZFSet.omega)) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    let s := SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)
    ∃ H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega)),
      H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      ∀ U ∈ M.sets, GroundSequenceReflection M (M.ordinaryExtension s H) U := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  obtain ⟨H, hp, genericCoded, genericFormula⟩ :=
    M.exists_countableFunction_generic small pairing unions powers separation infinite hX hY p
  exact ⟨H, hp, genericCoded, genericFormula, fun _ hU =>
    M.countableFunction_sequenceReflection pairing unions powers separation collection infinite choice
      small hX hY hU H genericCoded genericFormula⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
