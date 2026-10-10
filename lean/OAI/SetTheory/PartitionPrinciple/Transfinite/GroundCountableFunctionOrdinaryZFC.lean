import OAI.SetTheory.PartitionPrinciple.Models.GroundSupportedEqualityChoices

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem countableFunction_ordinaryZF
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    let s := SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega)),
      H.GenericFor (formulaFamily (M.nameDomain s)) →
        ZFRealization (M.ordinaryExtension s H).sets ∧
          CollectionSchema (M.ordinaryExtension s H).sets := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  let := M.smallFunctionTop X Y ZFSet.omega ⟨X, hX⟩
  let s := SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX hY
  have order := M.countableFunctionOrder_mem pairing unions powers separation infinite hX hY
  dsimp only
  intro H generic
  constructor
  · exact M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order infinite H generic
  · intro n
    exact M.ordinaryExtension_collection s pairing unions powers separation collection carrier order H generic

theorem countableFunction_ordinaryZFC
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    let s := SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega)),
      H.GenericFor (formulaFamily (M.nameDomain s)) →
        ZFRealization (M.ordinaryExtension s H).sets ∧
          CollectionSchema (M.ordinaryExtension s H).sets ∧
          Realize (M.ordinaryExtension s H).sets SetFormula.choice Fin.elim0 := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  let := M.smallFunctionTop X Y ZFSet.omega ⟨X, hX⟩
  let s := SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX hY
  have order := M.countableFunctionOrder_mem pairing unions powers separation infinite hX hY
  dsimp only
  intro H generic
  have axioms := M.countableFunction_ordinaryZF pairing unions powers separation collection infinite hX hY H generic
  exact ⟨axioms.1, axioms.2,
    M.ordinaryExtension_choice s pairing unions powers separation collection infinite choice carrier order H generic⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
