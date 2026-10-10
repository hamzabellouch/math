import OAI.SetTheory.PartitionPrinciple.Definability.MainLimitCoverageFormulas

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem assignmentQueriesWithin_mem (separation : SeparationSchema M.sets)
    {Q X T : ZFSet.{u}} (hQ : Q ∈ M.sets) (hX : X ∈ M.sets) (hT : T ∈ M.sets) :
    assignmentQueriesWithin Q X T ∈ M.sets := by
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.assignmentQueryWithinFormula 1 2 0) (extend X (extend T Fin.elim0))
    (Fin.cases hX (Fin.cases hT (fun i => Fin.elim0 i))) hQ
  simpa only [BoundedFormula.truth_assignmentQueryWithinFormula, assignmentQueriesWithin, extend,
    show (1 : Fin 3) = Fin.succ 0 from rfl,
    show (2 : Fin 3) = Fin.succ (Fin.succ 0) from rfl, Fin.cases_zero, Fin.cases_succ] using selected

theorem representativeIndexAdditions_mem (separation : SeparationSchema M.sets)
    {I T Q c X : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hQ : Q ∈ M.sets) (hc : c ∈ M.sets) (hX : X ∈ M.sets) :
    representativeIndexAdditions I T Q c X ∈ M.sets := by
  let params := extend I (extend T (extend Q (extend c (extend X Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.representativeIndexAdditionsMemberFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hT (Fin.cases hQ (Fin.cases hc
      (Fin.cases hX (fun i => Fin.elim0 i)))))) hI
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.representativeIndexAdditionsMemberFormula 0 1 2 3 4 5)
      (extend z params)) I = representativeIndexAdditions I T Q c X := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_representativeIndexAdditionsMemberFormula]
    change (z ∈ I ∧ z ∈ representativeIndexAdditions I T Q c X) ↔ _
    exact ⟨And.right, fun h =>
      ⟨((mem_representativeIndexAdditions I T Q c X z).1 h).1, h⟩⟩
  exact equal ▸ selected

theorem representativeIndexStep_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    {I T Q c X : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hQ : Q ∈ M.sets) (hc : c ∈ M.sets) (hX : X ∈ M.sets) :
    representativeIndexStep I T Q c X ∈ M.sets :=
  M.binary_union_mem pairing unions hX
    (M.representativeIndexAdditions_mem separation hI hT hQ hc hX)

noncomputable def definable_representativeIndexStep
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 5 → ZFSet.{u} =>
      representativeIndexStep (env 1) (env 2) (env 3) (env 4) (env 0)) where
  formula := exactSetFormula 0 (disj (.mem 0 2)
    (BoundedFormula.representativeIndexAdditionsMemberFormula 0 3 4 5 6 2).toFormula)
  closed := fun _ members => M.representativeIndexStep_mem pairing unions separation
    (members 1) (members 2) (members 3) (members 4) (members 0)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
      (fun _ h => M.transitive (M.representativeIndexStep_mem pairing unions separation
        (members 1) (members 2) (members 3) (members 4) (members 0)) h)
    intro w hw
    rw [realize_disj, BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz members)),
      BoundedFormula.truth_representativeIndexAdditionsMemberFormula]
    exact ZFSet.mem_union.symm

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
