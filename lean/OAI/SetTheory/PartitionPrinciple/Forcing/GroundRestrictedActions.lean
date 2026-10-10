import OAI.SetTheory.PartitionPrinciple.Definability.TaskRepresentativeCodes

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem restrictedActionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r A g source : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hA : A ∈ M.sets) (hg : g ∈ M.sets) (hsource : source ∈ M.sets) :
    restrictedActionGraph P r A g source ∈ M.sets := by
  let params := extend P (extend r (extend A (extend g (extend source Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.restrictedActionEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hP (Fin.cases hr (Fin.cases hA (Fin.cases hg
      (Fin.cases hsource (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hP hP)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.restrictedActionEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod P P) = restrictedActionGraph P r A g source := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, restrictedActionGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_restrictedActionEntryFormula 0 1 2 3 4 5 _)
  exact equal ▸ selected

theorem restrictedAction_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r A g source target base : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hA : A ∈ M.sets) (hg : g ∈ M.sets) (hsource : source ∈ M.sets)
    (code : RestrictedActionCode P r A g source target base) : base ∈ M.sets := by
  rw [code.eq_graph]
  exact M.restrictedActionGraph_mem pairing unions powers separation hP hr hA hg hsource

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
