import OAI.SetTheory.PartitionPrinciple.Definability.IndexedSubstructureCodes

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {I B R domains : ZFSet.{u}} (hI : I ∈ M.sets) (hB : B ∈ M.sets)
variable (hR : R ∈ M.sets) (hDomains : domains ∈ M.sets)
include pairing unions powers separation hI hB hR hDomains

theorem indexedSuborderGraph_mem : indexedSuborderGraph I B R domains ∈ M.sets := by
  let params := extend I (extend B (extend R (extend domains Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedSuborderEntryFormula 0 1 2 3 4) params
    (Fin.cases hI (Fin.cases hB (Fin.cases hR (Fin.cases hDomains (fun j => Fin.elim0 j)))))
    (M.prod_mem pairing unions powers separation hI hR)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedSuborderEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod I R) = indexedSuborderGraph I B R domains := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_indexedSuborderEntryFormula]
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected

theorem indexedSubmeetGraph_mem : indexedSubmeetGraph I B R domains ∈ M.sets := by
  let params := extend I (extend B (extend R (extend domains Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedSubmeetEntryFormula 0 1 2 3 4) params
    (Fin.cases hI (Fin.cases hB (Fin.cases hR (Fin.cases hDomains (fun j => Fin.elim0 j)))))
    (M.prod_mem pairing unions powers separation hI hR)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedSubmeetEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod I R) = indexedSubmeetGraph I B R domains := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_indexedSubmeetEntryFormula]
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
