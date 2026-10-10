import OAI.SetTheory.PartitionPrinciple.Definability.FlatLimitConditionFormulas

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def rowAssignmentCutGraph (upper lower levels alpha : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ row A,
    z = ZFSet.pair (ZFSet.pair row A) (ZFSet.pair row (assignmentCut levels alpha A)))
    (ZFSet.prod upper lower)

theorem mem_rowAssignmentCutGraph (upper lower levels alpha z : ZFSet.{u}) :
    z ∈ rowAssignmentCutGraph upper lower levels alpha ↔
      z ∈ ZFSet.prod upper lower ∧ ∃ row A,
        z = ZFSet.pair (ZFSet.pair row A) (ZFSet.pair row (assignmentCut levels alpha A)) :=
  ZFSet.mem_sep

theorem pair_mem_rowAssignmentCutGraph (upper lower levels alpha row A target : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair row A) target ∈ rowAssignmentCutGraph upper lower levels alpha ↔
      ZFSet.pair row A ∈ upper ∧ target ∈ lower ∧
        target = ZFSet.pair row (assignmentCut levels alpha A) := by
  rw [mem_rowAssignmentCutGraph, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hp, ht⟩, row', A', equal⟩
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    exact ⟨hp, ht, right⟩
  · rintro ⟨hp, ht, rfl⟩
    exact ⟨⟨hp, ht⟩, row, A, rfl⟩

namespace SetFormula
private def rowAssignmentCutBody {n : Nat} (z levels alpha : Fin n) : BoundedFormula (n + 5) :=
  let old := suffixIndex n 5
  let v := prefixIndex n 5
  .conj (BoundedFormula.orderedPairFormula (old z) (v 3) (v 4))
    (.conj (BoundedFormula.orderedPairFormula (v 3) (v 0) (v 1))
      (.conj (BoundedFormula.orderedPairFormula (v 4) (v 0) (v 2))
        (BoundedFormula.assignmentCutFormula (v 2) (old levels) (old alpha) (v 1))))

def rowAssignmentCutFormula {n : Nat} (z levels alpha : Fin n) : SetFormula n :=
  exBlock 5 (rowAssignmentCutBody z levels alpha).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_rowAssignmentCutFormula {n : Nat} (z levels alpha : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (rowAssignmentCutFormula z levels alpha) env ↔
      ∃ row A, env z = ZFSet.pair (ZFSet.pair row A)
        (ZFSet.pair row (assignmentCut (env levels) (env alpha) A)) := by
  rw [rowAssignmentCutFormula, realize_exBlock]
  have actual (f : Fin 5 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (SetFormula.rowAssignmentCutBody z levels alpha).toFormula
        (extendMany 5 f env) ↔
      env z = ZFSet.pair (f 3) (f 4) ∧ f 3 = ZFSet.pair (f 0) (f 1) ∧
        f 4 = ZFSet.pair (f 0) (f 2) ∧
          f 2 = assignmentCut (env levels) (env alpha) (f 1) := by
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 5 f env ground members)]
    simp only [SetFormula.rowAssignmentCutBody, BoundedFormula.Truth,
      BoundedFormula.truth_orderedPairFormula, BoundedFormula.truth_assignmentCutFormula,
      extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨equal, upper, lower, cut⟩ := (actual f ground).1 body
    rw [upper, lower, cut] at equal
    exact ⟨f 0, f 1, equal⟩
  · rintro ⟨row, A, equal⟩
    have pairGround := equal ▸ members z
    have upper := M.pair_left pairGround
    have lower := M.pair_right pairGround
    let cut := assignmentCut (env levels) (env alpha) A
    let f : Fin 5 → ZFSet.{u} := ![row, A, cut, ZFSet.pair row A, ZFSet.pair row cut]
    have ground : ∀ j, f j ∈ M.sets :=
      Fin.cases (M.pair_left upper) (Fin.cases (M.pair_right upper)
        (Fin.cases (M.pair_right lower) (Fin.cases upper
          (Fin.cases lower (fun j => Fin.elim0 j)))))
    exact ⟨f, ground, (actual f ground).2 ⟨equal, rfl, rfl, rfl⟩⟩

theorem rowAssignmentCutGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {upper lower levels alpha : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLower : lower ∈ M.sets)
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) :
    rowAssignmentCutGraph upper lower levels alpha ∈ M.sets := by
  let params : Fin 2 → ZFSet.{u} := ![levels, alpha]
  have ground : ∀ j, params j ∈ M.sets :=
    Fin.cases hLevels (Fin.cases hAlpha (fun j => Fin.elim0 j))
  have bound := M.prod_mem pairing unions powers separation hUpper hLower
  have selected := M.separation_mem separation (rowAssignmentCutFormula 0 1 2) params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets (rowAssignmentCutFormula 0 1 2) (extend z params))
      (ZFSet.prod upper lower) = rowAssignmentCutGraph upper lower levels alpha := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mem_rowAssignmentCutGraph]
    apply and_congr_right
    intro hz
    exact M.realize_rowAssignmentCutFormula 0 1 2 (extend z params)
      (Fin.cases (M.transitive bound hz) ground)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
