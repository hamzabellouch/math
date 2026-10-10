import OAI.SetTheory.PartitionPrinciple.Definability.RowAssignmentTransitionFormulas

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def rowAssignmentTransitionFamily (stages history levels : ZFSet.{u}) : ZFSet.{u} :=
  Forcing.rowAssignmentTransitionFamily stages history levels
    (M.groundRelations (⋃₀ ⋃₀ ⋃₀ history) (⋃₀ ⋃₀ ⋃₀ history))

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
  (unions : Realize M.sets SetFormula.union Fin.elim0)
  (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
  {stages history levels : ZFSet.{u}}
  (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hLevels : levels ∈ M.sets)

include pairing unions powers separation hStages hHistory hLevels

private theorem history_cut_bound {i j Qi Qj : ZFSet.{u}} (hj : j ∈ stages)
    (first : ZFSet.pair i Qi ∈ history) (second : ZFSet.pair j Qj ∈ history) :
    rowAssignmentCutGraph Qi Qj levels j ∈
      M.groundRelations (⋃₀ ⋃₀ ⋃₀ history) (⋃₀ ⋃₀ ⋃₀ history) := by
  apply (M.mem_groundRelations _ _ _).2
  refine ⟨M.rowAssignmentCutGraph_mem pairing unions powers separation
    (M.pair_right (M.transitive hHistory first)) (M.pair_right (M.transitive hHistory second))
    hLevels (M.transitive hStages hj), ?_⟩
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (mem_rowAssignmentCutGraph _ _ _ _ z |>.1 hz).1
  exact ZFSet.pair_mem_prod.2
    ⟨ZFSet.mem_sUnion.2 ⟨Qi, pair_second_mem_doubleUnion first, hx⟩,
      ZFSet.mem_sUnion.2 ⟨Qj, pair_second_mem_doubleUnion second, hy⟩⟩

theorem rowAssignmentTransitionFamily_mem : M.rowAssignmentTransitionFamily stages history levels ∈ M.sets := by
  let B := ⋃₀ ⋃₀ ⋃₀ history
  let W := M.groundRelations B B
  have hB : B ∈ M.sets := M.union_mem unions (M.union_mem unions (M.union_mem unions hHistory))
  have hW : W ∈ M.sets := M.groundRelations_mem pairing unions powers separation hB hB
  let params : Fin 4 → ZFSet.{u} := ![stages, history, levels, W]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hStages
    (Fin.cases hHistory (Fin.cases hLevels (Fin.cases hW (fun j => Fin.elim0 j))))
  have bound := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation hStages hStages) hW
  have selected := M.separation_mem separation (rowAssignmentTransitionFormula 0 1 2 3 4) params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets (rowAssignmentTransitionFormula 0 1 2 3 4)
      (extend z params)) (ZFSet.prod (ZFSet.prod stages stages) W) =
      M.rowAssignmentTransitionFamily stages history levels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, rowAssignmentTransitionFamily, mem_rowAssignmentTransitionFamily]
    apply and_congr_right
    intro hz
    exact M.realize_rowAssignmentTransitionFormula pairing unions powers separation 0 1 2 3 4
      (extend z params) (Fin.cases (M.transitive bound hz) ground)
  exact equal ▸ selected

theorem rowAssignmentTransitionFamily_function (function : FunctionGraphOn stages history) :
    ZFSet.IsFunc (ZFSet.prod stages stages)
      (M.groundRelations (⋃₀ ⋃₀ ⋃₀ history) (⋃₀ ⋃₀ ⋃₀ history))
      (M.rowAssignmentTransitionFamily stages history levels) := by
  apply Forcing.rowAssignmentTransitionFamily_function function
  intro i _ j hj Qi Qj first second
  exact M.history_cut_bound pairing unions powers separation hStages hHistory hLevels hj first second

theorem rowAssignmentTransitionFamily_entry (function : FunctionGraphOn stages history)
    {i j Qi Qj R : ZFSet.{u}} (first : ZFSet.pair i Qi ∈ history)
    (second : ZFSet.pair j Qj ∈ history) :
    ZFSet.pair (ZFSet.pair i j) R ∈ M.rowAssignmentTransitionFamily stages history levels ↔
      R = rowAssignmentCutGraph Qi Qj levels j := by
  rw [rowAssignmentTransitionFamily, Forcing.rowAssignmentTransitionFamily_entry_iff function first second]
  refine ⟨fun h => h.2, ?_⟩
  intro equal
  refine ⟨?_, equal⟩
  rw [equal]
  exact M.history_cut_bound pairing unions powers separation hStages hHistory hLevels
    (function.pair_source second) first second

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
