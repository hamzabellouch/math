import OAI.SetTheory.PartitionPrinciple.Definability.RowAssignmentCutGraphLaws

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

noncomputable def rowAssignmentTransitionFamily (stages history levels W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ stages, ∃ j ∈ stages, ∃ Qi Qj R,
    R ∈ W ∧ z = ZFSet.pair (ZFSet.pair i j) R ∧
    ZFSet.pair i Qi ∈ history ∧ ZFSet.pair j Qj ∈ history ∧
    R = rowAssignmentCutGraph Qi Qj levels j)
    (ZFSet.prod (ZFSet.prod stages stages) W)

theorem mem_rowAssignmentTransitionFamily (stages history levels W z : ZFSet.{u}) :
    z ∈ rowAssignmentTransitionFamily stages history levels W ↔
      z ∈ ZFSet.prod (ZFSet.prod stages stages) W ∧
      ∃ i ∈ stages, ∃ j ∈ stages, ∃ Qi Qj R,
        R ∈ W ∧ z = ZFSet.pair (ZFSet.pair i j) R ∧
        ZFSet.pair i Qi ∈ history ∧ ZFSet.pair j Qj ∈ history ∧
        R = rowAssignmentCutGraph Qi Qj levels j := ZFSet.mem_sep

theorem pair_mem_rowAssignmentTransitionFamily (stages history levels W i j R : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i j) R ∈ rowAssignmentTransitionFamily stages history levels W ↔
      i ∈ stages ∧ j ∈ stages ∧ R ∈ W ∧ ∃ Qi Qj,
        ZFSet.pair i Qi ∈ history ∧ ZFSet.pair j Qj ∈ history ∧
        R = rowAssignmentCutGraph Qi Qj levels j := by
  constructor
  · intro entry
    obtain ⟨_, a, ha, b, hb, Qi, Qj, R', hR, equal, first, second, output⟩ :=
      ZFSet.mem_sep.1 entry
    obtain ⟨indices, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 indices
    exact ⟨ha, hb, hR, Qi, Qj, first, second, output⟩
  · rintro ⟨hi, hj, hR, Qi, Qj, first, second, output⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hj⟩, hR⟩,
      i, hi, j, hj, Qi, Qj, R, hR, rfl, first, second, output⟩

theorem rowAssignmentTransitionFamily_entry_iff {stages history levels W i j Qi Qj R : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (first : ZFSet.pair i Qi ∈ history) (second : ZFSet.pair j Qj ∈ history) :
    ZFSet.pair (ZFSet.pair i j) R ∈ rowAssignmentTransitionFamily stages history levels W ↔
      R ∈ W ∧ R = rowAssignmentCutGraph Qi Qj levels j := by
  rw [pair_mem_rowAssignmentTransitionFamily]
  constructor
  · rintro ⟨_, _, hR, Qi', Qj', left, right, equal⟩
    have eqi := function.unique left first
    have eqj := function.unique right second
    exact ⟨hR, eqi ▸ eqj ▸ equal⟩
  · rintro ⟨hR, equal⟩
    exact ⟨function.pair_source first, function.pair_source second, hR, Qi, Qj, first, second, equal⟩

theorem rowAssignmentTransitionFamily_function {stages history levels W : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (bounded : ∀ i ∈ stages, ∀ j ∈ stages, ∀ Qi Qj,
      ZFSet.pair i Qi ∈ history → ZFSet.pair j Qj ∈ history →
      rowAssignmentCutGraph Qi Qj levels j ∈ W) :
    ZFSet.IsFunc (ZFSet.prod stages stages) W (rowAssignmentTransitionFamily stages history levels W) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro k hk
  obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 hk
  obtain ⟨Qi, first⟩ := function.total hi
  obtain ⟨Qj, second⟩ := function.total hj
  refine ⟨rowAssignmentCutGraph Qi Qj levels j,
    (rowAssignmentTransitionFamily_entry_iff function first second).2
      ⟨bounded i hi j hj Qi Qj first second, rfl⟩, ?_⟩
  intro R entry
  exact ((rowAssignmentTransitionFamily_entry_iff function first second).1 entry).2

end PartitionPilot.Forcing

end

end OAI
