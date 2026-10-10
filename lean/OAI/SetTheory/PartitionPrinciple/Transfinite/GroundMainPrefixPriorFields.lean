import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixLimitCoverageGraph

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def serialFieldUnion (j : Fin 5) : ZFSet.{u} :=
  ⋃₀ ZFSet.range (fun i => (run.linked i).serial.fields.graph j)

theorem serialFieldUnion_ground (j : Fin 5) : run.serialFieldUnion j ∈ M.sets :=
  M.union_mem unions (M.familyCodeGraph_valueRange_mem unions separation run.key _
    run.indices_ground (run.serialFieldFamily_ground j))

theorem serialFieldUnion_rank_le_code (j : Fin 5) :
    ZFSet.rank (run.serialFieldUnion j) ≤ ZFSet.rank run.code :=
  (familyCodeGraph_valueUnion_rank_le run.key _).trans (run.serialFieldFamily_rank_le_code j)

theorem serialFieldUnion_mem (j : Fin 5) (z : ZFSet.{u}) :
    z ∈ run.serialFieldUnion j ↔ ∃ i, z ∈ (run.linked i).serial.fields.graph j :=
  familyCodeGraph_valueUnion_mem_iff _ z

theorem historyFieldValue_transition {i k : I} (before : i ≤ k) (j : Fin 5) {s : ZFSet.{u}}
    (time : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) :
    (run.diagram.stage k).history.fieldValue j s = (run.diagram.stage i).history.fieldValue j s := by
  have equal := (run.diagram.transition before).history_prefix s time
  exact Fin.cases equal.1 (Fin.cases equal.2.1 (Fin.cases equal.2.2.1
    (Fin.cases equal.2.2.2.1 (fun _ => equal.2.2.2.2)))) j

theorem historyFieldValue_compatible (i k : I) (j : Fin 5) {s : ZFSet.{u}}
    (first : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff)
    (second : s = (run.diagram.stage k).cutoff ∨ s ∈ (run.diagram.stage k).cutoff) :
    (run.diagram.stage i).history.fieldValue j s = (run.diagram.stage k).history.fieldValue j s := by
  obtain ⟨m, im, km⟩ := run.common_upper i k
  exact (run.historyFieldValue_transition im j first).symm.trans
    (run.historyFieldValue_transition km j second)

theorem serialFieldGraph_entry (i : I) (j : Fin 5) (s y : ZFSet.{u}) :
    ZFSet.pair s y ∈ (run.linked i).serial.fields.graph j ↔
      (s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) ∧
      y = (run.diagram.stage i).history.fieldValue j s := by
  have historyEqual : (run.linked i).main.history.fieldValue j s =
      (run.diagram.stage i).history.fieldValue j s :=
    congrArg (fun stage : GroundChronologicalMainStage M C D rD => stage.history.fieldValue j s) (run.linked_main i)
  constructor
  · intro entry
    have hs := (ZFSet.pair_mem_prod.1 (((run.linked i).serial.fields.function j).1 entry)).1
    have agreement := (run.linked i).agreement j s hs
    have value := ((run.linked i).serial.fields.value_eq_of_entry j entry).symm.trans agreement
    exact ⟨by simpa only [run.linked_main, ZFSet.mem_insert_iff] using hs,
      value.trans historyEqual⟩
  · rintro ⟨time, equal⟩
    have hs : s ∈ insert (run.linked i).main.cutoff (run.linked i).main.cutoff := by
      simpa only [run.linked_main, ZFSet.mem_insert_iff] using time
    have entry := (run.linked i).serial.fields.value_entry j hs
    have agreement := (run.linked i).agreement j s hs
    rw [agreement] at entry
    have value : ZFSet.pair s ((run.diagram.stage i).history.fieldValue j s) ∈
        (run.linked i).serial.fields.graph j := by rw [← historyEqual]; exact entry
    exact equal.symm ▸ value

theorem serialFieldUnion_entry (j : Fin 5) (s y : ZFSet.{u}) :
    ZFSet.pair s y ∈ run.serialFieldUnion j ↔
      ∃ i, (s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) ∧
        y = (run.diagram.stage i).history.fieldValue j s := by
  rw [run.serialFieldUnion_mem]
  exact exists_congr (fun i => run.serialFieldGraph_entry i j s y)

theorem serialFieldUnion_at (i : I) (j : Fin 5) {s : ZFSet.{u}}
    (time : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) (y : ZFSet.{u}) :
    ZFSet.pair s y ∈ run.serialFieldUnion j ↔ y = (run.diagram.stage i).history.fieldValue j s := by
  rw [run.serialFieldUnion_entry]
  constructor
  · intro h
    obtain ⟨k, before, equal⟩ := h
    exact equal.trans (run.historyFieldValue_compatible k i j before time)
  · intro equal
    exact ⟨i, time, equal⟩

theorem serialFieldUnion_function (j : Fin 5) : FunctionGraphOn run.cutoffLimit (run.serialFieldUnion j) := by
  refine ⟨⋃₀ ⋃₀ run.serialFieldUnion j, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, entry⟩ := (run.serialFieldUnion_mem j z).1 hz
    obtain ⟨s, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (((run.linked i).serial.fields.function j).1 entry)
    have before := ((run.serialFieldGraph_entry i j s y).1 entry).1
    exact ZFSet.pair_mem_prod.2 ⟨(run.cutoffLimit_mem s).2 ⟨i, before⟩, pair_second_mem_doubleUnion hz⟩
  · intro s hs
    obtain ⟨i, before⟩ := (run.cutoffLimit_mem s).1 hs
    exact ⟨(run.diagram.stage i).history.fieldValue j s, (run.serialFieldUnion_at i j before _).2 rfl,
      fun y entry => (run.serialFieldUnion_at i j before y).1 entry⟩

theorem serialFieldUnion_restrict (i : I) (j : Fin 5) :
    graphRestriction (insert (run.diagram.stage i).cutoff (run.diagram.stage i).cutoff)
      (run.serialFieldUnion j) = (run.linked i).serial.fields.graph j := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨s, hs, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    have before := ZFSet.mem_insert_iff.1 hs
    exact (run.serialFieldGraph_entry i j s y).2 ⟨before, (run.serialFieldUnion_at i j before y).1 entry⟩
  · intro entry
    obtain ⟨s, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (((run.linked i).serial.fields.function j).1 entry)
    have before := ((run.serialFieldGraph_entry i j s y).1 entry).1
    exact pair_mem_graphRestriction.2 ⟨(run.serialFieldUnion_mem j _).2 ⟨i, entry⟩,
      ZFSet.mem_insert_iff.2 before⟩

noncomputable def limitPriorFields : GroundChronologyFields M run.cutoffLimit :=
  GroundChronologyFields.ofGraphs pairing unions run.cutoffLimit_ground
    run.serialFieldUnion run.serialFieldUnion_ground run.serialFieldUnion_function

theorem limitPriorFields_graph (j : Fin 5) :
    run.limitPriorFields.graph j = run.serialFieldUnion j := rfl

theorem limitPriorFields_values (i : I) (j : Fin 5) {s : ZFSet.{u}}
    (time : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) :
    run.limitPriorFields.value j s = (run.diagram.stage i).history.fieldValue j s :=
  run.limitPriorFields.value_eq_of_entry j ((run.serialFieldUnion_at i j time _).2 rfl)

theorem limitPriorFields_bound_rank_le_code :
    ZFSet.rank run.limitPriorFields.bound ≤ ZFSet.rank run.code := by
  change ZFSet.rank (⋃₀ ⋃₀ (run.serialFieldUnion 0 ∪ (run.serialFieldUnion 1 ∪
    (run.serialFieldUnion 2 ∪ (run.serialFieldUnion 3 ∪ run.serialFieldUnion 4))))) ≤ _
  apply (ZFSet.rank_sUnion_le _).trans ((ZFSet.rank_sUnion_le _).trans ?_)
  simp only [ZFSet.rank_union]
  exact max_le (run.serialFieldUnion_rank_le_code 0) (max_le (run.serialFieldUnion_rank_le_code 1)
    (max_le (run.serialFieldUnion_rank_le_code 2)
      (max_le (run.serialFieldUnion_rank_le_code 3) (run.serialFieldUnion_rank_le_code 4))))

theorem limitPriorFields_code_ground : run.limitPriorFields.code ∈ M.sets :=
  run.limitPriorFields.code_ground pairing

theorem limitPriorFields_code_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitPriorFields.code < o := by
  apply rank_nonemptyTupleCode_lt limit 6 run.limitPriorFields.codeFields
  exact Fin.cases (run.cutoffLimit_rank_le_code.trans_lt rank)
    (Fin.cases (run.limitPriorFields_bound_rank_le_code.trans_lt rank)
      (fun j => (run.serialFieldUnion_rank_le_code j).trans_lt rank))

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
