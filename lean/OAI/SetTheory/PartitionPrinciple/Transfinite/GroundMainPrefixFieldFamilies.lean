import OAI.SetTheory.PartitionPrinciple.Transfinite.CodedMainPrefixSystems

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem indices_rank_le_code : ZFSet.rank run.indices ≤ ZFSet.rank run.code := by
  simpa only [code, Fin.cases_zero] using
    (rank_nonemptyTupleCode_field_le 2
      (Fin.cases run.indices (Fin.cases run.stageGraph (fun _ => run.transitionGraph))) 0)

theorem stageGraph_rank_le_code : ZFSet.rank run.stageGraph ≤ ZFSet.rank run.code := by
  simpa only [code, Fin.cases_zero, Fin.cases_succ] using
    (rank_nonemptyTupleCode_field_le 2
      (Fin.cases run.indices (Fin.cases run.stageGraph (fun _ => run.transitionGraph))) (0 : Fin 2).succ)

theorem transitionGraph_rank_le_code : ZFSet.rank run.transitionGraph ≤ ZFSet.rank run.code := by
  simpa only [code, Fin.cases_zero, Fin.cases_succ] using
    (rank_nonemptyTupleCode_field_le 2
      (Fin.cases run.indices (Fin.cases run.stageGraph (fun _ => run.transitionGraph))) (0 : Fin 1).succ.succ)

theorem key_rank_lt_code (i : I) : ZFSet.rank (run.key i) < ZFSet.rank run.code :=
  (ZFSet.rank_lt_of_mem (show run.key i ∈ run.indices from ZFSet.mem_range.2 ⟨i, rfl⟩)).trans_le
    run.indices_rank_le_code

theorem linkedCode_rank_lt_code (i : I) : ZFSet.rank (run.linked i).code < ZFSet.rank run.code :=
  (ZFSet.rank_lt_of_mem (pair_second_mem_doubleUnion ((run.stageGraph_entry i _).2 rfl))).trans_le
    (((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _)).trans run.stageGraph_rank_le_code)

theorem mapCode_rank_lt_code {i j : I} (before : i ≤ j) :
    ZFSet.rank (run.diagram.transition before).map.code < ZFSet.rank run.code :=
  (ZFSet.rank_lt_of_mem (pair_second_mem_doubleUnion ((run.transitionGraph_entry before _).2 rfl))).trans_le
    (((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _)).trans run.transitionGraph_rank_le_code)

noncomputable def stageFieldFamily (j : Fin 11) : ZFSet.{u} :=
  familyCodeGraph run.key (fun i => (run.diagram.stage i).stage.field j)

noncomputable def carrierFamily : ZFSet.{u} := run.stageFieldFamily 0

noncomputable def actorFamily : ZFSet.{u} := run.stageFieldFamily 3

noncomputable def pointMapFamily : ZFSet.{u} :=
  familyCodeGraph (mainTransitionIndexKey run.key) (fun p => (run.diagram.transition p.property).map.points)

noncomputable def actorMapFamily : ZFSet.{u} :=
  familyCodeGraph (mainTransitionIndexKey run.key) (fun p => (run.diagram.transition p.property).map.actors)

theorem stageFieldFamily_ground (j : Fin 11) : run.stageFieldFamily j ∈ M.sets := by
  have stageCodes := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.stage.code)
    (fun i => ZFSet.pair (run.linked i).main.cutoff (run.linked i).serial.code)
    run.key_injective run.indices_ground run.stages_ground).1
  have codes : familyCodeGraph run.key (fun i => (run.diagram.stage i).stage.code) ∈ M.sets := by
    simpa only [run.linked_main] using stageCodes
  exact M.familyCodeGraph_tuple_fields pairing unions powers separation run.key run.key_injective
    run.indices_ground 10 (fun i => (run.diagram.stage i).stage.field) codes j

theorem carrierFamily_ground : run.carrierFamily ∈ M.sets := run.stageFieldFamily_ground 0

theorem actorFamily_ground : run.actorFamily ∈ M.sets := run.stageFieldFamily_ground 3

theorem mapFamilies_ground : run.pointMapFamily ∈ M.sets ∧ run.actorMapFamily ∈ M.sets := by
  have domain : ZFSet.range (mainTransitionIndexKey run.key) ∈ M.sets := by
    rw [mainTransitionIndex_range run.key run.key_order]
    exact M.chronologyPairs_mem pairing unions powers separation run.indices_ground
  exact M.familyCodeGraph_pair_projections pairing unions powers separation
    (mainTransitionIndexKey run.key) _ _ (mainTransitionIndexKey_injective run.key run.key_injective)
    domain run.transitions_ground

theorem pointMapFamily_ground : run.pointMapFamily ∈ M.sets := run.mapFamilies_ground.1

theorem actorMapFamily_ground : run.actorMapFamily ∈ M.sets := run.mapFamilies_ground.2

theorem stageFieldFamily_function (j : Fin 11) : FunctionGraphOn run.indices (run.stageFieldFamily j) :=
  familyCodeGraph_function run.key _ run.key_injective

theorem carrierFamily_function : FunctionGraphOn run.indices run.carrierFamily :=
  run.stageFieldFamily_function 0

theorem actorFamily_function : FunctionGraphOn run.indices run.actorFamily :=
  run.stageFieldFamily_function 3

theorem pointMapFamily_function : FunctionGraphOn (chronologyPairs run.indices) run.pointMapFamily := by
  have function := familyCodeGraph_function (mainTransitionIndexKey run.key)
    (fun p => (run.diagram.transition p.property).map.points)
    (mainTransitionIndexKey_injective run.key run.key_injective)
  rw [mainTransitionIndex_range run.key run.key_order] at function
  exact function

theorem actorMapFamily_function : FunctionGraphOn (chronologyPairs run.indices) run.actorMapFamily := by
  have function := familyCodeGraph_function (mainTransitionIndexKey run.key)
    (fun p => (run.diagram.transition p.property).map.actors)
    (mainTransitionIndexKey_injective run.key run.key_injective)
  rw [mainTransitionIndex_range run.key run.key_order] at function
  exact function

theorem stageFieldFamily_entry (j : Fin 11) (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.stageFieldFamily j ↔ z = (run.diagram.stage i).stage.field j :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i z

theorem carrierFamily_entry (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.carrierFamily ↔ z = (run.diagram.stage i).stage.carrier :=
  run.stageFieldFamily_entry 0 i z

theorem actorFamily_entry (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.actorFamily ↔ z = (run.diagram.stage i).stage.actors :=
  run.stageFieldFamily_entry 3 i z

theorem pointMapFamily_entry {i j : I} (before : i ≤ j) (z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (run.key j) (run.key i)) z ∈ run.pointMapFamily ↔
      z = (run.diagram.transition before).map.points :=
  pair_mem_familyCodeGraph (mainTransitionIndexKey run.key) _
    (mainTransitionIndexKey_injective run.key run.key_injective) ⟨(i, j), before⟩ z

theorem actorMapFamily_entry {i j : I} (before : i ≤ j) (z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (run.key j) (run.key i)) z ∈ run.actorMapFamily ↔
      z = (run.diagram.transition before).map.actors :=
  pair_mem_familyCodeGraph (mainTransitionIndexKey run.key) _
    (mainTransitionIndexKey_injective run.key run.key_injective) ⟨(i, j), before⟩ z

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
