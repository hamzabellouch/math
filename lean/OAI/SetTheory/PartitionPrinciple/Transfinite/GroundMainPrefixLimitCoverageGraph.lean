import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixConePreservation
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixDecoding

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
universe u

def LinkedCoverageFieldsCode (z P G cutoff : ZFSet.{u}) : Prop :=
  ∃ r μ m inv one action bottom top height serial,
    z = linkedMainStageCode (mainStageCode P r μ G m inv one action bottom top height) cutoff serial

def MainLimitConeEntryCode (T S row i P G cutoff points actors : ZFSet.{u}) : Prop :=
  i ∈ T ∧ ∃ z, ZFSet.pair i z ∈ S ∧ LinkedCoverageFieldsCode z P G cutoff ∧
    ZFSet.pair (ZFSet.pair T i) (ZFSet.pair points actors) ∈ row

def MainLimitOldPointImageCode (T S row x : ZFSet.{u}) : Prop :=
  ∃ i P G cutoff points actors y, MainLimitConeEntryCode T S row i P G cutoff points actors ∧
    y ∈ P ∧ ZFSet.pair y x ∈ points

def MainLimitOldActorImageCode (T S row g : ZFSet.{u}) : Prop :=
  ∃ i P G cutoff points actors h, MainLimitConeEntryCode T S row i P G cutoff points actors ∧
    h ∈ G ∧ ZFSet.pair h g ∈ actors

def MainLimitOldCutoffCode (T S t : ZFSet.{u}) : Prop :=
  ∃ i ∈ T, ∃ z, ZFSet.pair i z ∈ S ∧
    ∃ P G cutoff, LinkedCoverageFieldsCode z P G cutoff ∧ (t = cutoff ∨ t ∈ cutoff)

structure MainLimitCoverageGraphCode (T S row Q H R top cutoff birth : ZFSet.{u}) : Prop where
  points : ∀ x, (x ∈ Q ∧ x ≠ top) ↔ MainLimitOldPointImageCode T S row x
  actors : ∀ g, g ∈ H ↔ MainLimitOldActorImageCode T S row g
  strict_top : ∀ i P G t points actors, MainLimitConeEntryCode T S row i P G t points actors →
    ∀ x y, ZFSet.pair x y ∈ points → ZFSet.pair y top ∈ R ∧ ZFSet.pair top y ∉ R
  cutoff_mem : ∀ t, t ∈ cutoff ↔ MainLimitOldCutoffCode T S t
  top_birth : ∀ x, ZFSet.pair x cutoff ∈ birth ↔ x = top

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (stage : GroundLinkedMainStage M K Labels C D rD)

theorem coverageFields_iff {P G cutoff : ZFSet.{u}} :
    LinkedCoverageFieldsCode stage.code P G cutoff ↔
      P = stage.main.stage.carrier ∧ G = stage.main.stage.actors ∧ cutoff = stage.main.cutoff := by
  constructor
  · rintro ⟨r, μ, m, inv, one, action, bottom, top, height, serial, equal⟩
    have outer := linkedMainStageCode_inj.1 equal
    have fields := mainStageCode_inj.1 outer.1
    exact ⟨fields.1.symm, fields.2.2.2.1.symm, outer.2.1.symm⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨stage.main.stage.order, stage.main.stage.meetGraph, stage.main.stage.multiplication,
      stage.main.stage.inverse, stage.main.stage.identity, stage.main.stage.action,
      stage.main.stage.bottom, stage.main.stage.top, stage.main.stage.height, stage.serial.code, rfl⟩

end GroundLinkedMainStage

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

structure LimitCoverage (target : GroundChronologicalMainStage M C D rD)
    (cone : run.diagram.Cone target) : Prop where
  points : ∀ x, (x ∈ target.stage.carrier ∧ x ≠ target.stage.top) ↔
    ∃ i y, y ∈ (run.diagram.stage i).stage.carrier ∧ ZFSet.pair y x ∈ (cone.leg i).map.points
  actors : ∀ g, g ∈ target.stage.actors ↔
    ∃ i h, h ∈ (run.diagram.stage i).stage.actors ∧ ZFSet.pair h g ∈ (cone.leg i).map.actors
  strict_top : ∀ i x y, ZFSet.pair x y ∈ (cone.leg i).map.points →
    ZFSet.pair y target.stage.top ∈ target.stage.order ∧
      ZFSet.pair target.stage.top y ∉ target.stage.order
  cutoff : target.cutoff =
    ⋃₀ ZFSet.range (fun i => insert (run.diagram.stage i).cutoff (run.diagram.stage i).cutoff)
  top_birth : ∀ x, ZFSet.pair x target.cutoff ∈ target.birth ↔ x = target.stage.top

namespace LimitCoverage
variable {run} {target : GroundChronologicalMainStage M C D rD}
variable {cone : run.diagram.Cone target} (coverage : run.LimitCoverage target cone)
include coverage

theorem top_absent (i : I) (x : ZFSet.{u}) :
    ZFSet.pair x target.stage.top ∉ (cone.leg i).map.points := by
  intro entry
  have strict := coverage.strict_top i x target.stage.top entry
  exact strict.2 strict.1

theorem new_point_iff {x : ZFSet.{u}} (member : x ∈ target.stage.carrier) :
    (¬ ∃ i y, y ∈ (run.diagram.stage i).stage.carrier ∧
      ZFSet.pair y x ∈ (cone.leg i).map.points) ↔ x = target.stage.top := by
  constructor
  · intro fresh
    by_contra different
    exact fresh ((coverage.points x).1 ⟨member, different⟩)
  · rintro rfl ⟨i, y, _, entry⟩
    exact coverage.top_absent i y entry

end LimitCoverage





noncomputable def stageFieldUnion (j : Fin 11) : ZFSet.{u} :=
  ⋃₀ ZFSet.range (fun i => (run.diagram.stage i).stage.field j)

noncomputable def carrierUnion : ZFSet.{u} := run.stageFieldUnion 0

noncomputable def actorUnion : ZFSet.{u} := run.stageFieldUnion 3

noncomputable def pointMapUnion : ZFSet.{u} :=
  ⋃₀ ZFSet.range (fun p : MainTransitionIndex I => (run.diagram.transition p.property).map.points)

noncomputable def actorMapUnion : ZFSet.{u} :=
  ⋃₀ ZFSet.range (fun p : MainTransitionIndex I => (run.diagram.transition p.property).map.actors)

theorem stageFieldValues_ground (j : Fin 11) :
    ZFSet.range (fun i => (run.diagram.stage i).stage.field j) ∈ M.sets :=
  M.familyCodeGraph_valueRange_mem unions separation run.key _ run.indices_ground
    (run.stageFieldFamily_ground j)

theorem pointMapValues_ground :
    ZFSet.range (fun p : MainTransitionIndex I => (run.diagram.transition p.property).map.points) ∈ M.sets := by
  apply M.familyCodeGraph_valueRange_mem unions separation (mainTransitionIndexKey run.key) _ _
    run.pointMapFamily_ground
  rw [mainTransitionIndex_range run.key run.key_order]
  exact M.chronologyPairs_mem pairing unions powers separation run.indices_ground

theorem actorMapValues_ground :
    ZFSet.range (fun p : MainTransitionIndex I => (run.diagram.transition p.property).map.actors) ∈ M.sets := by
  apply M.familyCodeGraph_valueRange_mem unions separation (mainTransitionIndexKey run.key) _ _
    run.actorMapFamily_ground
  rw [mainTransitionIndex_range run.key run.key_order]
  exact M.chronologyPairs_mem pairing unions powers separation run.indices_ground

theorem stageFieldUnion_ground (j : Fin 11) : run.stageFieldUnion j ∈ M.sets :=
  M.union_mem unions (run.stageFieldValues_ground j)

theorem carrierUnion_ground : run.carrierUnion ∈ M.sets := run.stageFieldUnion_ground 0

theorem actorUnion_ground : run.actorUnion ∈ M.sets := run.stageFieldUnion_ground 3

theorem pointMapUnion_ground : run.pointMapUnion ∈ M.sets := M.union_mem unions run.pointMapValues_ground

theorem actorMapUnion_ground : run.actorMapUnion ∈ M.sets := M.union_mem unions run.actorMapValues_ground

theorem stageFieldUnion_mem (j : Fin 11) (x : ZFSet.{u}) :
    x ∈ run.stageFieldUnion j ↔ ∃ i, x ∈ (run.diagram.stage i).stage.field j :=
  familyCodeGraph_valueUnion_mem_iff _ x

theorem pointMapUnion_mem (x : ZFSet.{u}) :
    x ∈ run.pointMapUnion ↔ ∃ p : MainTransitionIndex I, x ∈ (run.diagram.transition p.property).map.points :=
  familyCodeGraph_valueUnion_mem_iff _ x

theorem actorMapUnion_mem (x : ZFSet.{u}) :
    x ∈ run.actorMapUnion ↔ ∃ p : MainTransitionIndex I, x ∈ (run.diagram.transition p.property).map.actors :=
  familyCodeGraph_valueUnion_mem_iff _ x

theorem stageFieldFamily_subset_union (j : Fin 11) {i X : ZFSet.{u}}
    (entry : ZFSet.pair i X ∈ run.stageFieldFamily j) : X ⊆ run.stageFieldUnion j :=
  familyCodeGraph_value_subset_union run.key _ entry

theorem carrierFamily_subset_union {i X : ZFSet.{u}}
    (entry : ZFSet.pair i X ∈ run.carrierFamily) : X ⊆ run.carrierUnion :=
  run.stageFieldFamily_subset_union 0 entry

theorem actorFamily_subset_union {i X : ZFSet.{u}}
    (entry : ZFSet.pair i X ∈ run.actorFamily) : X ⊆ run.actorUnion :=
  run.stageFieldFamily_subset_union 3 entry

theorem pointMapFamily_subset_union {i X : ZFSet.{u}}
    (entry : ZFSet.pair i X ∈ run.pointMapFamily) : X ⊆ run.pointMapUnion :=
  familyCodeGraph_value_subset_union (mainTransitionIndexKey run.key) _ entry

theorem actorMapFamily_subset_union {i X : ZFSet.{u}}
    (entry : ZFSet.pair i X ∈ run.actorMapFamily) : X ⊆ run.actorMapUnion :=
  familyCodeGraph_value_subset_union (mainTransitionIndexKey run.key) _ entry

theorem stageFieldFamily_rank_le_code (j : Fin 11) :
    ZFSet.rank (run.stageFieldFamily j) ≤ ZFSet.rank run.code := by
  apply (familyCodeGraph_rank_mono run.key _ (fun i => (run.linked i).code) ?_).trans
    run.stageGraph_rank_le_code
  intro i
  simpa only [run.linked_main] using (run.linked i).field_rank_le_linkedCode j

theorem carrierFamily_rank_le_code : ZFSet.rank run.carrierFamily ≤ ZFSet.rank run.code :=
  run.stageFieldFamily_rank_le_code 0

theorem actorFamily_rank_le_code : ZFSet.rank run.actorFamily ≤ ZFSet.rank run.code :=
  run.stageFieldFamily_rank_le_code 3

theorem pointMapFamily_rank_le_code : ZFSet.rank run.pointMapFamily ≤ ZFSet.rank run.code := by
  apply (familyCodeGraph_rank_mono (mainTransitionIndexKey run.key) _
    (fun p => (run.diagram.transition p.property).map.code) ?_).trans run.transitionGraph_rank_le_code
  intro p
  exact rank_nonemptyTupleCode_field_le 1
    (Fin.cases (run.diagram.transition p.property).map.points
      (fun _ => (run.diagram.transition p.property).map.actors)) 0

theorem actorMapFamily_rank_le_code : ZFSet.rank run.actorMapFamily ≤ ZFSet.rank run.code := by
  apply (familyCodeGraph_rank_mono (mainTransitionIndexKey run.key) _
    (fun p => (run.diagram.transition p.property).map.code) ?_).trans run.transitionGraph_rank_le_code
  intro p
  exact rank_nonemptyTupleCode_field_le 1
    (Fin.cases (run.diagram.transition p.property).map.points
      (fun _ => (run.diagram.transition p.property).map.actors)) 1

theorem stageFieldUnion_rank_le_code (j : Fin 11) :
    ZFSet.rank (run.stageFieldUnion j) ≤ ZFSet.rank run.code :=
  (familyCodeGraph_valueUnion_rank_le run.key _).trans (run.stageFieldFamily_rank_le_code j)

theorem carrierUnion_rank_le_code : ZFSet.rank run.carrierUnion ≤ ZFSet.rank run.code :=
  run.stageFieldUnion_rank_le_code 0

theorem actorUnion_rank_le_code : ZFSet.rank run.actorUnion ≤ ZFSet.rank run.code :=
  run.stageFieldUnion_rank_le_code 3

theorem pointMapUnion_rank_le_code : ZFSet.rank run.pointMapUnion ≤ ZFSet.rank run.code :=
  (familyCodeGraph_valueUnion_rank_le (mainTransitionIndexKey run.key) _).trans run.pointMapFamily_rank_le_code

theorem actorMapUnion_rank_le_code : ZFSet.rank run.actorMapUnion ≤ ZFSet.rank run.code :=
  (familyCodeGraph_valueUnion_rank_le (mainTransitionIndexKey run.key) _).trans run.actorMapFamily_rank_le_code





noncomputable def cutoffFamily : ZFSet.{u} :=
  familyCodeGraph run.key (fun i => (run.diagram.stage i).cutoff)

noncomputable def serialFieldFamily (j : Fin 5) : ZFSet.{u} :=
  familyCodeGraph run.key (fun i => (run.linked i).serial.fields.graph j)

noncomputable def birthFamily : ZFSet.{u} :=
  familyCodeGraph run.key (fun i => (run.diagram.stage i).birth)

theorem cutoffFamily_ground : run.cutoffFamily ∈ M.sets := by
  have tails := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.stage.code)
    (fun i => ZFSet.pair (run.linked i).main.cutoff (run.linked i).serial.code)
    run.key_injective run.indices_ground run.stages_ground).2
  have cutoffs := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.cutoff) (fun i => (run.linked i).serial.code)
    run.key_injective run.indices_ground tails).1
  simpa only [cutoffFamily, run.linked_main] using cutoffs

theorem serialFieldFamily_ground (j : Fin 5) : run.serialFieldFamily j ∈ M.sets := by
  have tails := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.stage.code)
    (fun i => ZFSet.pair (run.linked i).main.cutoff (run.linked i).serial.code)
    run.key_injective run.indices_ground run.stages_ground).2
  have serialCodes := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.cutoff) (fun i => (run.linked i).serial.code)
    run.key_injective run.indices_ground tails).2
  have fieldCodes := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).serial.fields.code)
    (fun i => ZFSet.pair (run.linked i).serial.layerBound (run.linked i).serial.layers)
    run.key_injective run.indices_ground serialCodes).1
  exact M.familyCodeGraph_tuple_fields pairing unions powers separation run.key run.key_injective
    run.indices_ground 6 (fun i => (run.linked i).serial.fields.codeFields) fieldCodes j.succ.succ

theorem serialBirth_entry (i : I) :
    ZFSet.pair (run.diagram.stage i).cutoff (run.diagram.stage i).birth ∈
      (run.linked i).serial.fields.graph 3 := by
  have entry := (run.linked i).serial.fields.value_entry 3 (ZFSet.mem_insert _ _)
  rw [(run.linked i).terminal_values.2.2.2.1] at entry
  simpa only [run.linked_main] using entry

theorem birthFamily_ground : run.birthFamily ∈ M.sets := by
  apply M.familyCodeGraph_evaluation_ground pairing unions powers separation run.key
    (fun i => (run.diagram.stage i).cutoff) (fun i => (run.linked i).serial.fields.graph 3)
    (fun i => (run.diagram.stage i).birth) run.key_injective run.indices_ground
    run.cutoffFamily_ground (run.serialFieldFamily_ground 3)
  intro i y
  exact ⟨fun entry => ((run.linked i).serial.fields.graphFunction 3).unique entry (run.serialBirth_entry i),
    fun equal => equal.symm ▸ run.serialBirth_entry i⟩

theorem cutoffFamily_function : FunctionGraphOn run.indices run.cutoffFamily :=
  familyCodeGraph_function run.key _ run.key_injective

theorem serialFieldFamily_function (j : Fin 5) : FunctionGraphOn run.indices (run.serialFieldFamily j) :=
  familyCodeGraph_function run.key _ run.key_injective

theorem birthFamily_function : FunctionGraphOn run.indices run.birthFamily :=
  familyCodeGraph_function run.key _ run.key_injective

theorem cutoffFamily_entry (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.cutoffFamily ↔ z = (run.diagram.stage i).cutoff :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i z

theorem serialFieldFamily_entry (j : Fin 5) (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.serialFieldFamily j ↔ z = (run.linked i).serial.fields.graph j :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i z

theorem birthFamily_entry (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.birthFamily ↔ z = (run.diagram.stage i).birth :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i z





noncomputable def pointPresentation : CodedDirectPresentation run.pointSystem
    run.indices run.carrierUnion run.carrierFamily run.pointMapFamily where
  key := run.key
  key_injective := run.key_injective
  key_range := rfl
  key_order := run.key_order
  carrier_function := run.carrierFamily_function
  carrier_entry i := (run.carrierFamily_entry i _).2 rfl
  map_function := run.pointMapFamily_function
  map_entry before := (run.pointMapFamily_entry before _).2 rfl
  carrier_bound i := run.carrierFamily_subset_union ((run.carrierFamily_entry i _).2 rfl)

noncomputable def actorPresentation : CodedDirectPresentation run.actorSystem
    run.indices run.actorUnion run.actorFamily run.actorMapFamily where
  key := run.key
  key_injective := run.key_injective
  key_range := rfl
  key_order := run.key_order
  carrier_function := run.actorFamily_function
  carrier_entry i := (run.actorFamily_entry i _).2 rfl
  map_function := run.actorMapFamily_function
  map_entry before := (run.actorMapFamily_entry before _).2 rfl
  carrier_bound i := run.actorFamily_subset_union ((run.actorFamily_entry i _).2 rfl)





noncomputable def cutoffUnion : ZFSet.{u} := ⋃₀ ZFSet.range (fun i => (run.diagram.stage i).cutoff)

noncomputable def birthUnion : ZFSet.{u} := ⋃₀ ZFSet.range (fun i => (run.diagram.stage i).birth)

theorem cutoffValues_ground : ZFSet.range (fun i => (run.diagram.stage i).cutoff) ∈ M.sets :=
  M.familyCodeGraph_valueRange_mem unions separation run.key _ run.indices_ground run.cutoffFamily_ground

theorem birthValues_ground : ZFSet.range (fun i => (run.diagram.stage i).birth) ∈ M.sets :=
  M.familyCodeGraph_valueRange_mem unions separation run.key _ run.indices_ground run.birthFamily_ground

theorem cutoffUnion_ground : run.cutoffUnion ∈ M.sets := M.union_mem unions run.cutoffValues_ground

theorem birthUnion_ground : run.birthUnion ∈ M.sets := M.union_mem unions run.birthValues_ground

theorem cutoffUnion_mem (x : ZFSet.{u}) :
    x ∈ run.cutoffUnion ↔ ∃ i, x ∈ (run.diagram.stage i).cutoff :=
  familyCodeGraph_valueUnion_mem_iff _ x

theorem birthUnion_mem (x : ZFSet.{u}) :
    x ∈ run.birthUnion ↔ ∃ i, x ∈ (run.diagram.stage i).birth :=
  familyCodeGraph_valueUnion_mem_iff _ x

theorem cutoffFamily_subset_union {i X : ZFSet.{u}} (entry : ZFSet.pair i X ∈ run.cutoffFamily) :
    X ⊆ run.cutoffUnion := familyCodeGraph_value_subset_union run.key _ entry

theorem birthFamily_subset_union {i X : ZFSet.{u}} (entry : ZFSet.pair i X ∈ run.birthFamily) :
    X ⊆ run.birthUnion := familyCodeGraph_value_subset_union run.key _ entry

theorem cutoffFamily_rank_le_code : ZFSet.rank run.cutoffFamily ≤ ZFSet.rank run.code := by
  apply (familyCodeGraph_rank_mono run.key _ (fun i => (run.linked i).code) ?_).trans
    run.stageGraph_rank_le_code
  intro i
  simpa only [GroundLinkedMainStage.code, linkedMainStageCode, Fin.cases_zero, Fin.cases_succ,
    run.linked_main] using (rank_nonemptyTupleCode_field_le 2
      (Fin.cases (run.linked i).main.stage.code
        (Fin.cases (run.linked i).main.cutoff (fun _ => (run.linked i).serial.code))) (0 : Fin 2).succ)

theorem serialFieldFamily_rank_le_code (j : Fin 5) :
    ZFSet.rank (run.serialFieldFamily j) ≤ ZFSet.rank run.code := by
  apply (familyCodeGraph_rank_mono run.key _ (fun i => (run.linked i).code) ?_).trans
    run.stageGraph_rank_le_code
  intro i
  have serialBound : ZFSet.rank (run.linked i).serial.code ≤ ZFSet.rank (run.linked i).code := by
    simpa only [GroundLinkedMainStage.code, linkedMainStageCode, Fin.cases_zero, Fin.cases_succ] using
      (rank_nonemptyTupleCode_field_le 2 (Fin.cases (run.linked i).main.stage.code
        (Fin.cases (run.linked i).main.cutoff (fun _ => (run.linked i).serial.code))) (0 : Fin 1).succ.succ)
  exact ((run.linked i).serial.fieldGraph_rank_le_code j).trans serialBound

theorem birthFamily_rank_le_code : ZFSet.rank run.birthFamily ≤ ZFSet.rank run.code :=
  (familyCodeGraph_evaluation_rank_le run.key (fun i => (run.diagram.stage i).cutoff)
    (fun i => (run.linked i).serial.fields.graph 3) (fun i => (run.diagram.stage i).birth)
    run.serialBirth_entry).trans (run.serialFieldFamily_rank_le_code 3)

theorem cutoffValues_rank_le_code :
    ZFSet.rank (ZFSet.range (fun i => (run.diagram.stage i).cutoff)) ≤ ZFSet.rank run.code :=
  (familyCodeGraph_valueRange_rank_le run.key _).trans run.cutoffFamily_rank_le_code

theorem birthValues_rank_le_code :
    ZFSet.rank (ZFSet.range (fun i => (run.diagram.stage i).birth)) ≤ ZFSet.rank run.code :=
  (familyCodeGraph_valueRange_rank_le run.key _).trans run.birthFamily_rank_le_code

theorem cutoffUnion_rank_le_code : ZFSet.rank run.cutoffUnion ≤ ZFSet.rank run.code :=
  (ZFSet.rank_sUnion_le _).trans run.cutoffValues_rank_le_code

theorem birthUnion_rank_le_code : ZFSet.rank run.birthUnion ≤ ZFSet.rank run.code :=
  (ZFSet.rank_sUnion_le _).trans run.birthValues_rank_le_code

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def cutoffSuccessorFamily : ZFSet.{u} :=
  familyCodeGraph run.key (fun i => insert (run.diagram.stage i).cutoff (run.diagram.stage i).cutoff)

noncomputable def cutoffLimit : ZFSet.{u} :=
  ⋃₀ ZFSet.range (fun i => insert (run.diagram.stage i).cutoff (run.diagram.stage i).cutoff)

theorem cutoffSuccessorFamily_ground : run.cutoffSuccessorFamily ∈ M.sets := by
  have tails := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.stage.code)
    (fun i => ZFSet.pair (run.linked i).main.cutoff (run.linked i).serial.code)
    run.key_injective run.indices_ground run.stages_ground).2
  have serialCodes := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.cutoff) (fun i => (run.linked i).serial.code)
    run.key_injective run.indices_ground tails).2
  have fieldCodes := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).serial.fields.code)
    (fun i => ZFSet.pair (run.linked i).serial.layerBound (run.linked i).serial.layers)
    run.key_injective run.indices_ground serialCodes).1
  have times := M.familyCodeGraph_tuple_fields pairing unions powers separation run.key run.key_injective
    run.indices_ground 6 (fun i => (run.linked i).serial.fields.codeFields) fieldCodes 0
  simpa only [cutoffSuccessorFamily, GroundChronologyFields.codeFields, Fin.cases_zero,
    run.linked_main] using times

theorem cutoffSuccessorFamily_function : FunctionGraphOn run.indices run.cutoffSuccessorFamily :=
  familyCodeGraph_function run.key _ run.key_injective

theorem cutoffSuccessorFamily_entry (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.cutoffSuccessorFamily ↔
      z = insert (run.diagram.stage i).cutoff (run.diagram.stage i).cutoff :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i z

theorem cutoffSuccessorValues_ground :
    ZFSet.range (fun i => insert (run.diagram.stage i).cutoff (run.diagram.stage i).cutoff) ∈ M.sets :=
  M.familyCodeGraph_valueRange_mem unions separation run.key _ run.indices_ground run.cutoffSuccessorFamily_ground

theorem cutoffLimit_ground : run.cutoffLimit ∈ M.sets := M.union_mem unions run.cutoffSuccessorValues_ground

theorem cutoffLimit_mem (t : ZFSet.{u}) :
    t ∈ run.cutoffLimit ↔ ∃ i, t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff := by
  rw [cutoffLimit, familyCodeGraph_valueUnion_mem_iff]
  exact exists_congr (fun i => ZFSet.mem_insert_iff)

theorem cutoff_mem_cutoffLimit (i : I) : (run.diagram.stage i).cutoff ∈ run.cutoffLimit :=
  (run.cutoffLimit_mem _).2 ⟨i, Or.inl rfl⟩

theorem birth_time_mem_cutoffLimit (i : I) {x t : ZFSet.{u}}
    (entry : ZFSet.pair x t ∈ (run.diagram.stage i).birth) : t ∈ run.cutoffLimit :=
  (run.cutoffLimit_mem t).2 ⟨i, (run.diagram.stage i).birth_bound entry⟩

theorem cutoffLimit_ordinal : ordinalSetProperty run.cutoffLimit := by
  apply ordinalSetProperty_sUnion
  intro a ha
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 ha
  exact ordinalSetProperty_succ (run.diagram.stage i).cutoff_ordinal

theorem cutoffSuccessorFamily_rank_le_code :
    ZFSet.rank run.cutoffSuccessorFamily ≤ ZFSet.rank run.code := by
  apply (familyCodeGraph_rank_mono run.key _ (fun i => (run.linked i).code) ?_).trans
    run.stageGraph_rank_le_code
  intro i
  have serialBound : ZFSet.rank (run.linked i).serial.code ≤ ZFSet.rank (run.linked i).code := by
    simpa only [GroundLinkedMainStage.code, linkedMainStageCode, Fin.cases_zero, Fin.cases_succ] using
      (rank_nonemptyTupleCode_field_le 2 (Fin.cases (run.linked i).main.stage.code
        (Fin.cases (run.linked i).main.cutoff (fun _ => (run.linked i).serial.code))) (0 : Fin 1).succ.succ)
  simpa only [run.linked_main] using (run.linked i).serial.time_rank_le_code.trans serialBound

theorem cutoffLimit_rank_le_code : ZFSet.rank run.cutoffLimit ≤ ZFSet.rank run.code :=
  (familyCodeGraph_valueUnion_rank_le run.key _).trans run.cutoffSuccessorFamily_rank_le_code

theorem cutoffLimit_mem_inaccessible (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) : run.cutoffLimit ∈ K := by
  have family : ZFSet.IsFunc run.indices K run.cutoffFamily := by
    refine ⟨?_, run.cutoffFamily_function.to_isFunc.2⟩
    intro z hz
    obtain ⟨i, rfl⟩ := (mem_familyCodeGraph run.key (fun i => (run.diagram.stage i).cutoff) z).1 hz
    have cutoff : (run.diagram.stage i).cutoff ∈ K := by
      simpa only [run.linked_main] using (run.linked i).invariant.cutoff_mem
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, cutoff⟩
  obtain ⟨δ, hδ, bounded⟩ := (standard.2.2.1.regular standard.1.1).bound_small_domain
    pairing unions powers separation run.indices_ground hK run.cutoffFamily_ground indices family
  have ordinalδ := ordinalSetProperty_member standard.1.1 hδ
  have subset : run.cutoffLimit ⊆ δ := by
    intro t ht
    obtain ⟨i, before⟩ := (run.cutoffLimit_mem t).1 ht
    have cutoff := bounded (run.key i) (run.diagram.stage i).cutoff ((run.cutoffFamily_entry i _).2 rfl)
    rcases before with rfl | before
    · exact cutoff
    · exact ordinalδ.1 _ cutoff t before
  have coded : ordinalCode (ZFSet.rank run.cutoffLimit) ∈ ordinalCode (ZFSet.rank K) :=
    (mem_ordinalCode_iff _ _).2 ((ZFSet.rank_mono subset).trans_lt (ZFSet.rank_lt_of_mem hδ))
  exact (congrArg₂ (fun a b : ZFSet.{u} => a ∈ b)
    (ordinalSetProperty_eq_code_rank run.cutoffLimit run.cutoffLimit_ordinal)
    (ordinalSetProperty_eq_code_rank K standard.1.1)).mpr coded

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing
universe u v

def mainPrefixLimitTargetFields {A : Type v} (w : Fin 32 → A) : Fin 24 → A :=
  fun j => w (Fin.natAdd 8 j)

def MainPrefixLimitStepRawCode (M : TransitiveGround.{u})
    (K Labels C D rD N old next : ZFSet.{u}) (w : Fin 32 → ZFSet.{u}) : Prop :=
  let v := mainPrefixLimitTargetFields w
  w 7 = insert (w 0) (w 0) ∧
  old = mainPrefixCode (w 0) (w 1) (w 2) ∧
  next = mainPrefixCode (w 7) (w 3) (w 4) ∧
  MainPrefixExtends old next ∧
  ZFSet.pair (w 0) (w 5) ∈ w 3 ∧
  LinkedMainStageRawCode M K Labels C D rD N (w 5) v ∧
  ZFSet.pair (v 11) (w 6) ∈ v 17 ∧
  MainLimitCoverageGraphCode (w 0) (w 1) (w 4) (v 0) (v 3) (v 1) (v 9) (v 11) (w 6)

def MainPrefixLimitStepCode (M : TransitiveGround.{u})
    (K Labels C D rD N old next : ZFSet.{u}) : Prop :=
  ∃ w : Fin 32 → ZFSet.{u}, (∀ j, w j ∈ M.sets) ∧
    MainPrefixLimitStepRawCode M K Labels C D rD N old next w

namespace MainPrefixLimitStepCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N old next : ZFSet.{u}}
variable (code : MainPrefixLimitStepCode M K Labels C D rD N old next)
include code

theorem extension : MainPrefixExtends old next := by
  obtain ⟨w, _, raw⟩ := code
  exact raw.2.2.2.1

theorem indices_successor {T S E T' S' E' : ZFSet.{u}}
    (oldCode : old = mainPrefixCode T S E) (nextCode : next = mainPrefixCode T' S' E') :
    T' = insert T T := by
  obtain ⟨w, _, raw⟩ := code
  have oldFields := mainPrefixCode_inj.1 (oldCode.symm.trans raw.2.1)
  have nextFields := mainPrefixCode_inj.1 (nextCode.symm.trans raw.2.2.1)
  rw [nextFields.1, raw.1, ← oldFields.1]

theorem next_fields {T S E : ZFSet.{u}} (oldCode : old = mainPrefixCode T S E) :
    ∃ S' E', next = mainPrefixCode (insert T T) S' E' := by
  obtain ⟨w, _, raw⟩ := code
  have fields := mainPrefixCode_inj.1 (oldCode.symm.trans raw.2.1)
  refine ⟨w 3, w 4, ?_⟩
  rw [raw.2.2.1, raw.1, ← fields.1]

end MainPrefixLimitStepCode

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

theorem rawFields_birth_entry :
    ZFSet.pair (linked.rawFields 11) linked.main.birth ∈ linked.rawFields 17 := by
  change ZFSet.pair linked.main.cutoff linked.main.birth ∈ linked.serial.fields.graph 3
  rw [← linked.terminal_values.2.2.2.1]
  exact linked.serial.fields.value_entry 3 (ZFSet.mem_insert _ _)

end GroundLinkedMainStage

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable {target : GroundChronologicalMainStage M C D rD} (cone : run.diagram.Cone target)
variable {row : ZFSet.{u}}
variable (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
  z = (cone.leg i).map.code)

include entries

theorem limitConeEntry_iff (i : I) {P G cutoff points actors : ZFSet.{u}} :
    MainLimitConeEntryCode run.indices run.stageGraph row (run.key i) P G cutoff points actors ↔
      P = (run.diagram.stage i).stage.carrier ∧ G = (run.diagram.stage i).stage.actors ∧
      cutoff = (run.diagram.stage i).cutoff ∧ points = (cone.leg i).map.points ∧
      actors = (cone.leg i).map.actors := by
  have fields : LinkedCoverageFieldsCode (run.linked i).code P G cutoff ↔
      P = (run.diagram.stage i).stage.carrier ∧ G = (run.diagram.stage i).stage.actors ∧
      cutoff = (run.diagram.stage i).cutoff := by
    rw [(run.linked i).coverageFields_iff, run.linked_main]
  constructor
  · rintro ⟨_, z, stageEntry, shape, mapEntry⟩
    rw [(run.stageGraph_entry i z).1 stageEntry] at shape
    obtain ⟨hp, hg, ht⟩ := fields.1 shape
    have maps := ZFSet.pair_inj.1 ((entries i _).1 mapEntry)
    exact ⟨hp, hg, ht, maps.1, maps.2⟩
  · rintro ⟨hp, hg, ht, rfl, rfl⟩
    exact ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, (run.linked i).code,
      (run.stageGraph_entry i _).2 rfl, fields.2 ⟨hp, hg, ht⟩, (entries i _).2 rfl⟩

theorem limitOldPointImage_iff (x : ZFSet.{u}) :
    MainLimitOldPointImageCode run.indices run.stageGraph row x ↔
      ∃ i y, y ∈ (run.diagram.stage i).stage.carrier ∧
        ZFSet.pair y x ∈ (cone.leg i).map.points := by
  constructor
  · rintro ⟨key, P, G, cutoff, points, actors, y, entry, hy, image⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 entry.1
    obtain ⟨rfl, _, _, rfl, _⟩ := (run.limitConeEntry_iff cone entries i).1 entry
    exact ⟨i, y, hy, image⟩
  · rintro ⟨i, y, hy, image⟩
    exact ⟨run.key i, _, _, _, _, _, y,
      (run.limitConeEntry_iff cone entries i).2 ⟨rfl, rfl, rfl, rfl, rfl⟩, hy, image⟩

theorem limitOldActorImage_iff (g : ZFSet.{u}) :
    MainLimitOldActorImageCode run.indices run.stageGraph row g ↔
      ∃ i h, h ∈ (run.diagram.stage i).stage.actors ∧
        ZFSet.pair h g ∈ (cone.leg i).map.actors := by
  constructor
  · rintro ⟨key, P, G, cutoff, points, actors, h, entry, hh, image⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 entry.1
    obtain ⟨_, rfl, _, _, rfl⟩ := (run.limitConeEntry_iff cone entries i).1 entry
    exact ⟨i, h, hh, image⟩
  · rintro ⟨i, h, hh, image⟩
    exact ⟨run.key i, _, _, _, _, _, h,
      (run.limitConeEntry_iff cone entries i).2 ⟨rfl, rfl, rfl, rfl, rfl⟩, hh, image⟩

omit entries in
theorem limitOldCutoff_iff (t : ZFSet.{u}) :
    MainLimitOldCutoffCode run.indices run.stageGraph t ↔ t ∈ run.cutoffLimit := by
  rw [run.cutoffLimit_mem]
  constructor
  · rintro ⟨key, member, z, entry, P, G, cutoff, shape, bound⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 member
    rw [(run.stageGraph_entry i z).1 entry, (run.linked i).coverageFields_iff,
      run.linked_main] at shape
    exact ⟨i, shape.2.2 ▸ bound⟩
  · rintro ⟨i, bound⟩
    refine ⟨run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩, (run.linked i).code,
      (run.stageGraph_entry i _).2 rfl, (run.diagram.stage i).stage.carrier,
      (run.diagram.stage i).stage.actors, (run.diagram.stage i).cutoff, ?_, bound⟩
    rw [(run.linked i).coverageFields_iff, run.linked_main]
    exact ⟨rfl, rfl, rfl⟩

theorem limitCoverage_graph_iff :
    MainLimitCoverageGraphCode run.indices run.stageGraph row target.stage.carrier
      target.stage.actors target.stage.order target.stage.top target.cutoff target.birth ↔
    run.LimitCoverage target cone := by
  constructor
  · intro raw
    refine ⟨fun x => (raw.points x).trans (run.limitOldPointImage_iff cone entries x),
      fun g => (raw.actors g).trans (run.limitOldActorImage_iff cone entries g), ?_, ?_, raw.top_birth⟩
    · intro i x y entry
      exact raw.strict_top _ _ _ _ _ _
        ((run.limitConeEntry_iff cone entries i).2 ⟨rfl, rfl, rfl, rfl, rfl⟩) x y entry
    · exact ZFSet.ext (fun t => (raw.cutoff_mem t).trans (run.limitOldCutoff_iff t))
  · intro coverage
    refine ⟨fun x => (coverage.points x).trans (run.limitOldPointImage_iff cone entries x).symm,
      fun g => (coverage.actors g).trans (run.limitOldActorImage_iff cone entries g).symm,
      ?_, ?_, coverage.top_birth⟩
    · intro key P G t points actors entry x y image
      obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 entry.1
      obtain ⟨_, _, _, rfl, _⟩ := (run.limitConeEntry_iff cone entries i).1 entry
      exact coverage.strict_top i x y image
    · intro t
      rw [coverage.cutoff]
      exact (run.limitOldCutoff_iff t).symm

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
