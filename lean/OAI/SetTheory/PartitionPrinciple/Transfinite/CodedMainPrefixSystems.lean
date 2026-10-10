import OAI.SetTheory.PartitionPrinciple.Definability.GroundExternalCutoffFieldGraphs
import OAI.SetTheory.PartitionPrinciple.Definability.GroundLowRankFunctionGraphs
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSerializedCodeRanks
import OAI.SetTheory.PartitionPrinciple.Definability.LinkedMainInvariantCodes
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionFiniteFieldGraphs
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundInitialSeedSerializationRanks
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainStageCandidates

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundChronologicalHistory
noncomputable def fieldValue {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
    (prior : GroundChronologicalHistory M T C D rD) : Fin 5 → ZFSet.{u} → ZFSet.{u} :=
  Fin.cases prior.space (Fin.cases prior.order (Fin.cases prior.meetGraph
    (Fin.cases prior.birth (fun _ => prior.height))))

end GroundChronologicalHistory

namespace CompressionChronologyFields
noncomputable def fieldValue (fields : CompressionChronologyFields.{u}) : Fin 5 → ZFSet.{u} → ZFSet.{u} :=
  Fin.cases fields.space (Fin.cases fields.order (Fin.cases fields.meetGraph
    (Fin.cases fields.birth (fun _ => fields.height))))

end CompressionChronologyFields

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (priorFields : GroundChronologyFields M T0)

noncomputable def chronologyGraph (j : Fin 5) : ZFSet.{u} :=
  compressionPrefixGraph oldTimes births.limit (priorFields.graph j)
    (births.cutoffFieldFamily heights j) births.stamps (births.terminalField heights j)

variable {inv : ZFSet.{u}}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (ordinal : ordinalSetProperty T0) (hOld : oldTimes ∈ T0)
include data group action pairing unions powers separation infinite hG hP0

theorem chronologyGraph_ground (j : Fin 5) : births.chronologyGraph heights priorFields j ∈ M.sets :=
  M.compressionPrefixGraph_mem pairing unions powers separation
    (M.omega_mem separation infinite)
    (M.transitive births.limit_ground births.times.base_mem_limit) births.limit_ground
    (priorFields.graph_ground j)
    (births.cutoffFieldFamily_spec heights data group action pairing unions powers separation infinite hG hP0 j).1
    births.stamps_ground
    (births.terminalField_ground heights data group action pairing unions powers separation infinite hG hP0 j)

include ordinal hOld in
theorem chronologyGraph_function (j : Fin 5) :
    FunctionGraphOn (insert births.limit births.limit) (births.chronologyGraph heights priorFields j) := by
  apply compressionPrefixGraph_function births.times (priorFields.value j) (births.cutoffField heights j)
  · intro s before y
    have hs : s ∈ T0 := before.elim (fun h => ordinal.1 oldTimes hOld s h) (fun h => h.symm ▸ hOld)
    exact ⟨fun entry => (priorFields.value_eq_of_entry j entry).symm,
      fun equal => equal.symm ▸ priorFields.value_entry j hs⟩
  · exact (births.cutoffFieldFamily_spec heights data group action pairing unions powers separation infinite hG hP0 j).2.2

noncomputable def groundChronologyFields : GroundChronologyFields M (insert births.limit births.limit) :=
  GroundChronologyFields.ofGraphs pairing unions (M.insert_mem pairing unions births.limit_ground births.limit_ground)
    (births.chronologyGraph heights priorFields)
    (births.chronologyGraph_ground heights priorFields data group action pairing unions powers separation infinite hG hP0)
    (births.chronologyGraph_function heights priorFields data group action pairing unions powers separation infinite hG hP0 ordinal hOld)

theorem groundChronologyFields_graph :
    (births.groundChronologyFields heights priorFields data group action pairing unions powers separation infinite hG hP0 ordinal hOld).graph =
      births.chronologyGraph heights priorFields := rfl

include ordinal hOld in
theorem groundChronologyFields_values (prior : GroundChronologicalHistory M T0 C D rD)
    (agreement : ∀ j s, s ∈ T0 → priorFields.value j s = prior.fieldValue j s)
    (j : Fin 5) {s : ZFSet.{u}} (hs : s ∈ insert births.limit births.limit) :
    (births.groundChronologyFields heights priorFields data group action pairing unions powers separation infinite hG hP0 ordinal hOld).value j s =
      (births.chronologyFields heights prior).fieldValue j s := by
  have field : (births.chronologyFields heights prior).fieldValue j =
      compressionPrefixValue oldTimes births.limit (prior.fieldValue j)
        (births.cutoffField heights j) (births.terminalField heights j) :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) j
  have oldEntries : ∀ t, t ∈ oldTimes ∨ t = oldTimes → ∀ y,
      ZFSet.pair t y ∈ priorFields.graph j ↔ y = prior.fieldValue j t := by
    intro t before y
    have ht : t ∈ T0 := before.elim (fun h => ordinal.1 oldTimes hOld t h) (fun h => h.symm ▸ hOld)
    constructor
    · intro entry
      exact (priorFields.value_eq_of_entry j entry).symm.trans (agreement j t ht)
    · intro equal
      rw [← agreement j t ht] at equal
      exact equal.symm ▸ priorFields.value_entry j ht
  apply GroundChronologyFields.value_eq_of_entry
  change ZFSet.pair s ((births.chronologyFields heights prior).fieldValue j s) ∈
    compressionPrefixGraph oldTimes births.limit (priorFields.graph j)
      (births.cutoffFieldFamily heights j) births.stamps (births.terminalField heights j)
  exact (compressionPrefixGraph_exact births.times (prior.fieldValue j) (births.cutoffField heights j)
    oldEntries (births.cutoffFieldFamily_spec heights data group action pairing unions powers separation infinite hG hP0 j).2.2 s _).2
      ⟨hs,congrFun field s⟩

include ordinal hOld in
theorem groundChronologyFields_code_ground :
    (births.groundChronologyFields heights priorFields data group action pairing unions powers separation infinite hG hP0 ordinal hOld).code ∈ M.sets :=
  GroundChronologyFields.code_ground _ pairing

end GroundExternalBirthData




namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T U cutoff : ZFSet.{u}}

theorem graphPrefixCode_iff_values (source : GroundChronologyFields M T)
    (target : GroundChronologyFields M U)
    (domains : ∀ s, s = cutoff ∨ s ∈ cutoff → s ∈ T ∧ s ∈ U) :
    ChronologyGraphPrefixCode cutoff source.graph target.graph ↔
      ∀ j s, s = cutoff ∨ s ∈ cutoff → source.value j s = target.value j s := by
  constructor
  · intro code j s before
    exact (target.value_eq_of_entry j
      ((code j s before _).1 (source.value_entry j (domains s before).1))).symm
  · intro values j s before x
    constructor
    · intro entry
      have equal := (values j s before).symm.trans (source.value_eq_of_entry j entry)
      exact equal ▸ target.value_entry j (domains s before).2
    · intro entry
      have equal := (values j s before).trans (target.value_eq_of_entry j entry)
      exact equal ▸ source.value_entry j (domains s before).1

end GroundChronologyFields

namespace GroundChronologicalMainTransition
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target : GroundChronologicalMainStage M C D rD}
variable (sourceFields : GroundChronologyFields M (insert source.cutoff source.cutoff))
variable (targetFields : GroundChronologyFields M (insert target.cutoff target.cutoff))
variable (sourceAgreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
  sourceFields.value j s = source.history.fieldValue j s)
variable (targetAgreement : ∀ j s, s ∈ insert target.cutoff target.cutoff →
  targetFields.value j s = target.history.fieldValue j s)

include sourceAgreement targetAgreement

theorem field_laws (transition : GroundChronologicalMainTransition source target) :
    ChronologicalTransitionLaws transition.map.points source.cutoff target.cutoff source.birth target.birth
      sourceFields.graph targetFields.graph := by
  refine ⟨transition.cutoff_le, transition.birth, ?_⟩
  apply (sourceFields.graphPrefixCode_iff_values targetFields (fun s before =>
    ⟨ZFSet.mem_insert_iff.2 before, ZFSet.mem_insert_iff.2 (transition.prefix_bound before)⟩)).2
  intro j s before
  rw [sourceAgreement j s (ZFSet.mem_insert_iff.2 before),
    targetAgreement j s (ZFSet.mem_insert_iff.2 (transition.prefix_bound before))]
  have h := transition.history_prefix s before
  exact Fin.cases h.1.symm (Fin.cases h.2.1.symm (Fin.cases h.2.2.1.symm
    (Fin.cases h.2.2.2.1.symm (Fin.cases h.2.2.2.2.symm (fun i => Fin.elim0 i))))) j

def ofFieldLaws (map : GroundMainTransition source.stage target.stage)
    (valid : ChronologicalTransitionLaws map.points source.cutoff target.cutoff source.birth target.birth
      sourceFields.graph targetFields.graph) : GroundChronologicalMainTransition source target where
  map := map
  cutoff_le := valid.cutoff_le
  birth := valid.birth
  history_prefix := by
    intro s before
    have bound : s = target.cutoff ∨ s ∈ target.cutoff := by
      rcases valid.cutoff_le with equal | lower
      · exact equal ▸ before
      · exact Or.inr (before.elim (fun equal => equal.symm ▸ lower)
          (fun hs => target.cutoff_ordinal.1 source.cutoff lower s hs))
    have values := (sourceFields.graphPrefixCode_iff_values targetFields (fun a earlier => by
      refine ⟨ZFSet.mem_insert_iff.2 earlier, ZFSet.mem_insert_iff.2 ?_⟩
      rcases valid.cutoff_le with equal | lower
      · exact equal ▸ earlier
      · exact Or.inr (earlier.elim (fun equal => equal.symm ▸ lower)
          (fun ha => target.cutoff_ordinal.1 source.cutoff lower a ha)))).1 valid.history_prefix
    have same (j : Fin 5) : target.history.fieldValue j s = source.history.fieldValue j s := by
      rw [← sourceAgreement j s (ZFSet.mem_insert_iff.2 before),
        ← targetAgreement j s (ZFSet.mem_insert_iff.2 bound)]
      exact (values j s before).symm
    exact ⟨same 0, same 1, same 2, same 3, same 4⟩

theorem ofFieldLaws_map (map : GroundMainTransition source.stage target.stage)
    (valid : ChronologicalTransitionLaws map.points source.cutoff target.cutoff source.birth target.birth
      sourceFields.graph targetFields.graph) :
    (ofFieldLaws sourceFields targetFields sourceAgreement targetAgreement map valid).map = map := rfl

theorem ofFieldLaws_self (transition : GroundChronologicalMainTransition source target) :
    ofFieldLaws sourceFields targetFields sourceAgreement targetAgreement transition.map
      (field_laws sourceFields targetFields sourceAgreement targetAgreement transition) = transition :=
  ext rfl

end GroundChronologicalMainTransition
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}

theorem GroundChronologicalHistory.fieldValue_rank_lt
    (history : GroundChronologicalHistory M T C D rD)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (times : ZFSet.rank T < o) (columns : ZFSet.rank C < o)
    (coordinates : ZFSet.rank D < o) {s : ZFSet.{u}} (hs : s ∈ T)
    (points : ZFSet.rank (history.space s) < o) (j : Fin 5) :
    ZFSet.rank (history.fieldValue j s) < o := by
  have meet := history.meet_order s hs
  have pp := rank_product_lt limit points points
  have order := (ZFSet.rank_mono meet.order.relation).trans_lt pp
  have operation := rank_functionGraph_lt limit meet.operation pp points
  have birth := rank_functionGraph_lt limit (history.birth_function s hs) points times
  have height := rank_functionGraph_lt limit (history.strict_height s hs).function points
    (rank_product_lt limit columns coordinates)
  exact Fin.cases points (Fin.cases order (Fin.cases operation
    (Fin.cases birth (Fin.cases height (fun i => Fin.elim0 i))))) j

namespace GroundChronologyFields
variable (fields : GroundChronologyFields M T)

theorem graph_rank_lt_of_history
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (hT : T ∈ K) (history : GroundChronologicalHistory M T C D rD)
    (agreement : ∀ j s, s ∈ T → fields.value j s = history.fieldValue j s)
    (points : ∀ s ∈ T, ZFSet.rank (history.space s) < ZFSet.rank K)
    (columns : ZFSet.rank C < ZFSet.rank K) (coordinates : ZFSet.rank D < ZFSet.rank K)
    (j : Fin 5) : ZFSet.rank (fields.graph j) < ZFSet.rank K := by
  apply conditions.functionGraphOn_rank_lt pairing unions powers separation collection infinite hK
    hT (fields.graph_ground j) ⟨fields.bound, fields.function j⟩
  intro s hs v entry
  rw [← fields.value_eq_of_entry j entry, agreement j s hs]
  exact history.fieldValue_rank_lt
    (conditions.rank_isLimit pairing unions powers separation infinite hK)
    (ZFSet.rank_lt_of_mem hT) columns coordinates hs (points s hs) j

end GroundChronologyFields

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)
variable (priorFields : GroundChronologyFields M T0)
variable (prior : GroundChronologicalHistory M T0 C Q qlt)

noncomputable def prefixGraph (finiteGraphs : Fin 5 → ZFSet.{u}) (j : Fin 5) : ZFSet.{u} :=
  compressionPrefixGraph base births.limit (priorFields.graph j) (finiteGraphs j) births.stamps
    (state.prefixTerminalField data births heights j)

theorem prefixGraph_exact
    (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
    (agreement : ∀ j s, s ∈ T0 → priorFields.value j s = prior.fieldValue j s)
    {finiteGraphs : Fin 5 → ZFSet.{u}}
    (finiteEntries : ∀ j n y, ZFSet.pair (natSetCode n) y ∈ finiteGraphs j ↔
      y = state.prefixFiniteField data births heights j n)
    (j : Fin 5) (s y : ZFSet.{u}) :
    ZFSet.pair s y ∈ state.prefixGraph data births heights priorFields finiteGraphs j ↔
      s ∈ insert births.limit births.limit ∧
        y = (state.prefixFields data births heights prior).fieldValue j s := by
  have field : (state.prefixFields data births heights prior).fieldValue j =
      compressionPrefixValue base births.limit (prior.fieldValue j)
        (state.prefixFiniteField data births heights j) (state.prefixTerminalField data births heights j) :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) j
  rw [field]
  apply compressionPrefixGraph_exact births.times
  · intro t before z
    have ht : t ∈ T0 := before.elim (fun h => ordinal.1 base hBase t h) (fun h => h.symm ▸ hBase)
    constructor
    · intro entry
      exact (priorFields.value_eq_of_entry j entry).symm.trans (agreement j t ht)
    · intro equal
      rw [← agreement j t ht] at equal
      exact equal.symm ▸ priorFields.value_entry j ht
  · exact finiteEntries j

theorem exists_groundPrefixFields
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
    (agreement : ∀ j s, s ∈ T0 → priorFields.value j s = prior.fieldValue j s) :
    ∃ fields : GroundChronologyFields M (insert births.limit births.limit),
      fields.code ∈ M.sets ∧ ChronologyCoreCode (insert births.limit births.limit)
        fields.bound C Q qlt fields.graph ∧
      ∀ j s, s ∈ insert births.limit births.limit →
        fields.value j s = (state.prefixFields data births heights prior).fieldValue j s := by
  obtain ⟨finiteGraphs, finiteGround, _, finiteEntries⟩ := state.exists_prefixFiniteGraphs data births heights
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  let graphs := state.prefixGraph data births heights priorFields finiteGraphs
  have ground : ∀ j, graphs j ∈ M.sets := by
    intro j
    exact M.compressionPrefixGraph_mem pairing unions powers separation (M.omega_mem separation infinite)
      (M.transitive births.limit_ground births.times.base_mem_limit) births.limit_ground
      (priorFields.graph_ground j) (finiteGround j) births.stamps_ground
      (state.prefixTerminalField_ground data births heights j)
  have functions : ∀ j, FunctionGraphOn (insert births.limit births.limit) (graphs j) := by
    intro j
    apply compressionPrefixGraph_function births.times (priorFields.value j)
      (state.prefixFiniteField data births heights j)
    · intro s before y
      have hs : s ∈ T0 := before.elim (fun h => ordinal.1 base hBase s h) (fun h => h.symm ▸ hBase)
      exact ⟨fun entry => (priorFields.value_eq_of_entry j entry).symm,
        fun equal => equal.symm ▸ priorFields.value_entry j hs⟩
    · exact finiteEntries j
  let fields := GroundChronologyFields.ofGraphs pairing unions
    (M.insert_mem pairing unions births.limit_ground births.limit_ground) graphs ground functions
  have values : ∀ j s, s ∈ insert births.limit births.limit →
      fields.value j s = (state.prefixFields data births heights prior).fieldValue j s := by
    intro j s hs
    apply fields.value_eq_of_entry
    exact (state.prefixGraph_exact data births heights priorFields prior ordinal hBase agreement
      finiteEntries j s _).2 ⟨hs, rfl⟩
  refine ⟨fields, fields.code_ground pairing, ⟨fields.function, ?_⟩, values⟩
  intro s hs L r μ birth height eL er eμ eb eh
  have eqL := (fields.value_eq_of_entry 0 eL).symm.trans (values 0 s hs)
  have eqr := (fields.value_eq_of_entry 1 er).symm.trans (values 1 s hs)
  have eqμ := (fields.value_eq_of_entry 2 eμ).symm.trans (values 2 s hs)
  have eqb := (fields.value_eq_of_entry 3 eb).symm.trans (values 3 s hs)
  have eqh := (fields.value_eq_of_entry 4 eh).symm.trans (values 4 s hs)
  rw [eqL, eqr, eqμ, eqb, eqh]
  have laws := state.prefixFields_stage_laws data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs
  exact ⟨laws.1, laws.2.1, laws.2.2.1, laws.2.2.2.1, laws.2.2.2.2⟩

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def linkedMainStageCode (stage cutoff serial : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 2 (Fin.cases stage (Fin.cases cutoff (fun _ => serial)))

theorem linkedMainStageCode_inj {a t h a' t' h' : ZFSet.{u}} :
    linkedMainStageCode a t h = linkedMainStageCode a' t' h' ↔ a = a' ∧ t = t' ∧ h = h' := by
  constructor
  · intro equal
    have fields := nonemptyTupleCode_injective 2 equal
    exact ⟨congrFun fields 0, congrFun fields 1, congrFun fields 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

structure GroundLinkedMainStage (M : TransitiveGround.{u}) (K Labels C D rD : ZFSet.{u}) where
  main : GroundChronologicalMainStage M C D rD
  serial : GroundSerializedChronology M (insert main.cutoff main.cutoff) C D rD
  agreement : ∀ j s, s ∈ insert main.cutoff main.cutoff →
    serial.fields.value j s = main.history.fieldValue j s
  invariant : main.Invariant K Labels
  serial_rank : ZFSet.rank serial.code < ZFSet.rank K

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

noncomputable def code : ZFSet.{u} :=
  linkedMainStageCode linked.main.stage.code linked.main.cutoff linked.serial.code

theorem code_ground (pairing : Realize M.sets SetFormula.pairing Fin.elim0) : linked.code ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 2 _ (Fin.cases (linked.main.stage.code_mem pairing)
    (Fin.cases linked.main.cutoff_ground (fun _ => linked.serial.code_ground pairing)))

theorem terminal_values :
    linked.serial.fields.value 0 linked.main.cutoff = linked.main.stage.carrier ∧
    linked.serial.fields.value 1 linked.main.cutoff = linked.main.stage.order ∧
    linked.serial.fields.value 2 linked.main.cutoff = linked.main.stage.meetGraph ∧
    linked.serial.fields.value 3 linked.main.cutoff = linked.main.birth ∧
    linked.serial.fields.value 4 linked.main.cutoff = linked.main.stage.height :=
  ⟨(linked.agreement 0 _ (ZFSet.mem_insert _ _)).trans linked.main.carrier_eq,
    (linked.agreement 1 _ (ZFSet.mem_insert _ _)).trans linked.main.order_eq,
    (linked.agreement 2 _ (ZFSet.mem_insert _ _)).trans linked.main.meet_eq,
    linked.agreement 3 _ (ZFSet.mem_insert _ _),
    (linked.agreement 4 _ (ZFSet.mem_insert _ _)).trans linked.main.height_eq⟩

theorem invariant_code : LinkedMainInvariantCode M K Labels C D linked.main.stage.carrier
    linked.main.stage.actors linked.main.cutoff linked.serial.code :=
  ⟨linked.invariant.points_small, linked.invariant.actors_small, linked.invariant.labels_small,
    linked.invariant.points_rank, linked.invariant.actors_rank, linked.invariant.labels_rank,
    linked.invariant.cutoff_mem, linked.invariant.columns_rank, linked.invariant.coordinates_rank,
    linked.serial_rank⟩

theorem code_rank_lt
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K) : ZFSet.rank linked.code < ZFSet.rank K :=
  rank_nonemptyTupleCode_lt (conditions.rank_isLimit pairing unions powers separation infinite hK) 2 _
    (Fin.cases (linked.invariant.code_rank_lt pairing unions powers separation infinite hK conditions)
      (Fin.cases (ZFSet.rank_lt_of_mem linked.invariant.cutoff_mem) (fun _ => linked.serial_rank)))

end GroundLinkedMainStage

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u v

structure GroundMainPrefix (M : TransitiveGround.{u}) (K Labels C D rD : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (I : Type v) [Small.{u} I] [Preorder I] where
  key : I → ZFSet.{u}
  key_injective : Function.Injective key
  key_order : ∀ i j, i ≤ j ↔ key i = key j ∨ key i ∈ key j
  indices_ground : ZFSet.range key ∈ M.sets
  indices_ordinal : ordinalSetProperty (ZFSet.range key)
  diagram : GroundChronologicalMainDiagram M C D rD pairing unions powers separation I
  linked : I → GroundLinkedMainStage M K Labels C D rD
  linked_main : ∀ i, (linked i).main = diagram.stage i
  coverage : diagram.CoversOldBirths
  stages_ground : familyCodeGraph key (fun i => (linked i).code) ∈ M.sets
  transitions_ground : familyCodeGraph (mainTransitionIndexKey key)
    (fun p => (diagram.transition p.property).map.code) ∈ M.sets

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def indices : ZFSet.{u} := ZFSet.range run.key

noncomputable def stageGraph : ZFSet.{u} := familyCodeGraph run.key (fun i => (run.linked i).code)

noncomputable def transitionGraph : ZFSet.{u} := familyCodeGraph (mainTransitionIndexKey run.key)
  (fun p => (run.diagram.transition p.property).map.code)

noncomputable def code : ZFSet.{u} := nonemptyTupleCode 2
  (Fin.cases run.indices (Fin.cases run.stageGraph (fun _ => run.transitionGraph)))

theorem code_ground : run.code ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 2 _ (Fin.cases run.indices_ground
    (Fin.cases run.stages_ground (fun _ => run.transitions_ground)))

theorem stageGraph_function : FunctionGraphOn run.indices run.stageGraph :=
  familyCodeGraph_function run.key _ run.key_injective

theorem transitionGraph_function : FunctionGraphOn (chronologyPairs run.indices) run.transitionGraph := by
  have function := familyCodeGraph_function (mainTransitionIndexKey run.key)
    (fun p => (run.diagram.transition p.property).map.code)
    (mainTransitionIndexKey_injective run.key run.key_injective)
  rw [mainTransitionIndex_range run.key run.key_order] at function
  exact function

theorem stageGraph_entry (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.stageGraph ↔ z = (run.linked i).code :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i z

theorem transitionGraph_entry {i j : I} (before : i ≤ j) (z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (run.key j) (run.key i)) z ∈ run.transitionGraph ↔
      z = (run.diagram.transition before).map.code :=
  pair_mem_familyCodeGraph (mainTransitionIndexKey run.key) _
    (mainTransitionIndexKey_injective run.key run.key_injective) ⟨(i, j), before⟩ z

theorem identity_entry (i : I) :
    ZFSet.pair (ZFSet.pair (run.key i) (run.key i))
      (GroundChronologicalMainTransition.identity pairing unions powers separation (run.diagram.stage i)).map.code ∈
        run.transitionGraph := by
  rw [run.transitionGraph_entry (le_refl i), run.diagram.self]

theorem composition_entry {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    ZFSet.pair (ZFSet.pair (run.key k) (run.key i))
      ((run.diagram.transition hij).comp pairing unions powers separation
        (run.diagram.transition hjk)).map.code ∈ run.transitionGraph := by
  rw [run.transitionGraph_entry (le_trans hij hjk), run.diagram.comp hij hjk]

end GroundMainPrefix

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundInitialMainSeedData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K C : ZFSet.{u}}
variable (seed : GroundInitialMainSeedData M K C)

theorem initialSerialization_agreement
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {injection : ZFSet.{u}} (hInjection : injection ∈ M.sets)
    (injected : InjectionCode seed.source.stage.carrier ZFSet.omega injection) :
    let serial := seed.source.stage.initialSerializedChronology pairing unions powers separation hInjection injected
    ∀ j t, t ∈ (insert (∅ : ZFSet.{u}) ∅ : ZFSet.{u}) →
      serial.fields.value j t = seed.source.history.fieldValue j t := by
  dsimp only
  intro j t ht
  have zero : t = ∅ := by
    simpa only [ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false] using ht
  subst t
  have values := seed.source.stage.initialSerializedChronology_values pairing unions powers separation
    hInjection injected (ZFSet.mem_insert (∅ : ZFSet.{u}) ∅)
  have carrier := (congrArg seed.source.history.space seed.cutoff_zero).symm.trans seed.source.carrier_eq
  have order := (congrArg seed.source.history.order seed.cutoff_zero).symm.trans seed.source.order_eq
  have meet := (congrArg seed.source.history.meetGraph seed.cutoff_zero).symm.trans seed.source.meet_eq
  have height := (congrArg seed.source.history.height seed.cutoff_zero).symm.trans seed.source.height_eq
  have birth : seed.source.stage.initialBirth = seed.source.history.birth ∅ := by
    have equal : seed.source.stage.initialBirth = seed.source.birth := by
      rw [GroundMainStage.initialBirth, seed.points_eq, seed.birth_eq]
    exact equal.trans (congrArg seed.source.history.birth seed.cutoff_zero)
  exact Fin.cases (values.1.trans carrier.symm)
    (Fin.cases (values.2.1.trans order.symm)
      (Fin.cases (values.2.2.1.trans meet.symm)
        (Fin.cases (values.2.2.2.1.trans birth)
          (Fin.cases (values.2.2.2.2.trans height.symm) (fun i => Fin.elim0 i))))) j

end PartitionPilot.Forcing.GroundInitialMainSeedData



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u v
namespace GroundChronologicalMainDiagram
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Preorder I]
variable (diagram : GroundChronologicalMainDiagram M C D rD pairing unions powers separation I)

noncomputable def pointSystem (upper : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k) : CodedDirectSystem.{u} I where
  carrier i := (diagram.stage i).stage.carrier
  map before := (diagram.transition before).map.points
  injection before := (diagram.transition before).map.point_embedding.injection
  identity := by
    intro i
    rw [diagram.self]
    rfl
  composition := by
    intro i j k first second
    rw [diagram.comp first second]
    rfl
  common_upper := upper

noncomputable def actorSystem (upper : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k) : CodedDirectSystem.{u} I where
  carrier i := (diagram.stage i).stage.actors
  map before := (diagram.transition before).map.actors
  injection before := (diagram.transition before).map.group_embedding.injection
  identity := by
    intro i
    rw [diagram.self]
    rfl
  composition := by
    intro i j k first second
    rw [diagram.comp first second]
    rfl
  common_upper := upper

end GroundChronologicalMainDiagram

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

include run in
theorem common_upper (i j : I) : ∃ k, i ≤ k ∧ j ≤ k := by
  let first := SetMembers.ofMem (run.key i) (ZFSet.mem_range.2 ⟨i, rfl⟩ : run.key i ∈ run.indices)
  let second := SetMembers.ofMem (run.key j) (ZFSet.mem_range.2 ⟨j, rfl⟩ : run.key j ∈ run.indices)
  have total := ordinalMainIndex_total run.indices_ordinal first second
  change (SetMembers.raw first = SetMembers.raw second ∨ SetMembers.raw first ∈ SetMembers.raw second) ∨
    (SetMembers.raw second = SetMembers.raw first ∨ SetMembers.raw second ∈ SetMembers.raw first) at total
  simp only [first, second, SetMembers.raw_ofMem] at total
  rcases total with before | after
  · exact ⟨j, (run.key_order i j).2 before, le_rfl⟩
  · exact ⟨i, le_rfl, (run.key_order j i).2 after⟩

noncomputable def pointSystem : CodedDirectSystem.{u} I :=
  run.diagram.pointSystem run.common_upper

noncomputable def actorSystem : CodedDirectSystem.{u} I :=
  run.diagram.actorSystem run.common_upper

theorem pointSystem_carrier (i : I) :
    run.pointSystem.carrier i = (run.diagram.stage i).stage.carrier := rfl

theorem pointSystem_map {i j : I} (before : i ≤ j) :
    run.pointSystem.map before = (run.diagram.transition before).map.points := rfl

theorem actorSystem_carrier (i : I) :
    run.actorSystem.carrier i = (run.diagram.stage i).stage.actors := rfl

theorem actorSystem_map {i j : I} (before : i ≤ j) :
    run.actorSystem.map before = (run.diagram.transition before).map.actors := rfl

end GroundMainPrefix
end PartitionPilot.Forcing

end OAI
