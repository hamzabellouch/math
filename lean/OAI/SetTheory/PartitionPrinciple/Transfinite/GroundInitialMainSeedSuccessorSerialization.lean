import OAI.SetTheory.PartitionPrinciple.Forcing.GroundCompressionSerializationTransport
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundInitialSeedMatchedSerialization
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundExternalSerializedChronology

namespace OAI


namespace PartitionPilot.Forcing.GroundSerializedChronology
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {s C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M (insert s s) C D rD)

noncomputable def fixedTopValues (newHeight : ZFSet.{u}) : Fin 5 → ZFSet.{u} :=
  Fin.cases (fixedTopCarrier (serial.fields.value 0 s))
    (Fin.cases (fixedTopOrder (serial.fields.value 0 s) (serial.fields.value 1 s))
      (Fin.cases (fixedTopMeet (serial.fields.value 0 s) (serial.fields.value 1 s))
        (Fin.cases (fixedTopBirth (serial.fields.value 0 s) (serial.fields.value 3 s) s)
          (fun _ => newHeight))))

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (newHeight : ZFSet.{u}) (hHeight : newHeight ∈ M.sets)
include pairing unions powers separation hHeight

theorem fixedTopValues_ground : ∀ j, serial.fixedTopValues newHeight j ∈ M.sets := by
  have hP := serial.fields.value_ground 0 s
  have hr := serial.fields.value_ground 1 s
  have hs := M.transitive serial.fields.time_ground (ZFSet.mem_insert s s)
  exact Fin.cases (M.fixedTopCarrier_mem pairing unions hP)
    (Fin.cases (M.fixedTopOrder_mem pairing unions powers separation hP hr)
      (Fin.cases (M.fixedTopMeet_mem pairing unions powers separation hP hr)
        (Fin.cases (M.fixedTopBirth_mem pairing unions hP (serial.fields.value_ground 3 s) hs)
          (fun _ => hHeight))))

noncomputable def fixedTopFields : GroundChronologyFields M (insert s s) :=
  serial.fields.replaceTerminal pairing unions separation (serial.fixedTopValues newHeight)
    (serial.fixedTopValues_ground pairing unions powers separation newHeight hHeight)

theorem fixedTopFields_value_at (j : Fin 5) :
    (serial.fixedTopFields pairing unions powers separation newHeight hHeight).value j s =
      serial.fixedTopValues newHeight j :=
  serial.fields.replaceTerminal_value_at pairing unions separation _ _ j

theorem fixedTopFields_value_old (j : Fin 5) {t : ZFSet.{u}} (ht : t ∈ s) :
    (serial.fixedTopFields pairing unions powers separation newHeight hHeight).value j t =
      serial.fields.value j t :=
  serial.fields.replaceTerminal_value_old pairing unions separation _ _ j ht

theorem fixedTopFields_value (j : Fin 5) {t : ZFSet.{u}} (ht : t ∈ insert s s) :
    (serial.fixedTopFields pairing unions powers separation newHeight hHeight).value j t =
      appendHistoryValue s (serial.fields.value j) (serial.fixedTopValues newHeight j) t :=
  serial.fields.replaceTerminal_value pairing unions separation _ _ j ht

theorem fixedTopFields_old_entries (j : Fin 5) {t y : ZFSet.{u}} (ht : t ∈ s) :
    ZFSet.pair t y ∈ (serial.fixedTopFields pairing unions powers separation newHeight hHeight).graph j ↔
      ZFSet.pair t y ∈ serial.fields.graph j :=
  serial.fields.replaceTerminal_old_entries pairing unions separation _ _ j ht

theorem fixedTopFields_core
    (earlier : ∀ x t, ZFSet.pair x t ∈ serial.fields.value 3 s → t ∈ s)
    (heightCode : StrictLexHeightCode (fixedTopCarrier (serial.fields.value 0 s)) C D
      (fixedTopOrder (serial.fields.value 0 s) (serial.fields.value 1 s)) newHeight rD) :
    ChronologyCoreCode (insert s s)
      (serial.fixedTopFields pairing unions powers separation newHeight hHeight).bound C D rD
      (serial.fixedTopFields pairing unions powers separation newHeight hHeight).graph := by
  let fields := serial.fixedTopFields pairing unions powers separation newHeight hHeight
  refine ⟨fields.function, ?_⟩
  intro cutoff hc L r μ birth height eL er eμ eb eh
  have eqL := fields.value_eq_of_entry 0 eL
  have eqr := fields.value_eq_of_entry 1 er
  have eqμ := fields.value_eq_of_entry 2 eμ
  have eqb := fields.value_eq_of_entry 3 eb
  have eqh := fields.value_eq_of_entry 4 eh
  rw [← eqL, ← eqr, ← eqμ, ← eqb, ← eqh]
  change ChronologyPointCode (insert s s) C D rD cutoff
    ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 0 cutoff)
    ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 1 cutoff)
    ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 2 cutoff)
    ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 3 cutoff)
    ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 4 cutoff)
  rcases ZFSet.mem_insert_iff.1 hc with equal | hc
  · subst cutoff
    rw [fixedTopFields_value_at, fixedTopFields_value_at, fixedTopFields_value_at,
      fixedTopFields_value_at, fixedTopFields_value_at]
    have point := serial.fields.decoded_point serial.core (ZFSet.mem_insert s s)
    exact ⟨fixedTopMeet_code point.meet,
      fixedTopBirth_function point.birth_function (ZFSet.mem_insert s s),
      fun x _ t entry => fixedTopBirth_bound earlier x t entry,
      fixedTopBirth_oldMeet point.meet point.birth_function earlier point.old_meet, heightCode⟩
  · rw [fixedTopFields_value_old _ _ _ _ _ _ _ 0 hc,
      fixedTopFields_value_old _ _ _ _ _ _ _ 1 hc,
      fixedTopFields_value_old _ _ _ _ _ _ _ 2 hc,
      fixedTopFields_value_old _ _ _ _ _ _ _ 3 hc,
      fixedTopFields_value_old _ _ _ _ _ _ _ 4 hc]
    exact serial.fields.decoded_point serial.core (ZFSet.mem_insert_of_mem _ hc)

end PartitionPilot.Forcing.GroundSerializedChronology



namespace PartitionPilot.Forcing.GroundSerializedChronology
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {s C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M (insert s s) C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (newHeight : ZFSet.{u}) (hHeight : newHeight ∈ M.sets)
variable (ordinal : ordinalSetProperty s)
variable (earlier : ∀ x t, ZFSet.pair x t ∈ serial.fields.value 3 s → t ∈ s)
include pairing unions powers separation hHeight ordinal earlier

theorem fixedTopFields_rawWitnesses :
    let fields := serial.fixedTopFields pairing unions powers separation newHeight hHeight
    ∀ cutoff ∈ insert s s, ∀ t ∈ insert s s, t = cutoff ∨ t ∈ cutoff →
      ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 cutoff) (fields.value 1 cutoff) (fields.value 2 cutoff)
        (fields.value 3 cutoff) t ZFSet.omega z := by
  dsimp only
  let fields := serial.fixedTopFields pairing unions powers separation newHeight hHeight
  have inside {t a : ZFSet.{u}} (ht : t ∈ insert s s) (ha : a ∈ t) : a ∈ s := by
    rcases ZFSet.mem_insert_iff.1 ht with equal | ht
    · exact equal ▸ ha
    · exact ordinal.1 t ht a ha
  have transportSources {t A r μ birth z : ZFSet.{u}} (ht : t ∈ insert s s)
      (code : GrowthLayerWitnessCode (serial.fields.graph 0) (serial.fields.graph 1) (serial.fields.graph 2)
        A r μ birth t ZFSet.omega z) :
      GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        A r μ birth t ZFSet.omega z := by
    exact code.congr_source_entries
      (fun a ha y => (serial.fixedTopFields_old_entries pairing unions powers separation newHeight hHeight 0
        (y := y) (inside ht ha)).symm)
      (fun a ha y => (serial.fixedTopFields_old_entries pairing unions powers separation newHeight hHeight 1
        (y := y) (inside ht ha)).symm)
      (fun a ha y => (serial.fixedTopFields_old_entries pairing unions powers separation newHeight hHeight 2
        (y := y) (inside ht ha)).symm)
  intro cutoff hc t ht before
  change ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
    (fields.value 0 cutoff) (fields.value 1 cutoff) (fields.value 2 cutoff) (fields.value 3 cutoff) t ZFSet.omega z
  by_cases terminal : cutoff = s
  · subst cutoff
    change ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 0 s)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 1 s)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 2 s)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 3 s) t ZFSet.omega z
    rw [fixedTopFields_value_at, fixedTopFields_value_at, fixedTopFields_value_at, fixedTopFields_value_at]
    by_cases top : t = s
    · subst t
      exact ⟨fixedTopLayerWitness (serial.fields.value 0 s),
        M.fixedTopLayerWitness_mem pairing (serial.fields.value_ground 0 s), fixedTopLayerWitness_code earlier⟩
    · have strict : t ∈ s := before.resolve_left top
      have prior := serial.layer_code s (ZFSet.mem_insert s s) t ht (Or.inr strict)
        _ (serial.layerWitness_entry (ZFSet.mem_insert s s) ht (Or.inr strict))
      have point := serial.fields.decoded_point serial.core (ZFSet.mem_insert s s)
      obtain ⟨z, hz, code⟩ := prior.exists_fixedTop_earlier pairing unions separation
        (serial.fields.value_ground 0 s) (serial.layerWitness_ground s t) point.meet point.birth_function strict
      exact ⟨z, hz, transportSources ht code⟩
  · have old : cutoff ∈ s := (ZFSet.mem_insert_iff.1 hc).resolve_left terminal
    have code := transportSources ht (serial.layer_code cutoff hc t ht before
      _ (serial.layerWitness_entry hc ht before))
    refine ⟨serial.layerWitness cutoff t, serial.layerWitness_ground cutoff t, ?_⟩
    change GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 0 cutoff)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 1 cutoff)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 2 cutoff)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 3 cutoff) t ZFSet.omega _
    rw [fixedTopFields_value_old _ _ _ _ _ _ _ 0 old,
      fixedTopFields_value_old _ _ _ _ _ _ _ 1 old,
      fixedTopFields_value_old _ _ _ _ _ _ _ 2 old,
      fixedTopFields_value_old _ _ _ _ _ _ _ 3 old]
    exact code

theorem exists_fixedTopSerialization
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (infinite : Realize M.sets infinity Fin.elim0)
    (heightCode : StrictLexHeightCode (fixedTopCarrier (serial.fields.value 0 s)) C D
      (fixedTopOrder (serial.fields.value 0 s) (serial.fields.value 1 s)) newHeight rD) :
    ∃ extended : GroundSerializedChronology M (insert s s) C D rD,
      extended.fields = serial.fixedTopFields pairing unions powers separation newHeight hHeight ∧
      extended.code ∈ M.sets := by
  exact (serial.fixedTopFields pairing unions powers separation newHeight hHeight).exists_serializedChronology
    pairing unions powers separation collection choice infinite
    (serial.fixedTopFields_core pairing unions powers separation newHeight hHeight earlier heightCode)
    (serial.fixedTopFields_rawWitnesses pairing unions powers separation newHeight hHeight ordinal earlier)
    serial.ordinal

theorem exists_fixedTopSerialization_values
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (infinite : Realize M.sets infinity Fin.elim0)
    (heightCode : StrictLexHeightCode (fixedTopCarrier (serial.fields.value 0 s)) C D
      (fixedTopOrder (serial.fields.value 0 s) (serial.fields.value 1 s)) newHeight rD) :
    ∃ extended : GroundSerializedChronology M (insert s s) C D rD,
      extended.fields = serial.fixedTopFields pairing unions powers separation newHeight hHeight ∧
      extended.code ∈ M.sets ∧ ∀ j t, t ∈ insert s s → extended.fields.value j t =
        appendHistoryValue s (serial.fields.value j) (serial.fixedTopValues newHeight j) t := by
  obtain ⟨extended, same, ground⟩ := serial.exists_fixedTopSerialization pairing unions powers separation
    newHeight hHeight ordinal earlier collection choice infinite heightCode
  refine ⟨extended, same, ground, ?_⟩
  intro j t ht
  rw [same]
  exact serial.fixedTopFields_value pairing unions powers separation newHeight hHeight j ht

end PartitionPilot.Forcing.GroundSerializedChronology



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem GroundChronologicalHistory.fieldValue_eq_of_heq
    {M : TransitiveGround.{u}} {T T' C D rD : ZFSet.{u}}
    {first : GroundChronologicalHistory M T C D rD}
    {second : GroundChronologicalHistory M T' C D rD}
    (times : T = T') (same : HEq first second) (j : Fin 5) (s : ZFSet.{u}) :
    first.fieldValue j s = second.fieldValue j s := by
  cases times
  cases eq_of_heq same
  rfl

namespace GroundInitialMainSuccessorData
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "comp" => certificate.compression
local notation "completion" => certificate.compression.born.profiled.heighted.completion
local notation "births" => certificate.births
local notation "heights" => certificate.heights
local notation "external" => certificate.external

include pairing unions powers separation collection infinite choice

theorem exists_compressionSerialization
    (prior : GroundSerializedChronology M (insert source.cutoff source.cutoff) C D rD)
    (agreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
      prior.fields.value j s = source.history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert (comp).born.births.limit (comp).born.births.limit) C D rD,
      serial.code ∈ M.sets ∧ ∀ j s, s ∈ insert (comp).born.births.limit (comp).born.births.limit →
        serial.fields.value j s = (comp).history.fieldValue j s := by
  exact certificate.origin.exists_serializedCompression comp prior
    pairing unions powers separation collection infinite choice
    certificate.indices_ground certificate.sources_ground certificate.representatives_ground
    source.stage.actors_ground certificate.task_action_ground (ZFSet.mem_insert _ _)
    (M.initialCompressionData_template_constancy source.stage.carrier source.stage.actors
      source.stage.order source.stage.meetGraph source.stage.action Labels)
    rfl rfl rfl source.carrier_eq source.order_eq source.meet_eq rfl agreement

theorem exists_externalSerialization
    (prior : GroundSerializedChronology M (insert (comp).born.births.limit (comp).born.births.limit) C D rD)
    (agreement : ∀ j s, s ∈ insert (comp).born.births.limit (comp).born.births.limit →
      prior.fields.value j s = (comp).history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert (births).limit (births).limit) C D rD,
      serial.code ∈ M.sets ∧ ∀ j s, s ∈ insert (births).limit (births).limit →
        serial.fields.value j s = (external).history.fieldValue j s := by
  have atBase (j : Fin 5) := agreement j (comp).born.births.limit (ZFSet.mem_insert _ _)
  have sourceValues := (comp).limit_values
  have sourceMatch : prior.fields.value 0 (comp).born.births.limit = (completion).algebra.union.fields 0 ∧
      prior.fields.value 1 (comp).born.births.limit = (completion).algebra.union.fields 1 ∧
      prior.fields.value 2 (comp).born.births.limit = (completion).algebra.union.fields 2 ∧
      prior.fields.value 3 (comp).born.births.limit = (comp).born.births.birth :=
    ⟨(atBase 0).trans sourceValues.1, (atBase 1).trans sourceValues.2.1,
      (atBase 2).trans sourceValues.2.2.1, (atBase 3).trans sourceValues.2.2.2.1⟩
  obtain ⟨serial, _, ground, values⟩ := (births).exists_externalSerializedChronology heights prior
    (external).inputs source.stage.group_code source.stage.action_code pairing unions powers separation
    infinite source.stage.actors_ground source.stage.carrier_ground (ZFSet.mem_insert _ _)
    sourceMatch collection choice
  refine ⟨serial, ground, ?_⟩
  intro j s hs
  rw [values j s hs]
  have oldValue (a : ZFSet.{u}) (before : a ∈ (comp).born.births.limit ∨ a = (comp).born.births.limit) :
      ((births).chronologyFields heights prior.toHistory).fieldValue j a = (external).history.fieldValue j a := by
    have ha : a ∈ insert (comp).born.births.limit (comp).born.births.limit := before.elim
      (fun h => ZFSet.mem_insert_of_mem _ h) (fun h => h.symm ▸ ZFSet.mem_insert _ _)
    have left := (births).chronologyFields_old heights prior.toHistory before
    have right := (external).old_values a before
    have eLeft : ((births).chronologyFields heights prior.toHistory).fieldValue j a = prior.fields.value j a :=
      Fin.cases left.1 (Fin.cases left.2.1 (Fin.cases left.2.2.1
        (Fin.cases left.2.2.2.1 (Fin.cases left.2.2.2.2 (fun i => Fin.elim0 i))))) j
    have eRight : (external).history.fieldValue j a = (comp).history.fieldValue j a :=
      Fin.cases right.1 (Fin.cases right.2.1 (Fin.cases right.2.2.1
        (Fin.cases right.2.2.2.1 (Fin.cases right.2.2.2.2 (fun i => Fin.elim0 i))))) j
    exact eLeft.trans ((agreement j a ha).trans eRight.symm)
  rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
  · have left := (births).chronologyFields_limit heights prior.toHistory
    have right := (external).limit_values
    exact Fin.cases (left.1.trans right.1.symm)
      (Fin.cases (left.2.1.trans right.2.1.symm) (Fin.cases (left.2.2.1.trans right.2.2.1.symm)
        (Fin.cases (left.2.2.2.1.trans right.2.2.2.1.symm)
          (Fin.cases (left.2.2.2.2.trans right.2.2.2.2.symm) (fun i => Fin.elim0 i))))) j
  · rcases ((births).times.mem_limit_iff s).1 hs with before | equal | ⟨n, rfl⟩
    · exact oldValue s (Or.inl before)
    · exact oldValue s (Or.inr equal)
    · have left := (births).chronologyFields_stamp heights prior.toHistory n
      have right := (external).stamp_values n
      exact Fin.cases (left.1.trans right.1.symm)
        (Fin.cases (left.2.1.trans right.2.1.symm) (Fin.cases (left.2.2.1.trans right.2.2.1.symm)
          (Fin.cases (left.2.2.2.1.trans right.2.2.2.1.symm)
            (Fin.cases (left.2.2.2.2.trans right.2.2.2.2.symm) (fun i => Fin.elim0 i))))) j

theorem exists_boundedSerialization
    (prior : GroundSerializedChronology M (insert (births).limit (births).limit) C D rD)
    (agreement : ∀ j s, s ∈ insert (births).limit (births).limit →
      prior.fields.value j s = (external).history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert (births).limit (births).limit) C D rD,
      serial.code ∈ M.sets ∧ ∀ j s, s ∈ insert (births).limit (births).limit →
        serial.fields.value j s = (external).bounded_history.fieldValue j s := by
  have space := (agreement 0 (births).limit (ZFSet.mem_insert _ _)).trans (external).limit_values.1
  have order := (agreement 1 (births).limit (ZFSet.mem_insert _ _)).trans (external).limit_values.2.1
  have birth := (agreement 3 (births).limit (ZFSet.mem_insert _ _)).trans (external).limit_values.2.2.2.1
  have earlier : ∀ x t, ZFSet.pair x t ∈ prior.fields.value 3 (births).limit → t ∈ (births).limit := by
    intro x t entry
    rw [birth] at entry
    exact (ZFSet.pair_mem_prod.1 ((births).function.1 entry)).2
  have heightCode : StrictLexHeightCode (fixedTopCarrier (prior.fields.value 0 (births).limit)) C D
      (fixedTopOrder (prior.fields.value 0 (births).limit) (prior.fields.value 1 (births).limit))
      (heights).boundedHeight rD := by
    rw [space, order]
    exact certificate.boundedHeights.code
  obtain ⟨serial, _, ground, values⟩ := prior.exists_fixedTopSerialization_values
    pairing unions powers separation (heights).boundedHeight certificate.boundedHeights.height_ground
    (births).times.ordinal earlier collection choice infinite heightCode
  have terminal (j : Fin 5) : prior.fixedTopValues (heights).boundedHeight j =
      (external).bounded_history.fieldValue j (births).limit := by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))) j
    · change fixedTopCarrier (prior.fields.value 0 (births).limit) = _
      rw [space]
      exact (external).bounded_values.1.symm
    · change fixedTopOrder (prior.fields.value 0 (births).limit) (prior.fields.value 1 (births).limit) = _
      rw [space, order]
      exact (external).bounded_values.2.1.symm
    · change fixedTopMeet (prior.fields.value 0 (births).limit) (prior.fields.value 1 (births).limit) = _
      rw [space, order]
      exact (external).bounded_values.2.2.1.symm
    · change fixedTopBirth (prior.fields.value 0 (births).limit) (prior.fields.value 3 (births).limit) (births).limit = _
      rw [space, birth]
      exact (external).bounded_values.2.2.2.1.symm
    · exact (external).bounded_values.2.2.2.2.symm
  refine ⟨serial, ground, ?_⟩
  intro j s hs
  rw [values j s hs]
  rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
  · rw [appendHistoryValue_at]
    exact terminal j
  · rw [appendHistoryValue_old hs]
    have previous := (external).bounded_old_values s hs
    have same : (external).bounded_history.fieldValue j s = (external).history.fieldValue j s :=
      Fin.cases previous.1 (Fin.cases previous.2.1 (Fin.cases previous.2.2.1
        (Fin.cases previous.2.2.2.1 (Fin.cases previous.2.2.2.2 (fun i => Fin.elim0 i))))) j
    exact (agreement j s (ZFSet.mem_insert_of_mem _ hs)).trans same.symm

theorem exists_targetSerialization
    (prior : GroundSerializedChronology M (insert source.cutoff source.cutoff) C D rD)
    (agreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
      prior.fields.value j s = source.history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert certificate.target.cutoff certificate.target.cutoff) C D rD,
      serial.code ∈ M.sets ∧
      (∀ j s, s ∈ insert certificate.target.cutoff certificate.target.cutoff →
        serial.fields.value j s = certificate.target.history.fieldValue j s) ∧
      serial.fields.value 0 certificate.target.cutoff = certificate.target.stage.carrier ∧
      serial.fields.value 1 certificate.target.cutoff = certificate.target.stage.order ∧
      serial.fields.value 2 certificate.target.cutoff = certificate.target.stage.meetGraph ∧
      serial.fields.value 3 certificate.target.cutoff = certificate.target.birth ∧
      serial.fields.value 4 certificate.target.cutoff = certificate.target.stage.height := by
  obtain ⟨compressionSerial, _, compressionValues⟩ := certificate.exists_compressionSerialization
    pairing unions powers separation collection infinite choice prior agreement
  obtain ⟨externalSerial, _, externalValues⟩ := certificate.exists_externalSerialization
    pairing unions powers separation collection infinite choice compressionSerial compressionValues
  obtain ⟨bounded, ground, values⟩ := certificate.exists_boundedSerialization
    pairing unions powers separation collection infinite choice externalSerial externalValues
  have times : insert (births).limit (births).limit = insert certificate.target.cutoff certificate.target.cutoff :=
    congrArg (fun t : ZFSet.{u} => insert t t) certificate.target_cutoff.symm
  let serial := bounded.castTime times
  have serialValues : ∀ j s, s ∈ insert certificate.target.cutoff certificate.target.cutoff →
      serial.fields.value j s = certificate.target.history.fieldValue j s := by
    intro j s hs
    rw [GroundSerializedChronology.castTime_value]
    have old := values j s (times.symm ▸ hs)
    have same := GroundChronologicalHistory.fieldValue_eq_of_heq times.symm certificate.target_history j s
    exact old.trans same.symm
  refine ⟨serial, ?_, serialValues, ?_, ?_, ?_, ?_, ?_⟩
  · rw [GroundSerializedChronology.castTime_code]
    exact ground
  · exact (serialValues 0 _ (ZFSet.mem_insert _ _)).trans certificate.target.carrier_eq
  · exact (serialValues 1 _ (ZFSet.mem_insert _ _)).trans certificate.target.order_eq
  · exact (serialValues 2 _ (ZFSet.mem_insert _ _)).trans certificate.target.meet_eq
  · exact serialValues 3 _ (ZFSet.mem_insert _ _)
  · exact (serialValues 4 _ (ZFSet.mem_insert _ _)).trans certificate.target.height_eq

end GroundInitialMainSuccessorData

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
local notation "comp" => certificate.compression
local notation "completion" => certificate.compression.born.profiled.heighted.completion
local notation "births" => certificate.births
local notation "external" => certificate.external
variable {o : Ordinal.{u}}
variable (completed : ZFSet.rank (certificate.compression.born.profiled.heighted.completion.algebra.union.fields 0) < o)
variable (prior : ∀ s ∈ insert source.cutoff source.cutoff, ZFSet.rank (source.history.space s) < o)
include completed prior

theorem compression_history_carrier_rank_lt {s : ZFSet.{u}}
    (hs : s ∈ insert (comp).born.births.limit (comp).born.births.limit) :
    ZFSet.rank ((comp).history.space s) < o := by
  rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
  · rw [(comp).limit_values.1]
    exact completed
  · rcases ((comp).born.births.times.mem_limit_iff s).1 hs with before | equal | ⟨n, rfl⟩
    · rw [((comp).old_values s (Or.inl before)).1]
      exact prior s (ZFSet.mem_insert_of_mem _ before)
    · rw [((comp).old_values s (Or.inr equal)).1]
      exact prior s (equal.symm ▸ ZFSet.mem_insert _ _)
    · rw [((comp).stamp_values n).1]
      exact (ZFSet.rank_mono (((completion).algebra.union.fieldUnion 0).subset (n + 1))).trans_lt completed

theorem external_history_carrier_rank_lt
    (points : ZFSet.rank ((completion).externalPointCarrier source.stage.carrier
      source.stage.order source.stage.meetGraph source.stage.action) < o)
    {s : ZFSet.{u}} (hs : s ∈ insert (births).limit (births).limit) :
    ZFSet.rank ((external).history.space s) < o := by
  rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
  · rw [(external).limit_values.1]
    exact points
  · rcases ((births).times.mem_limit_iff s).1 hs with before | equal | ⟨n, rfl⟩
    · rw [((external).old_values s (Or.inl before)).1]
      exact certificate.compression_history_carrier_rank_lt completed prior (ZFSet.mem_insert_of_mem _ before)
    · rw [((external).old_values s (Or.inr equal)).1]
      exact certificate.compression_history_carrier_rank_lt completed prior (equal.symm ▸ ZFSet.mem_insert _ _)
    · rw [((external).stamp_values n).1]
      exact (ZFSet.rank_mono ((births).cutoff_subset n)).trans_lt points

theorem target_history_carrier_rank_lt
    (target : ZFSet.rank certificate.target.stage.carrier < o)
    {s : ZFSet.{u}} (hs : s ∈ insert certificate.target.cutoff certificate.target.cutoff) :
    ZFSet.rank (certificate.target.history.space s) < o := by
  have times : insert certificate.target.cutoff certificate.target.cutoff = insert (births).limit (births).limit :=
    congrArg (fun t : ZFSet.{u} => insert t t) certificate.target_cutoff
  have same : certificate.target.history.space s = (external).bounded_history.space s :=
    GroundChronologicalHistory.fieldValue_eq_of_heq times certificate.target_history 0 s
  rw [same]
  have hs' : s ∈ insert (births).limit (births).limit := times ▸ hs
  rcases ZFSet.mem_insert_iff.1 hs' with rfl | hs'
  · rw [(external).bounded_values.1, ← certificate.target_fields.1]
    exact target
  · rw [((external).bounded_old_values s hs').1]
    have points : ZFSet.rank ((completion).externalPointCarrier source.stage.carrier
        source.stage.order source.stage.meetGraph source.stage.action) < o := by
      rw [certificate.target_fields.1] at target
      exact (ZFSet.rank_mono (fixedTopCarrier_subset _)).trans_lt target
    exact certificate.external_history_carrier_rank_lt completed prior points (ZFSet.mem_insert_of_mem _ hs')

end PartitionPilot.Forcing.GroundInitialMainSuccessorData



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem GroundSerializedChronology.agreeing_history_carrier_rank_lt
    {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
    (serial : GroundSerializedChronology M T C D rD)
    (history : GroundChronologicalHistory M T C D rD)
    {o : Ordinal.{u}} (rank : ZFSet.rank serial.code < o)
    (agreement : ∀ j s, s ∈ T → serial.fields.value j s = history.fieldValue j s)
    {s : ZFSet.{u}} (hs : s ∈ T) : ZFSet.rank (history.space s) < o := by
  have bound := (serial.fieldValue_rank_lt_code 0 hs).trans rank
  rw [agreement 0 s hs] at bound
  exact bound

namespace GroundInitialMainSuccessorData
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (invariant : source.Invariant K Labels)
variable (prior : GroundSerializedChronology M (insert source.cutoff source.cutoff) C D rD)
variable (priorRank : ZFSet.rank prior.code < ZFSet.rank K)
variable (priorAgreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
  prior.fields.value j s = source.history.fieldValue j s)
include certificate pairing unions powers separation collection infinite hK conditions invariant priorRank priorAgreement
local notation "comp" => certificate.compression
local notation "completion" => certificate.compression.born.profiled.heighted.completion
local notation "births" => certificate.births
local notation "external" => certificate.external

theorem compressionFieldGraphs_rank_lt
    (fields : GroundChronologyFields M (insert (comp).born.births.limit (comp).born.births.limit))
    (agreement : ∀ j s, s ∈ insert (comp).born.births.limit (comp).born.births.limit →
      fields.value j s = (comp).history.fieldValue j s) (j : Fin 5) :
    ZFSet.rank (fields.graph j) < ZFSet.rank K := by
  have completed := certificate.compression_union_rank_lt pairing unions powers separation collection infinite
    hK conditions invariant.points_rank invariant.labels_rank
  have times := conditions.successor_mem pairing unions powers separation infinite hK
    (certificate.compression_limit_mem pairing unions powers separation infinite hK conditions invariant.cutoff_mem)
  exact fields.graph_rank_lt_of_history pairing unions powers separation collection infinite hK conditions times
    (comp).history agreement
    (fun _ hs => certificate.compression_history_carrier_rank_lt completed
      (fun _ ht => prior.agreeing_history_carrier_rank_lt source.history priorRank priorAgreement ht) hs)
    invariant.columns_rank invariant.coordinates_rank j

theorem externalFieldGraphs_rank_lt
    (fields : GroundChronologyFields M (insert (births).limit (births).limit))
    (agreement : ∀ j s, s ∈ insert (births).limit (births).limit →
      fields.value j s = (external).history.fieldValue j s) (j : Fin 5) :
    ZFSet.rank (fields.graph j) < ZFSet.rank K := by
  have completed := certificate.compression_union_rank_lt pairing unions powers separation collection infinite
    hK conditions invariant.points_rank invariant.labels_rank
  have target := (certificate.target_rank_lt pairing unions powers separation collection infinite
    hK conditions invariant.points_rank invariant.labels_rank invariant.actors_rank).1
  rw [certificate.target_fields.1] at target
  have points := (ZFSet.rank_mono (fixedTopCarrier_subset _)).trans_lt target
  have times := conditions.successor_mem pairing unions powers separation infinite hK
    (certificate.external_limit_mem pairing unions powers separation infinite hK conditions invariant.cutoff_mem)
  exact fields.graph_rank_lt_of_history pairing unions powers separation collection infinite hK conditions times
    (external).history agreement
    (fun _ hs => certificate.external_history_carrier_rank_lt completed
      (fun _ ht => prior.agreeing_history_carrier_rank_lt source.history priorRank priorAgreement ht) points hs)
    invariant.columns_rank invariant.coordinates_rank j

theorem targetFieldGraphs_rank_lt
    (fields : GroundChronologyFields M (insert certificate.target.cutoff certificate.target.cutoff))
    (agreement : ∀ j s, s ∈ insert certificate.target.cutoff certificate.target.cutoff →
      fields.value j s = certificate.target.history.fieldValue j s) (j : Fin 5) :
    ZFSet.rank (fields.graph j) < ZFSet.rank K := by
  have completed := certificate.compression_union_rank_lt pairing unions powers separation collection infinite
    hK conditions invariant.points_rank invariant.labels_rank
  have target := (certificate.target_rank_lt pairing unions powers separation collection infinite
    hK conditions invariant.points_rank invariant.labels_rank invariant.actors_rank).1
  have times := certificate.target_time_domain_mem pairing unions powers separation infinite hK conditions invariant.cutoff_mem
  exact fields.graph_rank_lt_of_history pairing unions powers separation collection infinite hK conditions times
    certificate.target.history agreement
    (fun _ hs => certificate.target_history_carrier_rank_lt completed
      (fun _ ht => prior.agreeing_history_carrier_rank_lt source.history priorRank priorAgreement ht) target hs)
    invariant.columns_rank invariant.coordinates_rank j

end GroundInitialMainSuccessorData

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialMainSeedSuccessor
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ seed : GroundInitialMainSeedData M K C,
      ∃ certificate : GroundInitialMainSuccessorData M C (rationalCarrier seed.fractionCode)
          (rationalLtGraph seed.fractionCode) seed.source C,
        certificate.target.Invariant K C ∧
          ZFSet.rank certificate.transition.map.code < ZFSet.rank K := by
  dsimp only
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨seed⟩ := M.exists_groundInitialMainSeed pairing unions powers separation infinite
    collection hK conditions
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  obtain ⟨certificate⟩ := M.exists_groundInitialMainSuccessor pairing unions powers separation
    collection infinite choice seed.source hC seed.injection_ground seed.dense
    (fun lo hlo => (seed.no_endpoints lo hlo).2) seed.injection_code
  have invariant := certificate.target_invariant pairing unions powers separation collection infinite
    choice hC hK standard seed.invariant
  refine ⟨seed, certificate, invariant, ?_⟩
  exact certificate.transition.map.code_rank_lt_inaccessible pairing unions powers separation infinite
    hK conditions seed.invariant.points_rank invariant.points_rank
    seed.invariant.actors_rank invariant.actors_rank






theorem exists_groundInitialMainSeedSuccessorSerialized
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ seed : GroundInitialMainSeedData M K C,
      ∃ certificate : GroundInitialMainSuccessorData M C (rationalCarrier seed.fractionCode)
          (rationalLtGraph seed.fractionCode) seed.source C,
        ∃ initial : GroundSerializedChronology M (insert seed.source.cutoff seed.source.cutoff)
            C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode),
          ∃ successor : GroundSerializedChronology M
              (insert certificate.target.cutoff certificate.target.cutoff)
              C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode),
            initial.code ∈ M.sets ∧ ZFSet.rank initial.code < ZFSet.rank K ∧
            (∀ j t, t ∈ insert seed.source.cutoff seed.source.cutoff →
              initial.fields.value j t = seed.source.history.fieldValue j t) ∧
            successor.code ∈ M.sets ∧
            (∀ j t, t ∈ insert certificate.target.cutoff certificate.target.cutoff →
              successor.fields.value j t = certificate.target.history.fieldValue j t) ∧
            certificate.target.Invariant K C ∧
            ZFSet.rank certificate.transition.map.code < ZFSet.rank K ∧
            successor.fields.value 0 certificate.target.cutoff = certificate.target.stage.carrier ∧
            successor.fields.value 1 certificate.target.cutoff = certificate.target.stage.order ∧
            successor.fields.value 2 certificate.target.cutoff = certificate.target.stage.meetGraph ∧
            successor.fields.value 3 certificate.target.cutoff = certificate.target.birth ∧
            successor.fields.value 4 certificate.target.cutoff = certificate.target.stage.height := by
  dsimp only
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨seed⟩ := M.exists_groundInitialMainSeed pairing unions powers separation infinite collection hK conditions
  obtain ⟨initial, initialGround, initialRank, initialAgreement⟩ :=
    seed.exists_matchedInitialSerialization pairing unions powers separation infinite hK conditions
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  obtain ⟨certificate⟩ := M.exists_groundInitialMainSuccessor pairing unions powers separation
    collection infinite choice seed.source hC seed.injection_ground seed.dense
    (fun lo hlo => (seed.no_endpoints lo hlo).2) seed.injection_code
  obtain ⟨successor, successorGround, successorAgreement, terminal⟩ :=
    certificate.exists_targetSerialization pairing unions powers separation collection infinite choice initial initialAgreement
  have invariant := certificate.target_invariant pairing unions powers separation collection infinite
    choice hC hK standard seed.invariant
  have transitionRank := certificate.transition.map.code_rank_lt_inaccessible pairing unions powers separation infinite
    hK conditions seed.invariant.points_rank invariant.points_rank seed.invariant.actors_rank invariant.actors_rank
  exact ⟨seed, certificate, initial, successor, initialGround, initialRank, initialAgreement,
    successorGround, successorAgreement, invariant, transitionRank, terminal⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
