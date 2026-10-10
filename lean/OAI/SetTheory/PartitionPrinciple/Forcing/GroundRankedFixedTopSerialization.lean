import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRankedSerializedChronology

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem terminalChronologyGraph_rank_lt {s f v : ZFSet.{u}} {o : Ordinal.{u}}
    (limit : Order.IsSuccLimit o) (time : ZFSet.rank s < o) (graph : ZFSet.rank f < o)
    (value : ZFSet.rank v < o) : ZFSet.rank (terminalChronologyGraph s f v) < o := by
  rw [terminalChronologyGraph, ZFSet.rank_insert]
  exact max_lt (limit.succ_lt (rank_orderedPair_lt limit time value))
    ((ZFSet.rank_mono (graphRestriction_subset s f)).trans_lt graph)

namespace GroundSerializedChronology
variable {M : TransitiveGround.{u}} {s C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M (insert s s) C D rD)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank serial.code < o)
variable {newHeight : ZFSet.{u}} (height : ZFSet.rank newHeight < o)
include limit rank height

theorem fixedTopValues_rank_lt : ∀ j, ZFSet.rank (serial.fixedTopValues newHeight j) < o := by
  have value := fun j => (serial.fieldValue_rank_lt_code j (ZFSet.mem_insert s s)).trans rank
  have time := (ZFSet.rank_lt_of_mem (ZFSet.mem_insert s s)).trans_le serial.time_rank_le_code
  have points : ZFSet.rank (fixedTopCarrier (serial.fields.value 0 s)) < o := by
    rw [fixedTopCarrier, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt (value 0)) (value 0)
  have meet := fixedTopMeet_code (serial.fields.decoded_point serial.core (ZFSet.mem_insert s s)).meet
  have pp := rank_product_lt limit points points
  have order := (ZFSet.rank_mono meet.order.relation).trans_lt pp
  have operation := rank_functionGraph_lt limit meet.operation pp points
  have birth : ZFSet.rank (fixedTopBirth (serial.fields.value 0 s) (serial.fields.value 3 s) s) < o := by
    rw [fixedTopBirth, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt (rank_orderedPair_lt limit (value 0) (time.trans rank))) (value 3)
  exact Fin.cases points (Fin.cases order (Fin.cases operation (Fin.cases birth (fun _ => height))))

theorem fixedTopFields_graph_rank_lt
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hHeight : newHeight ∈ M.sets) (j : Fin 5) :
    ZFSet.rank ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).graph j) < o :=
  terminalChronologyGraph_rank_lt limit
    (((ZFSet.rank_lt_of_mem (ZFSet.mem_insert s s)).trans_le serial.time_rank_le_code).trans rank)
    ((serial.fieldGraph_rank_le_code j).trans_lt rank)
    (serial.fixedTopValues_rank_lt limit rank height j)

end GroundSerializedChronology

end PartitionPilot.Forcing

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
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank serial.code < o)
include pairing unions powers separation hHeight ordinal earlier limit rank

theorem fixedTopFields_rankedRawWitnesses :
    let fields := serial.fixedTopFields pairing unions powers separation newHeight hHeight
    ∀ cutoff ∈ insert s s, ∀ t ∈ insert s s, t = cutoff ∨ t ∈ cutoff →
      ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
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
  change ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
    (fields.value 0 cutoff) (fields.value 1 cutoff) (fields.value 2 cutoff) (fields.value 3 cutoff) t ZFSet.omega z
  by_cases terminal : cutoff = s
  · subst cutoff
    change ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 0 s)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 1 s)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 2 s)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 3 s) t ZFSet.omega z
    rw [fixedTopFields_value_at, fixedTopFields_value_at, fixedTopFields_value_at, fixedTopFields_value_at]
    by_cases top : t = s
    · subst t
      exact ⟨fixedTopLayerWitness (serial.fields.value 0 s),
        M.fixedTopLayerWitness_mem pairing (serial.fields.value_ground 0 s),
        fixedTopLayerWitness_rank_lt limit ((serial.fieldValue_rank_lt_code 0 (ZFSet.mem_insert s s)).trans rank),
        fixedTopLayerWitness_code earlier⟩
    · have strict : t ∈ s := before.resolve_left top
      have prior := serial.layer_code s (ZFSet.mem_insert s s) t ht (Or.inr strict)
        _ (serial.layerWitness_entry (ZFSet.mem_insert s s) ht (Or.inr strict))
      have point := serial.fields.decoded_point serial.core (ZFSet.mem_insert s s)
      obtain ⟨z, hz, code, rankZ⟩ := prior.exists_fixedTop_earlier_rank_lt pairing unions separation
        (serial.fields.value_ground 0 s) (serial.layerWitness_ground s t) limit
        ((serial.layerWitness_rank_lt_code (ZFSet.mem_insert s s) ht (Or.inr strict)).trans rank)
        point.meet point.birth_function strict
      exact ⟨z, hz, rankZ, transportSources ht code⟩
  · have old : cutoff ∈ s := (ZFSet.mem_insert_iff.1 hc).resolve_left terminal
    have code := transportSources ht (serial.layer_code cutoff hc t ht before
      _ (serial.layerWitness_entry hc ht before))
    refine ⟨serial.layerWitness cutoff t, serial.layerWitness_ground cutoff t,
      (serial.layerWitness_rank_lt_code hc ht before).trans rank, ?_⟩
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

end PartitionPilot.Forcing.GroundSerializedChronology

namespace PartitionPilot.Forcing.GroundSerializedChronology
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {s C D rD K : ZFSet.{u}}
variable (serial : GroundSerializedChronology M (insert s s) C D rD)

theorem exists_rankedFixedTopSerialization
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (time : insert s s ∈ K) (level : GroundMainCandidateLevel M K)
    (rank : ZFSet.rank serial.code < ZFSet.rank K)
    (newHeight : ZFSet.{u}) (hHeight : newHeight ∈ M.sets)
    (heightRank : ZFSet.rank newHeight < ZFSet.rank K)
    (ordinal : ordinalSetProperty s)
    (earlier : ∀ x t, ZFSet.pair x t ∈ serial.fields.value 3 s → t ∈ s)
    (heightCode : StrictLexHeightCode (fixedTopCarrier (serial.fields.value 0 s)) C D
      (fixedTopOrder (serial.fields.value 0 s) (serial.fields.value 1 s)) newHeight rD) :
    ∃ extended : GroundSerializedChronology M (insert s s) C D rD,
      extended.code ∈ M.sets ∧ ZFSet.rank extended.code < ZFSet.rank K ∧
        extended.code ∈ level.validChronologies C D rD ∧
        extended.fields.graph = (serial.fixedTopFields pairing unions powers separation newHeight hHeight).graph ∧
        ∀ j t, t ∈ insert s s → extended.fields.value j t =
          appendHistoryValue s (serial.fields.value j) (serial.fixedTopValues newHeight j) t := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  obtain ⟨extended, ground, rankExtended, member, graphs, values, _⟩ :=
    (serial.fixedTopFields pairing unions powers separation newHeight hHeight).exists_rankedSerialization
      pairing unions powers separation collection infinite choice hK conditions time level
      (ordinalSetProperty_succ ordinal)
      (serial.fixedTopFields_core pairing unions powers separation newHeight hHeight earlier heightCode)
      (serial.fixedTopFields_graph_rank_lt limit rank heightRank pairing unions powers separation hHeight)
      (serial.fixedTopFields_rankedRawWitnesses pairing unions powers separation
        newHeight hHeight ordinal earlier limit rank)
  refine ⟨extended, ground, rankExtended, member, graphs, ?_⟩
  intro j t ht
  rw [values j t]
  exact serial.fixedTopFields_value pairing unions powers separation newHeight hHeight j ht

end PartitionPilot.Forcing.GroundSerializedChronology

end OAI
