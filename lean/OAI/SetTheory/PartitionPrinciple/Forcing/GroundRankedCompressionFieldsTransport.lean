import OAI.SetTheory.PartitionPrinciple.Forcing.GroundBatchEarlierLayerWitnesses
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundCompressionIncomingWitnessRanks
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundLayerSourceCongruence
import OAI.SetTheory.PartitionPrinciple.Transfinite.CodedMainPrefixSystems

namespace OAI


namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)

theorem exists_canonicalIncomingWitness
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {HQs Hrs Hμs HTime N : ZFSet.{u}}
    (historySpaces : FunctionGraphOn HTime HQs)
    (historyOrders : FunctionGraphOn HTime Hrs)
    (historyMeets : FunctionGraphOn HTime Hμs)
    (source : ZFSet.pair base P0 ∈ HQs ∧ ZFSet.pair base r0 ∈ Hrs ∧ ZFSet.pair base μ0 ∈ Hμs)
    (n : Nat) :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T (n + 1)).D
      (state.data.iterate M I Sources Reps G T (n + 1)).rD
      (state.data.iterate M I Sources Reps G T (n + 1)).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth)
      (compressionStamp base n) N z := by
  let current := state.iterate pairing unions powers separation hI hSources hReps hG hT n
  have equal : current.data = state.data.iterate M I Sources Reps G T n :=
    state.iterate_data pairing unions powers separation hI hSources hReps hG hT n
  have currentConstant : RecursiveTemplateConstancy P0 r0 μ0 current.data := by
    simpa only [equal] using constant.iterate M I Sources Reps G T n
  have finite : ZFSet.IsFunc current.data.D births.limit
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth) := by
    simpa only [equal] using state.canonical_birth_function data pairing unions powers separation
      hI hSources hReps hG hT births.extension births.initial_function births.times n
  have earlier : ∀ x t, ZFSet.pair x t ∈
      graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth →
      t ∈ compressionStamp base n := fun _ _ entry =>
    state.canonical_birth_before_stamp pairing unions powers separation hI hSources hReps hG hT
      births.extension births.initial_bound n entry
  have result := current.batch.constantBatchLayerWitness_spec pairing unions powers separation
    current.ground.carrier current.ground.indices current.ground.spaces current.ground.relations
    current.ground.anchors current.ground.embeddings historySpaces historyOrders historyMeets finite earlier
    (M.transitive births.limit_ground (births.times.stamp_mem_limit n)) (compressionStamp_base_mem base n)
    (fun i => ⟨((currentConstant.space_entry_iff _ _).1 (current.batch.space_entry i)).2,
      ((currentConstant.relation_entry_iff _ _).1 (current.batch.rel_entry i)).2,
      ((currentConstant.meet_entry_iff _ _).1 (current.batch.meet_entry i)).2⟩) source (N := N)
  refine ⟨current.batch.constantBatchLayerWitness M base, result.1, ?_⟩
  have code := result.2
  change GrowthLayerWitnessCode HQs Hrs Hμs current.data.currentCarrier
    current.data.currentOrder current.data.currentMeet
    (taggedBirth current.data.D current.data.fresh
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth)
      (compressionStamp base n)) (compressionStamp base n) N _ at code
  rw [state.canonical_birth_step pairing unions powers separation hI hSources hReps hG hT
    births.extension births.initial_function n]
  simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor] using code

end PartitionPilot.Forcing.GroundCompressionState



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
variable (prior : GroundSerializedChronology M T0 C Q qlt)
variable (fields : GroundChronologyFields M (insert births.limit births.limit))
variable (hBase : base ∈ T0)
variable (values : ∀ j s, s ∈ insert births.limit births.limit →
  fields.value j s = (state.prefixFields data births heights prior.toHistory).fieldValue j s)
include values

theorem prefixOldField_value (j : Fin 5) {s : ZFSet.{u}} (oldTime : s ∈ base ∨ s = base) :
    fields.value j s = prior.fields.value j s := by
  have hs : s ∈ insert births.limit births.limit := ZFSet.mem_insert_of_mem _
    ((births.times.mem_limit_iff s).2 (oldTime.elim Or.inl (fun h => Or.inr (Or.inl h))))
  have oldFields := state.prefixFields_old data births heights prior.toHistory oldTime
  exact (values j s hs).trans (Fin.cases oldFields.1 (Fin.cases oldFields.2.1
    (Fin.cases oldFields.2.2.1 (Fin.cases oldFields.2.2.2.1 (Fin.cases oldFields.2.2.2.2 (fun i => Fin.elim0 i))))) j)

include hBase in
theorem prefixOldField_entries (j : Fin 5) {s : ZFSet.{u}} (oldTime : s ∈ base ∨ s = base)
    (y : ZFSet.{u}) :
    ZFSet.pair s y ∈ prior.fields.graph j ↔ ZFSet.pair s y ∈ fields.graph j := by
  have oldIndex : s ∈ T0 := oldTime.elim (fun h => prior.ordinal.1 base hBase s h) (fun h => h.symm ▸ hBase)
  have newIndex : s ∈ insert births.limit births.limit := ZFSet.mem_insert_of_mem _
    ((births.times.mem_limit_iff s).2 (oldTime.elim Or.inl (fun h => Or.inr (Or.inl h))))
  have equal := state.prefixOldField_value data births heights prior fields values j oldTime
  constructor
  · intro entry
    have output := (prior.fields.value_eq_of_entry j entry).symm.trans equal.symm
    exact output.symm ▸ fields.value_entry j newIndex
  · intro entry
    have output := (fields.value_eq_of_entry j entry).symm.trans equal
    exact output.symm ▸ prior.fields.value_entry j oldIndex

include hBase in
theorem exists_prefixOldWitness {cutoff t : ZFSet.{u}}
    (oldCutoff : cutoff ∈ base ∨ cutoff = base) (bound : t = cutoff ∨ t ∈ cutoff) :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
      (fields.value 0 cutoff) (fields.value 1 cutoff) (fields.value 2 cutoff)
      (fields.value 3 cutoff) t ZFSet.omega z := by
  have hc : cutoff ∈ T0 := oldCutoff.elim
    (fun member => prior.ordinal.1 base hBase cutoff member) (fun equal => equal.symm ▸ hBase)
  have ht : t ∈ T0 := bound.elim (fun equal => equal.symm ▸ hc)
    (fun before => prior.ordinal.1 cutoff hc t before)
  have oldTime : t ∈ base ∨ t = base := by
    rcases bound with equal | before
    · exact equal.symm ▸ oldCutoff
    · apply Or.inl
      rcases oldCutoff with member | equal
      · exact prior.ordinal.2 base hBase cutoff member t before
      · exact equal ▸ before
  have oldSource {s : ZFSet.{u}} (before : s ∈ t) : s ∈ base ∨ s = base := by
    apply Or.inl
    rcases oldTime with member | equal
    · exact prior.ordinal.2 base hBase t member s before
    · exact equal ▸ before
  have code := (prior.layer_code cutoff hc t ht bound _ (prior.layerWitness_entry hc ht bound)).congr_source_entries
    (fun s hs y => state.prefixOldField_entries data births heights prior fields hBase values 0 (oldSource hs) y)
    (fun s hs y => state.prefixOldField_entries data births heights prior fields hBase values 1 (oldSource hs) y)
    (fun s hs y => state.prefixOldField_entries data births heights prior fields hBase values 2 (oldSource hs) y)
  refine ⟨prior.layerWitness cutoff t, prior.layerWitness_ground cutoff t, ?_⟩
  rw [state.prefixOldField_value data births heights prior fields values 0 oldCutoff,
    state.prefixOldField_value data births heights prior fields values 1 oldCutoff,
    state.prefixOldField_value data births heights prior fields values 2 oldCutoff,
    state.prefixOldField_value data births heights prior fields values 3 oldCutoff]
  exact code

end PartitionPilot.Forcing.GroundCompressionState




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
variable (prior : GroundSerializedChronology M T0 C Q qlt)
variable (fields : GroundChronologyFields M (insert births.limit births.limit))

theorem prefix_rawWitnesses
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (hBase : base ∈ T0)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
    (initialMeet : state.data.μD = μ0)
    (priorSpace : prior.fields.value 0 base = P0) (priorOrder : prior.fields.value 1 base = r0)
    (priorMeet : prior.fields.value 2 base = μ0) (priorBirth : prior.fields.value 3 base = old)
    (values : ∀ j s, s ∈ insert births.limit births.limit →
      fields.value j s = (state.prefixFields data births heights prior.toHistory).fieldValue j s) :
    ∀ cutoff ∈ insert births.limit births.limit, ∀ t ∈ insert births.limit births.limit,
      t = cutoff ∨ t ∈ cutoff → ∃ z ∈ M.sets,
      GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 cutoff) (fields.value 1 cutoff) (fields.value 2 cutoff)
        (fields.value 3 cutoff) t ZFSet.omega z := by
  have baseIn : base ∈ insert births.limit births.limit :=
    ZFSet.mem_insert_of_mem _ births.times.base_mem_limit
  have atBase := fun j => state.prefixOldField_value data births heights prior fields values j
    (Or.inr rfl : base ∈ base ∨ base = base)
  have source : ZFSet.pair base P0 ∈ fields.graph 0 ∧ ZFSet.pair base r0 ∈ fields.graph 1 ∧
      ZFSet.pair base μ0 ∈ fields.graph 2 := by
    have first := fields.value_entry 0 baseIn
    have second := fields.value_entry 1 baseIn
    have third := fields.value_entry 2 baseIn
    rw [atBase 0, priorSpace] at first
    rw [atBase 1, priorOrder] at second
    rw [atBase 2, priorMeet] at third
    exact ⟨first, second, third⟩
  have oldWitness (t : ZFSet.{u}) (before : t ∈ base ∨ t = base) :
      ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        state.data.D state.data.rD state.data.μD old t ZFSet.omega z := by
    obtain ⟨z, hz, code⟩ := state.exists_prefixOldWitness data births heights prior fields hBase values
      (Or.inr rfl : base ∈ base ∨ base = base) before.symm
    rw [atBase 0, atBase 1, atBase 2, atBase 3, priorSpace, priorOrder, priorMeet, priorBirth] at code
    exact ⟨z, hz, initialDomain.symm ▸ initialOrder.symm ▸ initialMeet.symm ▸ code⟩
  have incoming (n : Nat) := state.exists_canonicalIncomingWitness data births
    pairing unions powers separation hI hSources hReps hG hT constant
    (fields.graphFunction 0) (fields.graphFunction 1) (fields.graphFunction 2) source n (N := ZFSet.omega)
  have atStamp (n : Nat) :
      fields.value 0 (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).D ∧
      fields.value 1 (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).rD ∧
      fields.value 2 (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).μD ∧
      fields.value 3 (compressionStamp base n) = graphRestriction
        (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth := by
    have hs := ZFSet.mem_insert_of_mem births.limit (births.times.stamp_mem_limit n)
    have exactFields := state.prefixFields_stamp data births heights prior.toHistory n
    exact ⟨(values 0 _ hs).trans exactFields.1, (values 1 _ hs).trans exactFields.2.1,
      (values 2 _ hs).trans exactFields.2.2.1, (values 3 _ hs).trans exactFields.2.2.2.1⟩
  have atLimit : fields.value 0 births.limit = data.fields 0 ∧
      fields.value 1 births.limit = data.fields 1 ∧ fields.value 2 births.limit = data.fields 2 ∧
      fields.value 3 births.limit = births.birth := by
    have hs := ZFSet.mem_insert births.limit births.limit
    have exactFields := state.prefixFields_limit data births heights prior.toHistory
    exact ⟨(values 0 _ hs).trans exactFields.1, (values 1 _ hs).trans exactFields.2.1,
      (values 2 _ hs).trans exactFields.2.2.1, (values 3 _ hs).trans exactFields.2.2.2.1⟩
  have finite (n : Nat) (t : ZFSet.{u}) (bound : t = compressionStamp base n ∨ t ∈ compressionStamp base n) :
      ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 (compressionStamp base n)) (fields.value 1 (compressionStamp base n))
        (fields.value 2 (compressionStamp base n)) (fields.value 3 (compressionStamp base n)) t ZFSet.omega z := by
    rw [(atStamp n).1, (atStamp n).2.1, (atStamp n).2.2.1, (atStamp n).2.2.2]
    have cases : (t ∈ base ∨ t = base) ∨ ∃ j, j ≤ n ∧ t = compressionStamp base j := by
      rcases bound with equal | before
      · exact Or.inr ⟨n, Nat.le_refl n, equal⟩
      · rcases (mem_compressionStamp_iff base t n).1 before with old | same | ⟨j, earlier, equal⟩
        · exact Or.inl (Or.inl old)
        · exact Or.inl (Or.inr same)
        · exact Or.inr ⟨j, Nat.le_of_lt earlier, equal⟩
    rcases cases with before | ⟨j, before, rfl⟩
    · obtain ⟨z, hz, code⟩ := oldWitness t before
      exact state.exists_priorWitness_to_finite data births pairing unions powers separation hI hSources hReps hG hT
        (n + 1) before hz code
    · obtain ⟨z, hz, code⟩ := incoming j
      exact state.exists_birthWitness_to_finite data births pairing unions powers separation hI hSources hReps hG hT
        (j + 1) (n + 1) (Nat.add_le_add_right before 1)
        ((compressionStamp_mem_iff base j (j + 1)).2 (Nat.lt_succ_self j)) hz code
  have terminal (t : ZFSet.{u}) (bound : t = births.limit ∨ t ∈ births.limit) :
      ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 births.limit) (fields.value 1 births.limit)
        (fields.value 2 births.limit) (fields.value 3 births.limit) t ZFSet.omega z := by
    rw [atLimit.1, atLimit.2.1, atLimit.2.2.1, atLimit.2.2.2]
    rcases bound with rfl | before
    · exact state.exists_limitWitness data births pairing
    · rcases (births.times.mem_limit_iff t).1 before with old | same | ⟨j, rfl⟩
      · obtain ⟨z, hz, code⟩ := oldWitness t (Or.inl old)
        exact state.exists_priorWitness_to_union data births pairing unions powers separation hI hSources hReps hG hT
          (Or.inl old) hz code
      · obtain ⟨z, hz, code⟩ := oldWitness t (Or.inr same)
        exact state.exists_priorWitness_to_union data births pairing unions powers separation hI hSources hReps hG hT
          (Or.inr same) hz code
      · obtain ⟨z, hz, code⟩ := incoming j
        exact state.exists_birthWitness_to_union data births pairing unions powers separation hI hSources hReps hG hT
          (j + 1) ((compressionStamp_mem_iff base j (j + 1)).2 (Nat.lt_succ_self j)) hz code
  intro cutoff hc t _ bound
  rcases ZFSet.mem_insert_iff.1 hc with rfl | before
  · exact terminal t bound
  · rcases (births.times.mem_limit_iff cutoff).1 before with oldTime | same | ⟨n, rfl⟩
    · exact state.exists_prefixOldWitness data births heights prior fields hBase values (Or.inl oldTime) bound
    · exact state.exists_prefixOldWitness data births heights prior fields hBase values (Or.inr same) bound
    · exact finite n t bound

end PartitionPilot.Forcing.GroundCompressionState



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
variable (prior : GroundSerializedChronology M T0 C Q qlt)
variable (fields : GroundChronologyFields M (insert births.limit births.limit))
variable (hBase : base ∈ T0)
variable (values : ∀ j s, s ∈ insert births.limit births.limit →
  fields.value j s = (state.prefixFields data births heights prior.toHistory).fieldValue j s)
include hBase values in
theorem exists_prefixOldRankedWitness {o : Ordinal.{u}} (priorRank : ZFSet.rank prior.code < o) {cutoff t : ZFSet.{u}}
    (oldCutoff : cutoff ∈ base ∨ cutoff = base) (bound : t = cutoff ∨ t ∈ cutoff) :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
      (fields.value 0 cutoff) (fields.value 1 cutoff) (fields.value 2 cutoff)
      (fields.value 3 cutoff) t ZFSet.omega z ∧ ZFSet.rank z < o := by
  have hc : cutoff ∈ T0 := oldCutoff.elim
    (fun member => prior.ordinal.1 base hBase cutoff member) (fun equal => equal.symm ▸ hBase)
  have ht : t ∈ T0 := bound.elim (fun equal => equal.symm ▸ hc)
    (fun before => prior.ordinal.1 cutoff hc t before)
  have oldTime : t ∈ base ∨ t = base := by
    rcases bound with equal | before
    · exact equal.symm ▸ oldCutoff
    · apply Or.inl
      rcases oldCutoff with member | equal
      · exact prior.ordinal.2 base hBase cutoff member t before
      · exact equal ▸ before
  have oldSource {s : ZFSet.{u}} (before : s ∈ t) : s ∈ base ∨ s = base := by
    apply Or.inl
    rcases oldTime with member | equal
    · exact prior.ordinal.2 base hBase t member s before
    · exact equal ▸ before
  have code := (prior.layer_code cutoff hc t ht bound _ (prior.layerWitness_entry hc ht bound)).congr_source_entries
    (fun s hs y => state.prefixOldField_entries data births heights prior fields hBase values 0 (oldSource hs) y)
    (fun s hs y => state.prefixOldField_entries data births heights prior fields hBase values 1 (oldSource hs) y)
    (fun s hs y => state.prefixOldField_entries data births heights prior fields hBase values 2 (oldSource hs) y)
  refine ⟨prior.layerWitness cutoff t, prior.layerWitness_ground cutoff t, ?_,
    (prior.layerWitness_rank_lt_code hc ht bound).trans priorRank⟩
  rw [state.prefixOldField_value data births heights prior fields values 0 oldCutoff,
    state.prefixOldField_value data births heights prior fields values 1 oldCutoff,
    state.prefixOldField_value data births heights prior fields values 2 oldCutoff,
    state.prefixOldField_value data births heights prior fields values 3 oldCutoff]
  exact code

end PartitionPilot.Forcing.GroundCompressionState




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
variable (prior : GroundSerializedChronology M T0 C Q qlt)
variable (fields : GroundChronologyFields M (insert births.limit births.limit))

theorem prefix_rankedRawWitnesses
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (hBase : base ∈ T0)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (priorRank : ZFSet.rank prior.code < o)
    (indices : ZFSet.rank state.data.J < o) (tasks : ZFSet.rank I < o)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
    (initialMeet : state.data.μD = μ0)
    (priorSpace : prior.fields.value 0 base = P0) (priorOrder : prior.fields.value 1 base = r0)
    (priorMeet : prior.fields.value 2 base = μ0) (priorBirth : prior.fields.value 3 base = old)
    (values : ∀ j s, s ∈ insert births.limit births.limit →
      fields.value j s = (state.prefixFields data births heights prior.toHistory).fieldValue j s) :
    ∀ cutoff ∈ insert births.limit births.limit, ∀ t ∈ insert births.limit births.limit,
      t = cutoff ∨ t ∈ cutoff → ∃ z ∈ M.sets,
      GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 cutoff) (fields.value 1 cutoff) (fields.value 2 cutoff)
        (fields.value 3 cutoff) t ZFSet.omega z ∧ ZFSet.rank z < o := by
  have templates : ZFSet.rank P0 < o := by
    rw [← priorSpace]
    exact (prior.fieldValue_rank_lt_code 0 hBase).trans priorRank
  have points : ZFSet.rank state.data.D < o := initialDomain.symm ▸ templates
  have time : ZFSet.rank base < o :=
    ((ZFSet.rank_lt_of_mem hBase).trans_le prior.time_rank_le_code).trans priorRank
  have baseIn : base ∈ insert births.limit births.limit :=
    ZFSet.mem_insert_of_mem _ births.times.base_mem_limit
  have atBase := fun j => state.prefixOldField_value data births heights prior fields values j
    (Or.inr rfl : base ∈ base ∨ base = base)
  have source : ZFSet.pair base P0 ∈ fields.graph 0 ∧ ZFSet.pair base r0 ∈ fields.graph 1 ∧
      ZFSet.pair base μ0 ∈ fields.graph 2 := by
    have first := fields.value_entry 0 baseIn
    have second := fields.value_entry 1 baseIn
    have third := fields.value_entry 2 baseIn
    rw [atBase 0, priorSpace] at first
    rw [atBase 1, priorOrder] at second
    rw [atBase 2, priorMeet] at third
    exact ⟨first, second, third⟩
  have oldWitness (t : ZFSet.{u}) (before : t ∈ base ∨ t = base) :
      ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        state.data.D state.data.rD state.data.μD old t ZFSet.omega z ∧ ZFSet.rank z < o := by
    obtain ⟨z, hz, code, rank⟩ := state.exists_prefixOldRankedWitness data births heights prior fields hBase values priorRank
      (Or.inr rfl : base ∈ base ∨ base = base) before.symm
    rw [atBase 0, atBase 1, atBase 2, atBase 3, priorSpace, priorOrder, priorMeet, priorBirth] at code
    exact ⟨z, hz, initialDomain.symm ▸ initialOrder.symm ▸ initialMeet.symm ▸ code, rank⟩
  have incoming (n : Nat) := state.exists_canonicalIncomingRankedWitness data births
    pairing unions powers separation hI hSources hReps hG hT constant
    (fields.graphFunction 0) (fields.graphFunction 1) (fields.graphFunction 2) source limit points indices templates tasks time n (N := ZFSet.omega)
  have atStamp (n : Nat) :
      fields.value 0 (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).D ∧
      fields.value 1 (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).rD ∧
      fields.value 2 (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).μD ∧
      fields.value 3 (compressionStamp base n) = graphRestriction
        (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth := by
    have hs := ZFSet.mem_insert_of_mem births.limit (births.times.stamp_mem_limit n)
    have exactFields := state.prefixFields_stamp data births heights prior.toHistory n
    exact ⟨(values 0 _ hs).trans exactFields.1, (values 1 _ hs).trans exactFields.2.1,
      (values 2 _ hs).trans exactFields.2.2.1, (values 3 _ hs).trans exactFields.2.2.2.1⟩
  have atLimit : fields.value 0 births.limit = data.fields 0 ∧
      fields.value 1 births.limit = data.fields 1 ∧ fields.value 2 births.limit = data.fields 2 ∧
      fields.value 3 births.limit = births.birth := by
    have hs := ZFSet.mem_insert births.limit births.limit
    have exactFields := state.prefixFields_limit data births heights prior.toHistory
    exact ⟨(values 0 _ hs).trans exactFields.1, (values 1 _ hs).trans exactFields.2.1,
      (values 2 _ hs).trans exactFields.2.2.1, (values 3 _ hs).trans exactFields.2.2.2.1⟩
  have finite (n : Nat) (t : ZFSet.{u}) (bound : t = compressionStamp base n ∨ t ∈ compressionStamp base n) :
      ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 (compressionStamp base n)) (fields.value 1 (compressionStamp base n))
        (fields.value 2 (compressionStamp base n)) (fields.value 3 (compressionStamp base n)) t ZFSet.omega z ∧ ZFSet.rank z < o := by
    rw [(atStamp n).1, (atStamp n).2.1, (atStamp n).2.2.1, (atStamp n).2.2.2]
    have cases : (t ∈ base ∨ t = base) ∨ ∃ j, j ≤ n ∧ t = compressionStamp base j := by
      rcases bound with equal | before
      · exact Or.inr ⟨n, Nat.le_refl n, equal⟩
      · rcases (mem_compressionStamp_iff base t n).1 before with old | same | ⟨j, earlier, equal⟩
        · exact Or.inl (Or.inl old)
        · exact Or.inl (Or.inr same)
        · exact Or.inr ⟨j, Nat.le_of_lt earlier, equal⟩
    rcases cases with before | ⟨j, before, rfl⟩
    · obtain ⟨z, hz, code, rank⟩ := oldWitness t before
      exact state.exists_priorWitness_to_finite_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
        (n + 1) before hz rank code
    · obtain ⟨z, hz, rank, code⟩ := incoming j
      exact state.exists_birthWitness_to_finite_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
        (j + 1) (n + 1) (Nat.add_le_add_right before 1)
        ((compressionStamp_mem_iff base j (j + 1)).2 (Nat.lt_succ_self j)) hz rank code
  have terminal (t : ZFSet.{u}) (bound : t = births.limit ∨ t ∈ births.limit) :
      ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 births.limit) (fields.value 1 births.limit)
        (fields.value 2 births.limit) (fields.value 3 births.limit) t ZFSet.omega z ∧ ZFSet.rank z < o := by
    rw [atLimit.1, atLimit.2.1, atLimit.2.2.1, atLimit.2.2.2]
    rcases bound with rfl | before
    · exact state.exists_limitWitness_rank_lt data births pairing limit
    · rcases (births.times.mem_limit_iff t).1 before with old | same | ⟨j, rfl⟩
      · obtain ⟨z, hz, code, rank⟩ := oldWitness t (Or.inl old)
        exact state.exists_priorWitness_to_union_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
          (Or.inl old) hz rank code
      · obtain ⟨z, hz, code, rank⟩ := oldWitness t (Or.inr same)
        exact state.exists_priorWitness_to_union_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
          (Or.inr same) hz rank code
      · obtain ⟨z, hz, rank, code⟩ := incoming j
        exact state.exists_birthWitness_to_union_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
          (j + 1) ((compressionStamp_mem_iff base j (j + 1)).2 (Nat.lt_succ_self j)) hz rank code
  intro cutoff hc t _ bound
  rcases ZFSet.mem_insert_iff.1 hc with rfl | before
  · exact terminal t bound
  · rcases (births.times.mem_limit_iff cutoff).1 before with oldTime | same | ⟨n, rfl⟩
    · exact state.exists_prefixOldRankedWitness data births heights prior fields hBase values priorRank (Or.inl oldTime) bound
    · exact state.exists_prefixOldRankedWitness data births heights prior fields hBase values priorRank (Or.inr same) bound
    · exact finite n t bound

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionOrigin
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters C Q qlt original Targets Separators base old T0 : ZFSet.{u}}
variable {history : GroundChronologicalHistory M T0 C Q qlt}
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)
variable (compression : GroundChronologicalCompression M initial I Sources Reps G m one T τ
  P0 C Q qlt original Targets Separators Filters base old T0 history)
variable (prior : GroundSerializedChronology M T0 C Q qlt)

include origin in
theorem exists_rankedRawCompressionFields
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) (hBase : base ∈ T0)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (priorRank : ZFSet.rank prior.code < o)
    (indices : ZFSet.rank initial.J < o) (tasks : ZFSet.rank I < o)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 initial)
    (initialDomain : initial.D = P0) (initialOrder : initial.rD = r0) (initialMeet : initial.μD = μ0)
    (priorSpace : history.space base = P0) (priorOrder : history.order base = r0)
    (priorMeet : history.meetGraph base = μ0) (priorBirth : history.birth base = old)
    (agreement : ∀ j s, s ∈ T0 → prior.fields.value j s = history.fieldValue j s) :
    ∃ fields : GroundChronologyFields M
        (insert compression.born.births.limit compression.born.births.limit),
      fields.code ∈ M.sets ∧
      ChronologyCoreCode (insert compression.born.births.limit compression.born.births.limit)
        fields.bound C Q qlt fields.graph ∧
      (∀ j s, s ∈ insert compression.born.births.limit compression.born.births.limit →
        fields.value j s = compression.history.fieldValue j s) ∧
      (∀ s ∈ insert compression.born.births.limit compression.born.births.limit,
        ∀ t ∈ insert compression.born.births.limit compression.born.births.limit,
        t = s ∨ t ∈ s → ∃ z ∈ M.sets, ZFSet.rank z < o ∧
          GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
            (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z) := by
  obtain ⟨seed, state, equal⟩ := origin
  cases equal
  let data := compression.born.profiled.heighted.completion.algebra.union
  let births := compression.born.births
  let heights := compression.born.profiled.heighted.heights
  obtain ⟨fields, ground, core, values⟩ := state.exists_groundPrefixFields data births heights
    prior.fields prior.toHistory pairing unions powers separation collection infinite
    hI hSources hReps hG hT prior.ordinal hBase
      (fun j _ _ => Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j)
  have ranked := state.prefix_rankedRawWitnesses data births heights prior fields
    pairing unions powers separation hI hSources hReps hG hT hBase limit priorRank indices tasks
    constant initialDomain initialOrder initialMeet
    ((agreement 0 base hBase).trans priorSpace) ((agreement 1 base hBase).trans priorOrder)
    ((agreement 2 base hBase).trans priorMeet) ((agreement 3 base hBase).trans priorBirth) values
  refine ⟨fields, ground, core, ?_, ?_⟩
  · intro j s hs
    rw [values j s hs]
    have oldValue (a : ZFSet.{u}) (before : a ∈ base ∨ a = base) :
        (state.prefixFields data births heights prior.toHistory).fieldValue j a =
          compression.history.fieldValue j a := by
      have ha : a ∈ T0 := before.elim (fun h => prior.ordinal.1 base hBase a h) (fun h => h.symm ▸ hBase)
      have left := state.prefixFields_old data births heights prior.toHistory before
      have right := compression.old_values a before
      have eLeft : (state.prefixFields data births heights prior.toHistory).fieldValue j a =
          prior.fields.value j a :=
        Fin.cases left.1 (Fin.cases left.2.1 (Fin.cases left.2.2.1
          (Fin.cases left.2.2.2.1 (Fin.cases left.2.2.2.2 (fun i => Fin.elim0 i))))) j
      have eRight : compression.history.fieldValue j a = history.fieldValue j a :=
        Fin.cases right.1 (Fin.cases right.2.1 (Fin.cases right.2.2.1
          (Fin.cases right.2.2.2.1 (Fin.cases right.2.2.2.2 (fun i => Fin.elim0 i))))) j
      exact eLeft.trans ((agreement j a ha).trans eRight.symm)
    rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
    · have left := state.prefixFields_limit data births heights prior.toHistory
      have right := compression.limit_values
      exact Fin.cases (left.1.trans right.1.symm)
        (Fin.cases (left.2.1.trans right.2.1.symm) (Fin.cases (left.2.2.1.trans right.2.2.1.symm)
          (Fin.cases (left.2.2.2.1.trans right.2.2.2.1.symm)
            (Fin.cases (left.2.2.2.2.trans right.2.2.2.2.symm) (fun i => Fin.elim0 i))))) j
    · rcases (births.times.mem_limit_iff s).1 hs with before | equal | ⟨n, rfl⟩
      · exact oldValue s (Or.inl before)
      · exact oldValue s (Or.inr equal)
      · have left := state.prefixFields_stamp data births heights prior.toHistory n
        have right := compression.stamp_values n
        exact Fin.cases (left.1.trans right.1.symm)
          (Fin.cases (left.2.1.trans right.2.1.symm) (Fin.cases (left.2.2.1.trans right.2.2.1.symm)
            (Fin.cases (left.2.2.2.1.trans right.2.2.2.1.symm)
              (Fin.cases (left.2.2.2.2.trans right.2.2.2.2.symm) (fun i => Fin.elim0 i))))) j

  · intro s hs t ht earlier
    obtain ⟨z, hz, code, rank⟩ := ranked s hs t ht earlier
    exact ⟨z, hz, rank, code⟩

end PartitionPilot.Forcing.GroundCompressionOrigin

end OAI
