import OAI.SetTheory.PartitionPrinciple.Forcing.GroundChronologyWitnessSelection
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundExternalLayerWitnessRanks
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainPrefixLimitLayerWitnesses
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalSerializedCore

namespace OAI



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundSerializedChronology M T0 C D rD)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (hOld : oldTimes ∈ T0)

local notation "fields" => births.serializedFields heights prior data group action
  pairing unions powers separation infinite hG hP0 hOld
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
include births heights prior data group action pairing unions powers separation infinite hG hP0 hOld

theorem serialized_old_raw_witness {s t : ZFSet.{u}}
    (before : s ∈ oldTimes ∨ s = oldTimes) (earlier : t = s ∨ t ∈ s) :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
      ((fields).value 0 s) ((fields).value 1 s) ((fields).value 2 s) ((fields).value 3 s) t ZFSet.omega z := by
  have baseOrdinal := ordinalSetProperty_member births.times.ordinal births.times.base_mem_limit
  have hs : s ∈ T0 := before.elim (fun h => prior.ordinal.1 oldTimes hOld s h) (fun h => h.symm ▸ hOld)
  have ht : t ∈ T0 := earlier.elim (fun h => h.symm ▸ hs) (fun h => prior.ordinal.1 s hs t h)
  have oldTime : t ∈ oldTimes ∨ t = oldTimes := by
    rcases earlier with rfl | h
    · exact before
    · exact Or.inl (before.elim (fun member => baseOrdinal.1 s member t h) (fun equal => equal ▸ h))
  have agree (j : Fin 5) (a : ZFSet.{u}) (ha : a ∈ t) (y : ZFSet.{u}) :
      ZFSet.pair a y ∈ prior.fields.graph j ↔ ZFSet.pair a y ∈ (fields).graph j := by
    have earlierBase : a ∈ oldTimes := oldTime.elim
      (fun member => baseOrdinal.1 t member a ha) (fun equal => equal ▸ ha)
    exact (births.serializedFields_old_entries heights prior data group action
      pairing unions powers separation infinite hG hP0 hOld j (Or.inl earlierBase) y).symm
  have code := (prior.layer_code s hs t ht earlier _ (prior.layerWitness_entry hs ht earlier)).congr_source_entries
    (agree 0) (agree 1) (agree 2)
  refine ⟨prior.layerWitness s t, prior.layerWitness_ground s t, ?_⟩
  rw [births.serializedFields_old heights prior data group action pairing unions powers separation infinite hG hP0 hOld 0 before,
    births.serializedFields_old heights prior data group action pairing unions powers separation infinite hG hP0 hOld 1 before,
    births.serializedFields_old heights prior data group action pairing unions powers separation infinite hG hP0 hOld 2 before,
    births.serializedFields_old heights prior data group action pairing unions powers separation infinite hG hP0 hOld 3 before]
  exact code

variable (source : prior.fields.value 0 oldTimes = completion.algebra.union.fields 0 ∧
  prior.fields.value 1 oldTimes = completion.algebra.union.fields 1 ∧
  prior.fields.value 2 oldTimes = completion.algebra.union.fields 2 ∧
  prior.fields.value 3 oldTimes = oldBirth)
include source

theorem serialized_base_entries :
    ZFSet.pair oldTimes U ∈ (fields).graph 0 ∧
      ZFSet.pair oldTimes (completion.algebra.union.fields 1) ∈ (fields).graph 1 ∧
      ZFSet.pair oldTimes (completion.algebra.union.fields 2) ∈ (fields).graph 2 := by
  have hs := ZFSet.mem_insert_of_mem births.limit births.times.base_mem_limit
  have values (j : Fin 5) := births.serializedFields_old heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j (Or.inr rfl)
  exact ⟨(values 0 |>.trans source.1) ▸ (fields).value_entry 0 hs,
    (values 1 |>.trans source.2.1) ▸ (fields).value_entry 1 hs,
    (values 2 |>.trans source.2.2.1) ▸ (fields).value_entry 2 hs⟩

theorem serialized_base_raw_witness (t : ZFSet.{u}) (oldTime : t ∈ oldTimes ∨ t = oldTimes) :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
      U (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) oldBirth t ZFSet.omega z := by
  obtain ⟨z, hz, code⟩ := births.serialized_old_raw_witness heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld (Or.inr rfl) oldTime.symm
  refine ⟨z, hz, ?_⟩
  have values (j : Fin 5) := births.serializedFields_old heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j (Or.inr rfl)
  simpa only [values 0, values 1, values 2, values 3, source.1, source.2.1, source.2.2.1, source.2.2.2] using code

theorem serialized_finite_raw_witness (n : Nat) (t : ZFSet.{u})
    (bound : t = compressionStamp oldTimes n ∨ t ∈ compressionStamp oldTimes n) :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
      ((fields).value 0 (compressionStamp oldTimes n)) ((fields).value 1 (compressionStamp oldTimes n))
      ((fields).value 2 (compressionStamp oldTimes n)) ((fields).value 3 (compressionStamp oldTimes n)) t ZFSet.omega z := by
  rw [births.serializedFields_stamp heights prior data group action pairing unions powers separation infinite hG hP0 hOld 0 n,
    births.serializedFields_stamp heights prior data group action pairing unions powers separation infinite hG hP0 hOld 1 n,
    births.serializedFields_stamp heights prior data group action pairing unions powers separation infinite hG hP0 hOld 2 n,
    births.serializedFields_stamp heights prior data group action pairing unions powers separation infinite hG hP0 hOld 3 n]
  change ∃ z ∈ M.sets, GrowthLayerWitnessCode _ _ _ (births.cutoff n)
    (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) t ZFSet.omega z
  have sources := births.serialized_base_entries heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld source
  have fresh (k : Nat) (before : k ≤ n) := births.cutoffLayerWitness_spec data group action
    pairing unions powers separation infinite hG hP0
    ⟨_, (fields).function 0⟩ ⟨_, (fields).function 1⟩ ⟨_, (fields).function 2⟩ sources k n before (N := ZFSet.omega)
  have original (a : ZFSet.{u}) (oldTime : a ∈ oldTimes ∨ a = oldTimes) :
      ∃ z ∈ M.sets, GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
        (births.cutoff n) (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) a ZFSet.omega z := by
    obtain ⟨z, hz, code⟩ := births.serialized_base_raw_witness heights prior data group action
      pairing unions powers separation infinite hG hP0 hOld source a oldTime
    exact births.rawCutoffPriorWitness data group action pairing unions powers separation infinite hG hP0
      ((fields).graph_ground 0) (M.omega_mem separation infinite) hz code oldTime n
  rcases bound with rfl | before
  · exact ⟨_, (fresh n (Nat.le_refl n)).1, (fresh n (Nat.le_refl n)).2⟩
  · rcases (mem_compressionStamp_iff oldTimes t n).1 before with old | same | ⟨k, earlier, rfl⟩
    · exact original t (Or.inl old)
    · exact original t (Or.inr same)
    · exact ⟨_, (fresh k (Nat.le_of_lt earlier)).1, (fresh k (Nat.le_of_lt earlier)).2⟩

theorem serialized_limit_raw_witness (t : ZFSet.{u}) (bound : t = births.limit ∨ t ∈ births.limit) :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
      ((fields).value 0 births.limit) ((fields).value 1 births.limit)
      ((fields).value 2 births.limit) ((fields).value 3 births.limit) t ZFSet.omega z := by
  rw [births.serializedFields_limit heights prior data group action pairing unions powers separation infinite hG hP0 hOld 0,
    births.serializedFields_limit heights prior data group action pairing unions powers separation infinite hG hP0 hOld 1,
    births.serializedFields_limit heights prior data group action pairing unions powers separation infinite hG hP0 hOld 2,
    births.serializedFields_limit heights prior data group action pairing unions powers separation infinite hG hP0 hOld 3]
  change ∃ z ∈ M.sets, GrowthLayerWitnessCode _ _ _ B
    (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0) births.birth t ZFSet.omega z
  have sources := births.serialized_base_entries heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld source
  have fresh (k : Nat) := births.layerWitness_spec data group action
    pairing unions powers separation infinite hG hP0
    ⟨_, (fields).function 0⟩ ⟨_, (fields).function 1⟩ ⟨_, (fields).function 2⟩ sources k (N := ZFSet.omega)
  have original (a : ZFSet.{u}) (oldTime : a ∈ oldTimes ∨ a = oldTimes) :
      ∃ z ∈ M.sets, GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
        B (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0) births.birth a ZFSet.omega z := by
    obtain ⟨z, hz, code⟩ := births.serialized_base_raw_witness heights prior data group action
      pairing unions powers separation infinite hG hP0 hOld source a oldTime
    exact births.rawPriorWitness data group action pairing unions powers separation infinite hG hP0
      ((fields).graph_ground 0) (M.omega_mem separation infinite) hz code oldTime
  rcases bound with rfl | before
  · have hEmpty := M.empty_mem ⟨births.limit, births.limit_ground⟩
    refine ⟨countableLayerWitness ∅ ∅, M.countableLayerWitness_mem pairing hEmpty hEmpty,
      Or.inl ⟨∅, ∅, rfl, ⟨InjectionCode.empty ZFSet.omega, ?_⟩⟩⟩
    intro x _ born
    exact (births.no_limit_birth x born).elim
  · rcases (births.times.mem_limit_iff t).1 before with old | same | ⟨k, rfl⟩
    · exact original t (Or.inl old)
    · exact original t (Or.inr same)
    · exact ⟨_, (fresh k).1, (fresh k).2⟩

theorem serialized_all_raw_witnesses :
    ∀ s ∈ insert births.limit births.limit, ∀ t ∈ insert births.limit births.limit,
      t = s ∨ t ∈ s → ∃ z ∈ M.sets,
        GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
          ((fields).value 0 s) ((fields).value 1 s) ((fields).value 2 s) ((fields).value 3 s) t ZFSet.omega z := by
  intro s hs t _ bound
  rcases ZFSet.mem_insert_iff.1 hs with rfl | before
  · exact births.serialized_limit_raw_witness heights prior data group action
      pairing unions powers separation infinite hG hP0 hOld source t bound
  · rcases (births.times.mem_limit_iff s).1 before with old | same | ⟨n, rfl⟩
    · exact births.serialized_old_raw_witness heights prior data group action
        pairing unions powers separation infinite hG hP0 hOld (Or.inl old) bound
    · exact births.serialized_old_raw_witness heights prior data group action
        pairing unions powers separation infinite hG hP0 hOld (Or.inr same) bound
    · exact births.serialized_finite_raw_witness heights prior data group action
        pairing unions powers separation infinite hG hP0 hOld source n t bound

end PartitionPilot.Forcing.GroundExternalBirthData




namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundSerializedChronology M T0 C D rD)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (hOld : oldTimes ∈ T0)
local notation "fields" => births.serializedFields heights prior data group action
  pairing unions powers separation infinite hG hP0 hOld
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
include births heights prior data group action pairing unions powers separation infinite hG hP0 hOld

theorem ranked_prior_source_entries {t : ZFSet.{u}}
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) (j : Fin 5) :
    ∀ a ∈ t, ∀ y, ZFSet.pair a y ∈ prior.fields.graph j ↔ ZFSet.pair a y ∈ (fields).graph j := by
  intro a ha y
  have baseOrdinal := ordinalSetProperty_member births.times.ordinal births.times.base_mem_limit
  have earlier : a ∈ oldTimes := oldTime.elim
    (fun member => baseOrdinal.1 t member a ha) (fun equal => equal ▸ ha)
  exact (births.serializedFields_old_entries heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j (Or.inl earlier) y).symm

variable {o : Ordinal.{u}} (priorRank : ZFSet.rank prior.code < o)
include priorRank

theorem serialized_old_ranked_raw_witness {s t : ZFSet.{u}}
    (before : s ∈ oldTimes ∨ s = oldTimes) (earlier : t = s ∨ t ∈ s) :
    ∃ z ∈ M.sets, ZFSet.rank z < o ∧
      GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
        ((fields).value 0 s) ((fields).value 1 s) ((fields).value 2 s) ((fields).value 3 s) t ZFSet.omega z := by
  have baseOrdinal := ordinalSetProperty_member births.times.ordinal births.times.base_mem_limit
  have hs : s ∈ T0 := before.elim (fun h => prior.ordinal.1 oldTimes hOld s h) (fun h => h.symm ▸ hOld)
  have ht : t ∈ T0 := earlier.elim (fun h => h.symm ▸ hs) (fun h => prior.ordinal.1 s hs t h)
  have oldTime : t ∈ oldTimes ∨ t = oldTimes := by
    rcases earlier with rfl | h
    · exact before
    · exact Or.inl (before.elim (fun member => baseOrdinal.1 s member t h) (fun equal => equal ▸ h))
  have agree (j : Fin 5) := births.ranked_prior_source_entries heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld oldTime j
  have code := (prior.layer_code s hs t ht earlier _ (prior.layerWitness_entry hs ht earlier)).congr_source_entries
    (agree 0) (agree 1) (agree 2)
  refine ⟨prior.layerWitness s t, prior.layerWitness_ground s t,
    (prior.layerWitness_rank_lt_code hs ht earlier).trans priorRank, ?_⟩
  rw [births.serializedFields_old heights prior data group action pairing unions powers separation infinite hG hP0 hOld 0 before,
    births.serializedFields_old heights prior data group action pairing unions powers separation infinite hG hP0 hOld 1 before,
    births.serializedFields_old heights prior data group action pairing unions powers separation infinite hG hP0 hOld 2 before,
    births.serializedFields_old heights prior data group action pairing unions powers separation infinite hG hP0 hOld 3 before]
  exact code

variable (source : prior.fields.value 0 oldTimes = completion.algebra.union.fields 0 ∧
  prior.fields.value 1 oldTimes = completion.algebra.union.fields 1 ∧
  prior.fields.value 2 oldTimes = completion.algebra.union.fields 2 ∧
  prior.fields.value 3 oldTimes = oldBirth)
include source

omit births heights data group action pairing unions powers separation infinite hG hP0 in
theorem serialized_terminal_prior_ranked_witness (t : ZFSet.{u})
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) :
    ∃ z ∈ M.sets, ZFSet.rank z < o ∧
      GrowthLayerWitnessCode (prior.fields.graph 0) (prior.fields.graph 1) (prior.fields.graph 2)
        U (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) oldBirth t ZFSet.omega z := by
  have ht : t ∈ T0 := oldTime.elim
    (fun h => prior.ordinal.1 oldTimes hOld t h) (fun h => h.symm ▸ hOld)
  have code := prior.layer_code oldTimes hOld t ht oldTime.symm _
    (prior.layerWitness_entry hOld ht oldTime.symm)
  refine ⟨prior.layerWitness oldTimes t, prior.layerWitness_ground oldTimes t,
    (prior.layerWitness_rank_lt_code hOld ht oldTime.symm).trans priorRank, ?_⟩
  simpa only [source.1, source.2.1, source.2.2.1, source.2.2.2] using code

theorem serialized_all_ranked_raw_witnesses (limit : Order.IsSuccLimit o)
    (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
    (points : ZFSet.rank P0 < o) (actors : ZFSet.rank G < o) :
    ∀ s ∈ insert births.limit births.limit, ∀ t ∈ insert births.limit births.limit,
      t = s ∨ t ∈ s → ∃ z ∈ M.sets, ZFSet.rank z < o ∧
        GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
          ((fields).value 0 s) ((fields).value 1 s) ((fields).value 2 s) ((fields).value 3 s) t ZFSet.omega z := by
  have completed : ZFSet.rank U < o := by
    rw [← source.1]
    exact (prior.fieldValue_rank_lt_code 0 hOld).trans priorRank
  have time : ZFSet.rank oldTimes < o :=
    ((ZFSet.rank_lt_of_mem hOld).trans_le prior.time_rank_le_code).trans priorRank
  have carrier := completion.externalPointCarrier_rank_lt_of_inputs limit r0 μ0 A0
    omega indices points actors completed
  have sources := births.serialized_base_entries heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld source
  have old (s t : ZFSet.{u}) (before : s ∈ oldTimes ∨ s = oldTimes) (earlier : t = s ∨ t ∈ s) :=
    births.serialized_old_ranked_raw_witness heights prior data group action
      pairing unions powers separation infinite hG hP0 hOld priorRank before earlier
  have base (t : ZFSet.{u}) (oldTime : t ∈ oldTimes ∨ t = oldTimes) :=
    serialized_terminal_prior_ranked_witness prior hOld priorRank source t oldTime
  have finite (n : Nat) (t : ZFSet.{u}) (bound : t = compressionStamp oldTimes n ∨ t ∈ compressionStamp oldTimes n) :
      ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode
        ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
        ((fields).value 0 (compressionStamp oldTimes n)) ((fields).value 1 (compressionStamp oldTimes n))
        ((fields).value 2 (compressionStamp oldTimes n)) ((fields).value 3 (compressionStamp oldTimes n)) t ZFSet.omega z := by
    rw [births.serializedFields_stamp heights prior data group action pairing unions powers separation infinite hG hP0 hOld 0 n,
      births.serializedFields_stamp heights prior data group action pairing unions powers separation infinite hG hP0 hOld 1 n,
      births.serializedFields_stamp heights prior data group action pairing unions powers separation infinite hG hP0 hOld 2 n,
      births.serializedFields_stamp heights prior data group action pairing unions powers separation infinite hG hP0 hOld 3 n]
    change ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode _ _ _ (births.cutoff n)
      (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) t ZFSet.omega z
    have fresh (k : Nat) (before : k ≤ n) := births.ranked_cutoffLayerWitness_spec data group action
      pairing unions powers separation infinite hG hP0 limit omega indices points actors completed time
      ⟨_, (fields).function 0⟩ ⟨_, (fields).function 1⟩ ⟨_, (fields).function 2⟩ sources k n before (N := ZFSet.omega)
    have original (a : ZFSet.{u}) (oldTime : a ∈ oldTimes ∨ a = oldTimes) :
        ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
          (births.cutoff n) (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) a ZFSet.omega z := by
      obtain ⟨z, hz, rank, code⟩ := base a oldTime
      obtain ⟨z', hz', rank', code'⟩ := births.ranked_rawCutoffPriorWitness data group action
        pairing unions powers separation infinite hG hP0 (prior.fields.graph_ground 0)
        (M.omega_mem separation infinite) hz code oldTime n limit rank
        ((prior.fieldGraph_rank_le_code 0).trans_lt priorRank) carrier omega
      have agree (j : Fin 5) := births.ranked_prior_source_entries heights prior data group action
        pairing unions powers separation infinite hG hP0 hOld oldTime j
      exact ⟨z', hz', rank', code'.congr_source_entries (agree 0) (agree 1) (agree 2)⟩
    rcases bound with rfl | before
    · exact ⟨_, fresh n (Nat.le_refl n)⟩
    · rcases (mem_compressionStamp_iff oldTimes t n).1 before with h | h | ⟨k, earlier, rfl⟩
      · exact original t (Or.inl h)
      · exact original t (Or.inr h)
      · exact ⟨_, fresh k (Nat.le_of_lt earlier)⟩
  have terminal (t : ZFSet.{u}) (bound : t = births.limit ∨ t ∈ births.limit) :
      ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode
        ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
        ((fields).value 0 births.limit) ((fields).value 1 births.limit)
        ((fields).value 2 births.limit) ((fields).value 3 births.limit) t ZFSet.omega z := by
    rw [births.serializedFields_limit heights prior data group action pairing unions powers separation infinite hG hP0 hOld 0,
      births.serializedFields_limit heights prior data group action pairing unions powers separation infinite hG hP0 hOld 1,
      births.serializedFields_limit heights prior data group action pairing unions powers separation infinite hG hP0 hOld 2,
      births.serializedFields_limit heights prior data group action pairing unions powers separation infinite hG hP0 hOld 3]
    change ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode _ _ _ B
      (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0) births.birth t ZFSet.omega z
    have fresh (k : Nat) := births.ranked_layerWitness_spec data group action
      pairing unions powers separation infinite hG hP0 limit omega indices points actors completed time
      ⟨_, (fields).function 0⟩ ⟨_, (fields).function 1⟩ ⟨_, (fields).function 2⟩ sources k (N := ZFSet.omega)
    have original (a : ZFSet.{u}) (oldTime : a ∈ oldTimes ∨ a = oldTimes) :
        ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
          B (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0) births.birth a ZFSet.omega z := by
      obtain ⟨z, hz, rank, code⟩ := base a oldTime
      obtain ⟨z', hz', rank', code'⟩ := births.ranked_rawPriorWitness data group action
        pairing unions powers separation infinite hG hP0 (prior.fields.graph_ground 0)
        (M.omega_mem separation infinite) hz code oldTime limit rank
        ((prior.fieldGraph_rank_le_code 0).trans_lt priorRank) carrier omega
      have agree (j : Fin 5) := births.ranked_prior_source_entries heights prior data group action
        pairing unions powers separation infinite hG hP0 hOld oldTime j
      exact ⟨z', hz', rank', code'.congr_source_entries (agree 0) (agree 1) (agree 2)⟩
    rcases bound with rfl | before
    · have hEmpty := M.empty_mem ⟨births.limit, births.limit_ground⟩
      have emptyRank : ZFSet.rank (∅ : ZFSet.{u}) < o := by simpa only [ZFSet.rank_empty] using limit.pos
      refine ⟨countableLayerWitness ∅ ∅, M.countableLayerWitness_mem pairing hEmpty hEmpty,
        countableLayerWitness_rank_lt limit emptyRank emptyRank,
        Or.inl ⟨∅, ∅, rfl, ⟨InjectionCode.empty ZFSet.omega, ?_⟩⟩⟩
      intro x _ born
      exact (births.no_limit_birth x born).elim
    · rcases (births.times.mem_limit_iff t).1 before with h | h | ⟨k, rfl⟩
      · exact original t (Or.inl h)
      · exact original t (Or.inr h)
      · exact ⟨_, fresh k⟩
  intro s hs t _ bound
  rcases ZFSet.mem_insert_iff.1 hs with rfl | before
  · exact terminal t bound
  · rcases (births.times.mem_limit_iff s).1 before with h | h | ⟨n, rfl⟩
    · exact old s t (Or.inl h) bound
    · exact old s t (Or.inr h) bound
    · exact finite n t bound

end PartitionPilot.Forcing.GroundExternalBirthData



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundSerializedChronology M T0 C D rD)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (hOld : oldTimes ∈ T0)

variable (source : prior.fields.value 0 oldTimes = completion.algebra.union.fields 0 ∧
  prior.fields.value 1 oldTimes = completion.algebra.union.fields 1 ∧
  prior.fields.value 2 oldTimes = completion.algebra.union.fields 2 ∧
  prior.fields.value 3 oldTimes = oldBirth)
variable (collection : CollectionSchema M.sets)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "fields" => births.serializedFields heights prior data group action
  pairing unions powers separation infinite hG hP0 hOld
include births heights prior data group action pairing unions powers separation infinite hG hP0 hOld source collection choice

theorem exists_externalSerializedChronology :
    ∃ serial : GroundSerializedChronology M (insert births.limit births.limit) C D rD,
      serial.fields = fields ∧ serial.code ∈ M.sets ∧
        ∀ j s, s ∈ insert births.limit births.limit →
          serial.fields.value j s = (births.chronologyFields heights prior.toHistory).fieldValue j s := by
  obtain ⟨serial, same, ground⟩ := (fields).exists_serializedChronology
    pairing unions powers separation collection choice infinite
    (births.serializedFields_core heights prior data group action
      pairing unions powers separation infinite hG hP0 hOld)
    (births.serialized_all_raw_witnesses heights prior data group action
      pairing unions powers separation infinite hG hP0 hOld source)
    (ordinalSetProperty_succ births.times.ordinal)
  refine ⟨serial, same, ground, ?_⟩
  intro j s hs
  rw [same]
  exact births.serializedFields_value heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j hs

end PartitionPilot.Forcing.GroundExternalBirthData

end OAI
