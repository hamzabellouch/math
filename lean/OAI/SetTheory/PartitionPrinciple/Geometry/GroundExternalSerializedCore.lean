import OAI.SetTheory.PartitionPrinciple.Transfinite.CodedMainPrefixSystems

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
open scoped ZFSet
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

noncomputable abbrev serializedFields : GroundChronologyFields M (insert births.limit births.limit) :=
  births.groundChronologyFields heights prior.fields data group action
    pairing unions powers separation infinite hG hP0 prior.ordinal hOld

local notation "fields" => births.serializedFields heights prior data group action
  pairing unions powers separation infinite hG hP0 hOld

include births heights prior data group action pairing unions powers separation infinite hG hP0 hOld

theorem serializedFields_value (j : Fin 5) {s : ZFSet.{u}}
    (hs : s ∈ insert births.limit births.limit) :
    (fields).value j s = (births.chronologyFields heights prior.toHistory).fieldValue j s := by
  apply births.groundChronologyFields_values heights prior.fields data group action
    pairing unions powers separation infinite hG hP0 prior.ordinal hOld prior.toHistory ?_ j hs
  intro k a _
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) k

theorem serializedFields_core :
    ChronologyCoreCode (insert births.limit births.limit) (fields).bound C D rD (fields).graph := by
  refine ⟨(fields).function, ?_⟩
  intro s hs L r μ birth height eL er eμ eb eh
  have v (j : Fin 5) := births.serializedFields_value heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j hs
  have laws := births.chronologyFields_stage_laws heights prior.toHistory data group action
    pairing unions powers separation infinite hG hP0 prior.ordinal hOld hs
  rw [← (fields).value_eq_of_entry 0 eL, ← (fields).value_eq_of_entry 1 er,
    ← (fields).value_eq_of_entry 2 eμ, ← (fields).value_eq_of_entry 3 eb,
    ← (fields).value_eq_of_entry 4 eh, v 0, v 1, v 2, v 3, v 4]
  exact ⟨laws.1, laws.2.1, laws.2.2.1, laws.2.2.2.1, laws.2.2.2.2⟩

theorem serializedFields_old (j : Fin 5) {s : ZFSet.{u}}
    (before : s ∈ oldTimes ∨ s = oldTimes) :
    (fields).value j s = prior.fields.value j s := by
  have hs : s ∈ insert births.limit births.limit := ZFSet.mem_insert_of_mem _
    ((births.times.mem_limit_iff s).2 (before.elim Or.inl (fun h => Or.inr (Or.inl h))))
  rw [births.serializedFields_value heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j hs]
  have values := births.chronologyFields_old heights prior.toHistory before
  exact Fin.cases values.1 (Fin.cases values.2.1 (Fin.cases values.2.2.1
    (Fin.cases values.2.2.2.1 (Fin.cases values.2.2.2.2 (fun i => Fin.elim0 i))))) j

theorem serializedFields_stamp (j : Fin 5) (n : Nat) :
    (fields).value j (compressionStamp oldTimes n) = births.cutoffField heights j n := by
  rw [births.serializedFields_value heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j
      (ZFSet.mem_insert_of_mem _ (births.times.stamp_mem_limit n))]
  have values := births.chronologyFields_stamp heights prior.toHistory n
  exact Fin.cases values.1 (Fin.cases values.2.1 (Fin.cases values.2.2.1
    (Fin.cases values.2.2.2.1 (Fin.cases values.2.2.2.2 (fun i => Fin.elim0 i))))) j

theorem serializedFields_limit (j : Fin 5) :
    (fields).value j births.limit = births.terminalField heights j := by
  rw [births.serializedFields_value heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j (ZFSet.mem_insert _ _)]
  have values := births.chronologyFields_limit heights prior.toHistory
  exact Fin.cases values.1 (Fin.cases values.2.1 (Fin.cases values.2.2.1
    (Fin.cases values.2.2.2.1 (Fin.cases values.2.2.2.2 (fun i => Fin.elim0 i))))) j

theorem serializedFields_old_entries (j : Fin 5) {s : ZFSet.{u}}
    (before : s ∈ oldTimes ∨ s = oldTimes) (y : ZFSet.{u}) :
    ZFSet.pair s y ∈ (fields).graph j ↔ ZFSet.pair s y ∈ prior.fields.graph j := by
  have oldValue := births.serializedFields_old heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j before
  have hs : s ∈ T0 := before.elim (fun h => prior.ordinal.1 oldTimes hOld s h) (fun h => h.symm ▸ hOld)
  have hs' : s ∈ insert births.limit births.limit := ZFSet.mem_insert_of_mem _
    ((births.times.mem_limit_iff s).2 (before.elim Or.inl (fun h => Or.inr (Or.inl h))))
  constructor
  · intro entry
    have equal := oldValue.symm.trans ((fields).value_eq_of_entry j entry)
    exact equal ▸ prior.fields.value_entry j hs
  · intro entry
    have equal := oldValue.trans (prior.fields.value_eq_of_entry j entry)
    exact equal ▸ (fields).value_entry j hs'

end PartitionPilot.Forcing.GroundExternalBirthData

end

end OAI
