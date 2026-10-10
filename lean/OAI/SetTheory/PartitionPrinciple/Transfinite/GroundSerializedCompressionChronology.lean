import OAI.SetTheory.PartitionPrinciple.Forcing.GroundChronologyWitnessSelection
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRankedCompressionFieldsTransport

namespace OAI

section

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
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable (hBase : base ∈ T0)
variable (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
variable (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
variable (initialMeet : state.data.μD = μ0)
variable (priorSpace : prior.fields.value 0 base = P0) (priorOrder : prior.fields.value 1 base = r0)
variable (priorMeet : prior.fields.value 2 base = μ0) (priorBirth : prior.fields.value 3 base = old)
include pairing unions powers separation collection infinite choice hI hSources hReps hG hT
  hBase constant initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth

theorem exists_serializedPrefix_of_fields
    (fields : GroundChronologyFields M (insert births.limit births.limit))
    (core : ChronologyCoreCode (insert births.limit births.limit) fields.bound C Q qlt fields.graph)
    (values : ∀ j s, s ∈ insert births.limit births.limit →
      fields.value j s = (state.prefixFields data births heights prior.toHistory).fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert births.limit births.limit) C Q qlt,
      serial.fields = fields ∧ serial.code ∈ M.sets :=
  fields.exists_serializedChronology pairing unions powers separation collection choice infinite core
    (state.prefix_rawWitnesses data births heights prior fields pairing unions powers separation
      hI hSources hReps hG hT hBase constant initialDomain initialOrder initialMeet
      priorSpace priorOrder priorMeet priorBirth values)
    (ordinalSetProperty_succ births.times.ordinal)

theorem exists_serializedPrefix :
    ∃ serial : GroundSerializedChronology M (insert births.limit births.limit) C Q qlt,
      serial.code ∈ M.sets ∧ ∀ j s, s ∈ insert births.limit births.limit →
        serial.fields.value j s = (state.prefixFields data births heights prior.toHistory).fieldValue j s := by
  have agreement : ∀ j s, s ∈ T0 → prior.fields.value j s = prior.toHistory.fieldValue j s := by
    intro j s _
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j
  obtain ⟨fields, _, core, values⟩ := state.exists_groundPrefixFields data births heights prior.fields prior.toHistory
    pairing unions powers separation collection infinite hI hSources hReps hG hT prior.ordinal hBase agreement
  obtain ⟨serial, same, ground⟩ := state.exists_serializedPrefix_of_fields data births heights prior
    pairing unions powers separation collection infinite choice hI hSources hReps hG hT hBase
    constant initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth fields core values
  exact ⟨serial, ground, same.symm ▸ values⟩

end PartitionPilot.Forcing.GroundCompressionState

end

end OAI
