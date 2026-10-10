import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundSerializedCompressionChronology

namespace OAI

section

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
theorem exists_serializedCompression
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) (hBase : base ∈ T0)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 initial)
    (initialDomain : initial.D = P0) (initialOrder : initial.rD = r0) (initialMeet : initial.μD = μ0)
    (priorSpace : history.space base = P0) (priorOrder : history.order base = r0)
    (priorMeet : history.meetGraph base = μ0) (priorBirth : history.birth base = old)
    (agreement : ∀ j s, s ∈ T0 → prior.fields.value j s = history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M
        (insert compression.born.births.limit compression.born.births.limit) C Q qlt,
      serial.code ∈ M.sets ∧ ∀ j s, s ∈ insert compression.born.births.limit compression.born.births.limit →
        serial.fields.value j s = compression.history.fieldValue j s := by
  obtain ⟨seed, state, equal⟩ := origin
  cases equal
  let data := compression.born.profiled.heighted.completion.algebra.union
  let births := compression.born.births
  let heights := compression.born.profiled.heighted.heights
  obtain ⟨serial, ground, values⟩ := state.exists_serializedPrefix data births heights prior
    pairing unions powers separation collection infinite choice hI hSources hReps hG hT hBase
    constant initialDomain initialOrder initialMeet
    ((agreement 0 base hBase).trans priorSpace) ((agreement 1 base hBase).trans priorOrder)
    ((agreement 2 base hBase).trans priorMeet) ((agreement 3 base hBase).trans priorBirth)
  refine ⟨serial, ground, ?_⟩
  intro j s hs
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

end PartitionPilot.Forcing.GroundCompressionOrigin

end

end OAI
