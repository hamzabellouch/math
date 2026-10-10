import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialCompressionHistory

namespace OAI

section

namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem successor_coherent : RecursiveStateCoherence I state.data
    (state.data.successor M I Sources Reps G T) := by
  obtain ⟨next, _, _, _, _, _, _, _, _, _, entries, inputs, _⟩ :=
    state.task.exists_groundSuccessor M pairing unions powers separation
      (state.invariant.compatible state.task) hI state.ground.indices state.ground.carrier
      state.ground.order state.ground.spaces state.ground.relations state.ground.meets
      state.ground.anchors state.ground.embeddings state.ground.filters state.ground.separators
      state.ground.maps hSources hReps hG state.ground.action hT
  have result := state.inputs.next_coherent M next entries inputs
  rw [state.inputs.toState_successor M next inputs, state.inputs_toState] at result
  exact result

theorem canonical_iterate_coherent {n k : Nat} (before : n ≤ k) :
    RecursiveStateCoherence I (state.data.iterate M I Sources Reps G T n)
      (state.data.iterate M I Sources Reps G T k) := by
  induction k, before using Nat.le_induction with
  | base =>
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    rw [← equal]
    exact RecursiveStateCoherence.refl current.inputs.maps
  | succ k _ ih =>
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT k
    have step := current.successor_coherent pairing unions powers separation hI hSources hReps hG hT
    rw [equal, ← RecursiveStateData.iterate_succ] at step
    apply ih.trans step
    rw [← equal]
    exact current.inputs.maps

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem successor_accounting (accounted : FiniteCompressionAccounting P0 I Sources τ state.data) :
    FiniteCompressionAccounting P0 I Sources τ (state.data.successor M I Sources Reps G T) := by
  obtain ⟨next, _, _, _, _, _, _, _, _, _, entries, inputs, _⟩ :=
    state.task.exists_groundSuccessor M pairing unions powers separation
      (state.invariant.compatible state.task) hI state.ground.indices state.ground.carrier
      state.ground.order state.ground.spaces state.ground.relations state.ground.meets
      state.ground.anchors state.ground.embeddings state.ground.filters state.ground.separators
      state.ground.maps hSources hReps hG state.ground.action hT
  have old : FiniteCompressionAccounting P0 I Sources τ state.inputs.toState :=
    state.inputs_toState.symm ▸ accounted
  have result := state.inputs.accounting_next M next entries inputs
    (state.invariant.originalSubset seed.top_mem) state.invariant.top old
  rw [state.inputs.toState_successor M next inputs, state.inputs_toState] at result
  exact result

theorem canonical_iterate_accounting
    (initial : FiniteCompressionAccounting P0 I Sources τ state.data) (n : Nat) :
    FiniteCompressionAccounting P0 I Sources τ (state.data.iterate M I Sources Reps G T n) := by
  induction n with
  | zero => exact initial
  | succ n ih =>
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    have step := current.successor_accounting pairing unions powers separation hI hSources hReps hG hT
      (equal.symm ▸ ih)
    rw [equal, ← RecursiveStateData.iterate_succ] at step
    exact step

end PartitionPilot.Forcing.GroundCompressionState

end

end OAI
