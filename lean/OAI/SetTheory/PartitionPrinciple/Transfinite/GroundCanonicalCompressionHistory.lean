import OAI.SetTheory.PartitionPrinciple.Definability.GroundCompressionHistoryFormulas

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace RecursiveStateData
variable (initial : RecursiveStateData.{u}) (M : TransitiveGround.{u})
variable (I Sources Reps G T : ZFSet.{u})

noncomputable def canonicalHistory : ZFSet.{u} :=
  familyCodeGraph natSetCode (fun n => (initial.iterate M I Sources Reps G T n).code)

theorem pair_mem_canonicalHistory (n : Nat) (y : ZFSet.{u}) :
    ZFSet.pair (natSetCode n) y ∈ initial.canonicalHistory M I Sources Reps G T ↔
      y = (initial.iterate M I Sources Reps G T n).code :=
  pair_mem_familyCodeGraph _ _ natSetCode_injective n y

theorem canonicalHistory_function :
    FunctionGraphOn ZFSet.omega (initial.canonicalHistory M I Sources Reps G T) := by
  have domain : ZFSet.range (natSetCode : Nat → ZFSet.{u}) = ZFSet.omega := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_range, mem_omega_iff_natSetCode]
    change (∃ n, natSetCode n = x) ↔ ∃ n, x = natSetCode n
    constructor
    · rintro ⟨n, hx⟩
      exact ⟨n, hx.symm⟩
    · rintro ⟨n, hx⟩
      exact ⟨n, hx.symm⟩
  exact domain ▸ familyCodeGraph_function natSetCode
    (fun n => (initial.iterate M I Sources Reps G T n).code) natSetCode_injective

theorem canonicalHistory_eq_of_entries {history : ZFSet.{u}}
    (function : FunctionGraphOn ZFSet.omega history)
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔
      y = (initial.iterate M I Sources Reps G T n).code) :
    initial.canonicalHistory M I Sources Reps G T = history := by
  apply (initial.canonicalHistory_function M I Sources Reps G T).eq_of_agree function
  intro x y z xy xz
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1
    ((initial.canonicalHistory_function M I Sources Reps G T).pair_source xy)
  exact ((initial.pair_mem_canonicalHistory M I Sources Reps G T n y).1 xy).trans
    ((entries n z).1 xz).symm

end RecursiveStateData

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)

include pairing unions powers separation collection infinite hI hSources hReps hG hT

theorem canonicalHistory_spec :
    let R := groundRecursionStep M
      (naturalStepFormula (M.compressionSuccessorFormula pairing unions powers separation))
      (extend state.data.code (extend I (extend Sources (extend Reps (extend G (extend T Fin.elim0))))))
    state.data.canonicalHistory M I Sources Reps G T ∈ M.sets ∧
      OrdinalRecursionTrace R ZFSet.omega (state.data.canonicalHistory M I Sources Reps G T) ∧
      ∀ history, OrdinalRecursionTrace R ZFSet.omega history →
        history = state.data.canonicalHistory M I Sources Reps G T := by
  obtain ⟨history, ground, trace, entries, unique, _⟩ := state.exists_groundHistory
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  have equal := state.data.canonicalHistory_eq_of_entries M I Sources Reps G T trace.1 entries
  rw [← equal] at ground trace unique
  exact ⟨ground, trace, unique⟩

theorem canonicalHistory_mem :
    state.data.canonicalHistory M I Sources Reps G T ∈ M.sets :=
  (state.canonicalHistory_spec pairing unions powers separation collection infinite
    hI hSources hReps hG hT).1

theorem realize_compressionHistory_iff {history : ZFSet.{u}} (hHistory : history ∈ M.sets) :
    Realize M.sets (M.compressionHistoryFormula pairing unions powers separation)
      (extend ZFSet.omega (extend history (extend state.data.code
        (extend I (extend Sources (extend Reps (extend G (extend T Fin.elim0)))))))) ↔
      history = state.data.canonicalHistory M I Sources Reps G T := by
  have initial : state.data.code ∈ M.sets := by
    simpa only [RecursiveStateData.iterate_zero] using
      state.canonical_iterate_code_mem pairing unions powers separation hI hSources hReps hG hT 0
  rw [M.realize_compressionHistoryFormula pairing unions powers separation
    (M.omega_mem separation infinite) hHistory initial hI hSources hReps hG hT]
  obtain ⟨_, trace, unique⟩ := state.canonicalHistory_spec pairing unions powers separation
    collection infinite hI hSources hReps hG hT
  exact ⟨unique history, fun equal => equal.symm ▸ trace⟩

end GroundCompressionState
end PartitionPilot.Forcing

end

end OAI
