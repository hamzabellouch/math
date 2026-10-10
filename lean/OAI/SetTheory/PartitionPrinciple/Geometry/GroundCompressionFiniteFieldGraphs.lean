import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundChronologyFieldAppend

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
variable {base old C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)

noncomputable def prefixFiniteField (j : Fin 5) (n : Nat) : ZFSet.{u} :=
  Fin.cases (state.data.iterate M I Sources Reps G T (n + 1)).D
    (Fin.cases (state.data.iterate M I Sources Reps G T (n + 1)).rD
      (Fin.cases (state.data.iterate M I Sources Reps G T (n + 1)).μD
        (Fin.cases (graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth)
          (fun _ => heights.function.natValue (n + 1))))) j

noncomputable def prefixTerminalField (j : Fin 5) : ZFSet.{u} :=
  Fin.cases (data.fields 0) (Fin.cases (data.fields 1) (Fin.cases (data.fields 2)
    (Fin.cases births.birth (fun _ => heights.height)))) j

theorem prefixTerminalField_ground (j : Fin 5) : state.prefixTerminalField data births heights j ∈ M.sets :=
  Fin.cases (data.ground 0) (Fin.cases (data.ground 1) (Fin.cases (data.ground 2)
    (Fin.cases births.birth_ground (fun _ => heights.height_ground)))) j

theorem exists_prefixFiniteGraphs
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    ∃ graphs : Fin 5 → ZFSet.{u}, (∀ j, graphs j ∈ M.sets) ∧
      (∀ j, FunctionGraphOn ZFSet.omega (graphs j)) ∧
      ∀ j n y, ZFSet.pair (natSetCode n) y ∈ graphs j ↔
        y = state.prefixFiniteField data births heights j n := by
  have hOmega := M.omega_mem separation infinite
  obtain ⟨history, hHistory, _, entries, _, _⟩ := state.exists_groundHistory
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  obtain ⟨Ps, hPs, pFunc, pEntries⟩ := M.exists_groundStateFieldFamily
    pairing separation collection hOmega hHistory (state.data.iterate M I Sources Reps G T) entries 0
  obtain ⟨Rs, hRs, rFunc, rEntries⟩ := M.exists_groundStateFieldFamily
    pairing separation collection hOmega hHistory (state.data.iterate M I Sources Reps G T) entries 1
  obtain ⟨Ms, hMs, mFunc, mEntries⟩ := M.exists_groundStateFieldFamily
    pairing separation collection hOmega hHistory (state.data.iterate M I Sources Reps G T) entries 2
  let sources : Fin 5 → ZFSet.{u} := Fin.cases Ps (Fin.cases Rs (Fin.cases Ms
    (Fin.cases births.family (fun _ => heights.family))))
  have ground : ∀ j, sources j ∈ M.sets := Fin.cases hPs (Fin.cases hRs (Fin.cases hMs
    (Fin.cases births.family_ground (fun _ => heights.family_ground))))
  have functions : ∀ j, FunctionGraphOn ZFSet.omega (sources j) := Fin.cases pFunc
    (Fin.cases rFunc (Fin.cases mFunc (Fin.cases births.family_function (fun _ => heights.function))))
  refine ⟨fun j => naturalFamilyShift (sources j),
    fun j => M.naturalFamilyShift_mem pairing unions powers separation infinite (ground j),
    fun j => naturalFamilyShift_function (functions j), ?_⟩
  intro j n y
  rw [naturalFamilyShift_entries]
  exact Fin.cases (pEntries (n + 1) y) (Fin.cases (rEntries (n + 1) y)
    (Fin.cases (mEntries (n + 1) y) (Fin.cases (births.family_entries (n + 1) y)
      (fun _ => heights.function.natValue_entry_iff (n + 1) y)))) j

end PartitionPilot.Forcing.GroundCompressionState

end

end OAI
