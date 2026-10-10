import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialCompressionHistory

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialCompressionIterates
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let Sources := literalTaskSourceGraph I P R U Labels
    let Filters := literalTaskFilterGraph I P R U Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ G ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters,
        ∀ n : Nat,
          ((M.initialCompressionData P G r μ A Labels).iterate M I Sources Reps G T n).code ∈ M.sets ∧
          ∃ current : GroundCompressionState M seed,
            current.data = (M.initialCompressionData P G r μ A Labels).iterate M I Sources Reps G T n := by
  obtain ⟨hI, hSources, hFilters, hG, hT, Reps, hReps, seed, initial, initialData⟩ :=
    M.exists_groundInitialCompressionState pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet hτ top
  refine ⟨hI, hSources, hFilters, hG, hT, Reps, hReps, seed, ?_⟩
  intro n
  rw [← initialData]
  exact ⟨initial.canonical_iterate_code_mem pairing unions powers separation
    hI hSources hReps hG hT n,
    initial.canonical_iterate_valid pairing unions powers separation hI hSources hReps hG hT n⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
