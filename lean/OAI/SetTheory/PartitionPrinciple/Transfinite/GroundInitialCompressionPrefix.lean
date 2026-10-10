import OAI.SetTheory.PartitionPrinciple.Geometry.GroundInitialCompressionOrigin

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialCompressionPrefix
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ C D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
    (hBase : base ∈ M.sets) (prior : GroundChronologicalHistory M T0 C D rD)
    (ordinal : ordinalSetProperty T0) (baseMember : base ∈ T0)
    (priorSpace : prior.space base = P) (priorOrder : prior.order base = r)
    (priorMeet : prior.meetGraph base = μ) (priorBirth : prior.birth base = old)
    (priorHeight : prior.height base = original) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        Nonempty (GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior) := by
  dsimp only
  have hOld : old ∈ M.sets := priorBirth ▸ prior.birth_mem base baseMember
  have oldFunction : FunctionGraphOn P old := by
    rw [← priorSpace, ← priorBirth]
    exact ⟨T0, prior.birth_function base baseMember⟩
  have oldBound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base := by
    intro x t entry
    have priorEntry : ZFSet.pair x t ∈ prior.birth base := priorBirth.symm ▸ entry
    have hx := (ZFSet.pair_mem_prod.1 ((prior.birth_function base baseMember).1 priorEntry)).1
    exact (prior.birth_bound base baseMember x hx t priorEntry).symm
  have oldMeet : OldMeetCode r μ old := by
    rw [← priorOrder, ← priorMeet, ← priorBirth]
    exact prior.old_meet base baseMember
  obtain ⟨hI, hSources, hFilters, hG, hT, Reps, hReps, seed, state, initialData⟩ :=
    M.exists_groundInitialCompressionState pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet hτ top
  refine ⟨hI, hSources, hFilters, hT, Reps, hReps, ?_⟩
  rw [← initialData]
  obtain ⟨algebra⟩ := state.exists_groundAlgebra pairing unions powers separation collection infinite
    hI hSources hReps hG hT
  have accounting := state.initial_union_range_accounting algebra pairing unions powers separation
    hP hG hr hμ hA hLabels hI hSources hReps hT initialData rfl rfl
  obtain ⟨completion⟩ := state.completion_of_accounting algebra pairing unions powers separation
    hI hSources hReps hG hT accounting
  have initialDomain : state.data.D = P := by rw [initialData]; rfl
  have initialOrder : state.data.rD = r := by rw [initialData]; rfl
  have constant : RecursiveTemplateConstancy P r μ state.data := by
    rw [initialData]
    exact M.initialCompressionData_template_constancy P G r μ A Labels
  obtain ⟨heights⟩ := state.exists_groundHeightData completion.algebra.union
    pairing unions powers separation collection infinite choice hI hSources hReps hG hT
    initialDomain initialOrder constant hP hC hD hrD hc hOriginal originalCode columns target above
    coordinateInjection originalSmall
  have profiles := state.initial_union_profiles completion.algebra pairing unions powers separation
    hP hG hr hμ hA hLabels hI hSources hReps hT initialData rfl
  have initialBirthFunction : FunctionGraphOn state.data.D old := initialDomain.symm ▸ oldFunction
  have initialOldMeet : OldMeetCode state.data.rD state.data.μD old := by
    rw [initialData]
    exact oldMeet
  obtain ⟨births⟩ := state.exists_groundBirthData completion.algebra.union
    pairing unions powers separation collection infinite hI hSources hReps hG hT
    hBase hOld (ordinalSetProperty_member ordinal baseMember) initialBirthFunction oldBound initialOldMeet
  have initialMeet : state.data.μD = μ := by rw [initialData]; rfl
  let history := state.prefixHistory completion.algebra.union births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal baseMember constant
    initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth
  refine ⟨⟨⟨⟨⟨completion, heights⟩, profiles⟩, births⟩, history, priorHeight, ?_, ?_, ?_⟩⟩
  · intro s before
    exact state.prefixHistory_old completion.algebra.union births heights prior
      pairing unions powers separation hI hSources hReps hG hT ordinal baseMember constant
      initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth before
  · intro n
    exact state.prefixHistory_stamp completion.algebra.union births heights prior
      pairing unions powers separation hI hSources hReps hG hT ordinal baseMember constant
      initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth n
  · exact state.prefixHistory_limit completion.algebra.union births heights prior
      pairing unions powers separation hI hSources hReps hG hT ordinal baseMember constant
      initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
