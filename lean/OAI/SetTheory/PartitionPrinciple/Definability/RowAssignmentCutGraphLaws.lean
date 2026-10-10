import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRowAssignmentCuts

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem rowAssignmentCutGraph_function (upper lower levels alpha : ZFSet.{u})
    (flat : ∀ p ∈ upper, ∃ row A, p = ZFSet.pair row A)
    (closed : ∀ row A, ZFSet.pair row A ∈ upper →
      ZFSet.pair row (assignmentCut levels alpha A) ∈ lower) :
    ZFSet.IsFunc upper lower (rowAssignmentCutGraph upper lower levels alpha) := by
  refine ⟨fun _ h => ((mem_rowAssignmentCutGraph _ _ _ _ _).1 h).1, ?_⟩
  intro p hp
  obtain ⟨row, A, rfl⟩ := flat p hp
  refine ⟨ZFSet.pair row (assignmentCut levels alpha A),
    (pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).2 ⟨hp, closed row A hp, rfl⟩, ?_⟩
  intro q entry
  exact ((pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).1 entry).2.2

theorem rowAssignmentCutGraph_compose
    (upper middle lower outerLevels beta innerLevels alpha directLevels gamma : ZFSet.{u})
    (middle_valid : ∀ row A, ZFSet.pair row A ∈ upper →
      ZFSet.pair row (assignmentCut outerLevels beta A) ∈ middle)
    (coherent : ∀ row A, ZFSet.pair row A ∈ upper →
      assignmentCut innerLevels alpha (assignmentCut outerLevels beta A) =
        assignmentCut directLevels gamma A) :
    relationCompose upper middle lower
      (rowAssignmentCutGraph upper middle outerLevels beta)
      (rowAssignmentCutGraph middle lower innerLevels alpha) =
        rowAssignmentCutGraph upper lower directLevels gamma := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨p, hp, q, _, w, hw, rfl, first, second⟩ := (mem_relationCompose _ _ _ _ _ z).1 hz
    obtain ⟨_, row, A, equal⟩ := (mem_rowAssignmentCutGraph _ _ _ _ _).1 first
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    have value := ((pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).1 second).2.2
    rw [coherent row A hp] at value
    exact (pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).2 ⟨hp, hw, value⟩
  · intro hz
    obtain ⟨bound, row, A, rfl⟩ := (mem_rowAssignmentCutGraph _ _ _ _ z).1 hz
    obtain ⟨hp, hw⟩ := ZFSet.pair_mem_prod.1 bound
    have hm := middle_valid row A hp
    exact (mem_relationCompose _ _ _ _ _ _).2
      ⟨ZFSet.pair row A, hp, ZFSet.pair row (assignmentCut outerLevels beta A), hm,
        ZFSet.pair row (assignmentCut directLevels gamma A), hw, rfl,
        (pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).2 ⟨hp, hm, rfl⟩,
        (pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).2
          ⟨hm, hw, congrArg (ZFSet.pair row) (coherent row A hp).symm⟩⟩

theorem rowAssignmentCutGraph_nested (upper middle lower levels alpha beta : ZFSet.{u})
    (below : alpha ⊆ beta)
    (middle_valid : ∀ row A, ZFSet.pair row A ∈ upper →
      ZFSet.pair row (assignmentCut levels beta A) ∈ middle) :
    relationCompose upper middle lower (rowAssignmentCutGraph upper middle levels beta)
      (rowAssignmentCutGraph middle lower levels alpha) =
        rowAssignmentCutGraph upper lower levels alpha :=
  rowAssignmentCutGraph_compose upper middle lower levels beta levels alpha levels alpha
    middle_valid (fun _ _ _ => assignmentCut_nested below)

theorem rowAssignmentCutGraph_identity (carrier levels alpha : ZFSet.{u})
    (flat : ∀ p ∈ carrier, ∃ row A, p = ZFSet.pair row A)
    (fixed : ∀ row A, ZFSet.pair row A ∈ carrier → assignmentCut levels alpha A = A) :
    rowAssignmentCutGraph carrier carrier levels alpha = identityFunctionGraph carrier := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨bound, row, A, rfl⟩ := (mem_rowAssignmentCutGraph _ _ _ _ z).1 hz
    have hp := (ZFSet.pair_mem_prod.1 bound).1
    rw [fixed row A hp]
    exact (mem_identityFunctionGraph _ _).2 ⟨ZFSet.pair row A, hp, rfl⟩
  · intro hz
    obtain ⟨p, hp, rfl⟩ := (mem_identityFunctionGraph _ _).1 hz
    obtain ⟨row, A, rfl⟩ := flat p hp
    exact (pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).2
      ⟨hp, hp, congrArg (ZFSet.pair row) (fixed row A hp).symm⟩

end PartitionPilot.Forcing

end

end OAI
