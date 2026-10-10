import OAI.SetTheory.PartitionPrinciple.Transfinite.StageOneDataBoundLaws

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

noncomputable def assignmentIndexLevels (I T eta levels : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (stageOneAssignments I T) I eta
    (productFirst I (ZFSet.prod T T)) levels

theorem pair_mem_assignmentIndexLevels (I T eta levels z level : ZFSet.{u}) :
    ZFSet.pair z level ∈ assignmentIndexLevels I T eta levels ↔
      ∃ i ∈ I, ∃ u ∈ T, ∃ w ∈ T,
        z = stageOneAssignment i u w ∧ level ∈ eta ∧ ZFSet.pair i level ∈ levels := by
  rw [assignmentIndexLevels, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, hl, i, hi, projection, entry⟩
    obtain ⟨j, _, rest, hr, equal⟩ := (mem_productFirst I (ZFSet.prod T T) _).1 projection
    obtain ⟨hz, hji⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨u, hu, w, hw, rfl⟩ := ZFSet.mem_prod.1 hr
    exact ⟨i, hi, u, hu, w, hw, hji ▸ hz, hl, entry⟩
  · rintro ⟨i, hi, u, hu, w, hw, rfl, hl, entry⟩
    refine ⟨(stageOneAssignment_mem_assignments I T i u w).2 ⟨hi, hu, hw⟩,
      hl, i, hi, ?_, entry⟩
    exact (mem_productFirst I (ZFSet.prod T T) _).2
      ⟨i, hi, ZFSet.pair u w, ZFSet.pair_mem_prod.2 ⟨hu, hw⟩, rfl⟩

theorem assignmentIndexLevels_entry (I T eta levels i u w level : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u w) level ∈ assignmentIndexLevels I T eta levels ↔
      i ∈ I ∧ u ∈ T ∧ w ∈ T ∧ level ∈ eta ∧ ZFSet.pair i level ∈ levels := by
  rw [pair_mem_assignmentIndexLevels]
  constructor
  · rintro ⟨j, hj, v, hv, x, hx, equal, hl, entry⟩
    obtain ⟨rfl, rfl, rfl⟩ := (stageOneAssignment_eq_iff i u w j v x).1 equal
    exact ⟨hj, hv, hx, hl, entry⟩
  · rintro ⟨hi, hu, hw, hl, entry⟩
    exact ⟨i, hi, u, hu, w, hw, rfl, hl, entry⟩

theorem assignmentIndexLevels_function {I T eta levels : ZFSet.{u}}
    (function : ZFSet.IsFunc I eta levels) :
    ZFSet.IsFunc (stageOneAssignments I T) eta (assignmentIndexLevels I T eta levels) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [assignmentIndexLevels, relationCompose] at hz
    exact (ZFSet.mem_sep.1 hz).1
  · intro z hz
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T z).1 hz
    obtain ⟨level, entry, unique⟩ := function.2 i hi
    have hl := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    refine ⟨level, (assignmentIndexLevels_entry I T eta levels i u w level).2
      ⟨hi, hu, hw, hl, entry⟩, ?_⟩
    intro other ho
    exact unique other ((assignmentIndexLevels_entry I T eta levels i u w other).1 ho).2.2.2.2

end PartitionPilot.Forcing

end

end OAI
