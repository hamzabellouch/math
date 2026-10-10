import OAI.SetTheory.PartitionPrinciple.Geometry.AssignmentNestedSplices

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

def FlatHistoryCuts (stages history levels row A : ZFSet.{u}) : Prop :=
  ∀ beta ∈ stages, ∃ Q, ZFSet.pair beta Q ∈ history ∧
    ZFSet.pair row (assignmentCut levels beta A) ∈ Q

def FlatLimitConditionCode (stages history levels z : ZFSet.{u}) : Prop :=
  ∃ row A, z = ZFSet.pair row A ∧ FlatHistoryCuts stages history levels row A

theorem flatLimitConditionCode_pair (stages history levels row A : ZFSet.{u}) :
    FlatLimitConditionCode stages history levels (ZFSet.pair row A) ↔
      FlatHistoryCuts stages history levels row A := by
  constructor
  · rintro ⟨row', A', equal, valid⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective equal
    exact valid
  · intro valid
    exact ⟨row, A, rfl, valid⟩

theorem flatHistoryCuts_lookup_iff {stages history levels row A : ZFSet.{u}}
    (function : FunctionGraphOn stages history) :
    FlatHistoryCuts stages history levels row A ↔
      ∀ beta ∈ stages, ∀ Q, ZFSet.pair beta Q ∈ history →
        ZFSet.pair row (assignmentCut levels beta A) ∈ Q := by
  constructor
  · intro valid beta hbeta Q entry
    obtain ⟨Q', entry', member⟩ := valid beta hbeta
    exact function.unique entry' entry ▸ member
  · intro valid beta hbeta
    obtain ⟨Q, entry⟩ := function.total hbeta
    exact ⟨Q, entry, valid beta hbeta Q entry⟩

theorem flatHistoryCuts_restrict {stages earlier history levels row A : ZFSet.{u}}
    (valid : FlatHistoryCuts stages history levels row A) (subset : earlier ⊆ stages) :
    FlatHistoryCuts earlier (graphRestriction earlier history) levels row A := by
  intro beta hbeta
  obtain ⟨Q, entry, member⟩ := valid beta (subset hbeta)
  exact ⟨Q, pair_mem_graphRestriction.2 ⟨entry, hbeta⟩, member⟩

theorem flatHistoryCuts_cut {stages earlier history levels alpha row A : ZFSet.{u}}
    (valid : FlatHistoryCuts stages history levels row A) (subset : earlier ⊆ stages)
    (nested : ∀ beta ∈ earlier, assignmentCut levels beta (assignmentCut levels alpha A) =
      assignmentCut levels beta A) :
    FlatHistoryCuts earlier (graphRestriction earlier history) levels row
      (assignmentCut levels alpha A) := by
  intro beta hbeta
  obtain ⟨Q, entry, member⟩ := flatHistoryCuts_restrict valid subset beta hbeta
  exact ⟨Q, entry, (nested beta hbeta).symm ▸ member⟩

theorem flatHistoryCuts_cut_of_subset {stages earlier history levels alpha row A : ZFSet.{u}}
    (valid : FlatHistoryCuts stages history levels row A) (subset : earlier ⊆ stages)
    (below : ∀ beta ∈ earlier, beta ⊆ alpha) :
    FlatHistoryCuts earlier (graphRestriction earlier history) levels row
      (assignmentCut levels alpha A) :=
  flatHistoryCuts_cut valid subset (fun beta hbeta => assignmentCut_nested (below beta hbeta))

end PartitionPilot.Forcing

end

end OAI
