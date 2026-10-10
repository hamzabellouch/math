import OAI.SetTheory.PartitionPrinciple.Transfinite.MainStageFilterBases

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

open Chronological CountableColumns
variable (Label : Type 1)

theorem countable_points_in_stage (B : Set (FinalPoint Label)) (small : B.Countable) :
    ∃ a, ∀ x ∈ B, ∃ y, (finalInclusion Label a).toFun y = x := by
  classical
  let := small.to_subtype
  let index (x : B) : Column := Classical.choose (final_point_cover Label x.val)
  have represented (x : B) : ∃ y, (finalInclusion Label (index x)).toFun y = x.val :=
    Classical.choose_spec (final_point_cover Label x.val)
  refine ⟨upperBound index, ?_⟩
  intro x hx
  rcases represented ⟨x, hx⟩ with ⟨y, eq⟩
  have h : index ⟨x, hx⟩ < upperBound index := upperBound_above index ⟨x, hx⟩
  exact ⟨(transition Label h.le).points.toFun y, (final_points_coherent Label h.le y).trans eq⟩

def LocalizedFilter (F : MeetFilter (finalOrder Label)) : Prop :=
  ∃ a, ∀ x, F.mem x → ∃ y : (stage Label a).Point,
    F.mem ((finalInclusion Label a).toFun y) ∧
      (finalOrder Label).le ((finalInclusion Label a).toFun y) x

theorem basis_localized (F : MeetFilter (finalOrder Label)) (basis : CountableBasis F) :
    LocalizedFilter Label F := by
  rcases basis with ⟨B, small, positive, below⟩
  rcases countable_points_in_stage Label B small with ⟨a, covered⟩
  refine ⟨a, ?_⟩
  intro x hx
  rcases below x hx with ⟨y, hy, lower⟩
  rcases covered y hy with ⟨z, eq⟩
  exact ⟨z, eq.symm ▸ positive y hy, eq.symm ▸ lower⟩

theorem localized_basis (F : MeetFilter (finalOrder Label)) (localized : LocalizedFilter Label F) :
    CountableBasis F := by
  rcases localized with ⟨a, localize⟩
  rcases countableBelow_copy (finalInclusion Label a) F
    (stage_all_filters_countable Label a) with ⟨B, small, positive, below⟩
  refine ⟨B, small, positive, ?_⟩
  intro x hx
  rcases localize x hx with ⟨y, hy, lower⟩
  rcases below ((finalInclusion Label a).toFun y) ⟨hy, y, rfl⟩ with ⟨z, hz, le⟩
  exact ⟨z, hz, (finalOrder Label).trans le lower⟩

theorem countable_basis_iff_localized (F : MeetFilter (finalOrder Label)) :
    CountableBasis F ↔ LocalizedFilter Label F :=
  ⟨basis_localized Label F, localized_basis Label F⟩

theorem final_coinitiality_iff_localization :
    AllFiltersCountable (finalOrder Label) ↔ ∀ F, LocalizedFilter Label F :=
  ⟨fun h F => basis_localized Label F (h F), fun h F => localized_basis Label F (h F)⟩

end PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

end

end OAI
