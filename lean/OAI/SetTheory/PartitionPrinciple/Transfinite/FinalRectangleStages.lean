import OAI.SetTheory.PartitionPrinciple.Geometry.MainRectangleMeets

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

open CountableColumns
variable (Label : Type 1)

theorem stage_successor_rectangles (a : Column)
    (r : ActionRectangle (stage Label a).order (stage Label a).action.iso)
    (X : (stage Label a).Point) : (transition Label (lt_start a).le).Rectangles r X := by
  apply (Transition.rectangles_transport _ (stage_successor Label a) r X).mp
  rw [transition_successor]
  exact (stage Label a).next_rectangles Label r X

theorem final_rectangles_at (a : Column)
    (r : ActionRectangle (stage Label a).order (stage Label a).action.iso)
    (X : (stage Label a).Point) :
    ∃ h : Bool → FinalActor Label,
      (∀ j z, (finalOrder Label).le z ((finalInclusion Label a).toFun r.C) →
        ((finalAction Label).iso (h j)).toFun z =
        ((finalAction Label).iso (finalGroupInclusion Label a ((stage Label a).rectangleOldActor r j))).toFun z) ∧
      (∀ z, (finalOrder Label).le z ((finalInclusion Label a).toFun r.B) →
        ((finalAction Label).iso (h false)).toFun z = ((finalAction Label).iso (h true)).toFun z) ∧
      (∀ j, (finalOrder Label).meet
        (((finalAction Label).iso (h j)).toFun ((finalInclusion Label a).toFun r.D))
        ((finalInclusion Label a).toFun X) = (finalInclusion Label a).toFun
        ((stage Label a).order.meet
          (((stage Label a).action.iso ((stage Label a).rectangleOldActor r j)).toFun r.C) X)) ∧
      (finalOrder Label).meet
        (((finalAction Label).iso (h false)).toFun ((finalInclusion Label a).toFun r.D))
        (((finalAction Label).iso (h true)).toFun ((finalInclusion Label a).toFun r.D)) =
        ((finalAction Label).iso (h false)).toFun ((finalInclusion Label a).toFun r.B) := by
  rcases stage_successor_rectangles Label a r X with ⟨h, agreeC, agreeB, rootMeet, pairMeet⟩
  refine ⟨fun j => finalGroupInclusion Label (start a) (h j), ?_, ?_, ?_, ?_⟩
  · intro j z lower
    rw [← final_actors_coherent Label (lt_start a).le ((stage Label a).rectangleOldActor r j)]
    apply final_agreement Label (start a) _ _ _ (agreeC j) z
    erw [final_points_coherent]
    exact lower
  · intro z lower
    apply final_agreement Label (start a) _ _ _ agreeB z
    erw [final_points_coherent]
    exact lower
  · intro j
    erw [← final_points_coherent Label (lt_start a).le r.D,
      ← final_points_coherent Label (lt_start a).le X,
      final_action_stage, ← (finalInclusion Label (start a)).map_meet,
      rootMeet, final_points_coherent]
  · rw [← final_points_coherent Label (lt_start a).le r.D,
      ← final_points_coherent Label (lt_start a).le r.B,
      final_action_stage, final_action_stage, final_action_stage,
      ← (finalInclusion Label (start a)).map_meet, pairMeet]

end PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

end

end OAI
