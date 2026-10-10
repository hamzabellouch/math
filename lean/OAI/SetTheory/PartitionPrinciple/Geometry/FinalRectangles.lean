import OAI.SetTheory.PartitionPrinciple.Transfinite.FinalRectangleStages

namespace OAI

namespace PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

variable (Label : Type 1)

theorem rectangle_data_in_stage
    (r : ActionRectangle (finalOrder Label) (finalAction Label).iso) (X : FinalPoint Label) :
    ∃ a, ∃ t : ActionRectangle (stage Label a).order (stage Label a).action.iso,
      ∃ Y : (stage Label a).Point,
        (finalInclusion Label a).toFun t.C = r.C ∧
        (finalInclusion Label a).toFun t.B = r.B ∧
        (finalInclusion Label a).toFun t.D = r.D ∧
        finalGroupInclusion Label a t.first = r.first ∧
        finalGroupInclusion Label a t.second = r.second ∧
        (finalInclusion Label a).toFun Y = X := by
  let points (j : Bool × Bool) : FinalPoint Label :=
    if j.1 then (if j.2 then X else r.D) else (if j.2 then r.B else r.C)
  let actors (j : Bool) : FinalActor Label := if j then r.second else r.first
  rcases countable_data_in_stage Label points actors with ⟨a, hp, hg⟩
  obtain ⟨C, hC⟩ : ∃ C, (finalInclusion Label a).toFun C = r.C := hp (false, false)
  obtain ⟨B, hB⟩ : ∃ B, (finalInclusion Label a).toFun B = r.B := hp (false, true)
  obtain ⟨D, hD⟩ : ∃ D, (finalInclusion Label a).toFun D = r.D := hp (true, false)
  obtain ⟨Y, hY⟩ : ∃ Y, (finalInclusion Label a).toFun Y = X := hp (true, true)
  obtain ⟨g1, hg1⟩ : ∃ g, finalGroupInclusion Label a g = r.first := hg false
  obtain ⟨g2, hg2⟩ : ∃ g, finalGroupInclusion Label a g = r.second := hg true
  have cd : (stage Label a).order.le C D := by
    apply ((finalInclusion Label a).le_iff _ _).mp
    rw [hC, hD]
    exact r.C_le_D
  have bd : (stage Label a).order.le B D := by
    apply ((finalInclusion Label a).le_iff _ _).mp
    rw [hB, hD]
    exact r.B_le_D
  have agree : ∀ x, (stage Label a).order.le x ((stage Label a).order.meet C B) →
      ((stage Label a).action.iso g1).toFun x = ((stage Label a).action.iso g2).toFun x := by
    intro x lower
    apply embedding_injective (finalInclusion Label a)
    rw [← final_action_stage Label a g1 x, ← final_action_stage Label a g2 x, hg1, hg2]
    apply r.agree
    have h := ((finalInclusion Label a).le_iff _ _).mpr lower
    rw [(finalInclusion Label a).map_meet, hC, hB] at h
    exact h
  have separated : (stage Label a).order.meet
      (((stage Label a).action.iso g1).toFun D) (((stage Label a).action.iso g2).toFun D) =
      ((stage Label a).action.iso g1).toFun ((stage Label a).order.meet C B) := by
    apply embedding_injective (finalInclusion Label a)
    rw [(finalInclusion Label a).map_meet,
      ← final_action_stage Label a g1 D, ← final_action_stage Label a g2 D,
      ← final_action_stage Label a g1 ((stage Label a).order.meet C B),
      (finalInclusion Label a).map_meet, hC, hB, hD, hg1, hg2]
    exact r.separated
  exact ⟨a, ⟨C, B, D, g1, g2, cd, bd, agree, separated⟩, Y, hC, hB, hD, hg1, hg2, hY⟩

theorem final_rectangles
    (r : ActionRectangle (finalOrder Label) (finalAction Label).iso) (X : FinalPoint Label)
    (first_upper : (finalOrder Label).le (((finalAction Label).iso r.first).toFun r.D) X)
    (second_upper : (finalOrder Label).le (((finalAction Label).iso r.second).toFun r.D) X) :
    ∃ h1 h2 : FinalActor Label,
      (∀ z, (finalOrder Label).le z r.C →
        ((finalAction Label).iso h1).toFun z = ((finalAction Label).iso r.first).toFun z) ∧
      (∀ z, (finalOrder Label).le z r.C →
        ((finalAction Label).iso h2).toFun z = ((finalAction Label).iso r.second).toFun z) ∧
      (∀ z, (finalOrder Label).le z r.B →
        ((finalAction Label).iso h1).toFun z = ((finalAction Label).iso h2).toFun z) ∧
      (finalOrder Label).meet (((finalAction Label).iso h1).toFun r.D) X =
        ((finalAction Label).iso r.first).toFun r.C ∧
      (finalOrder Label).meet (((finalAction Label).iso h2).toFun r.D) X =
        ((finalAction Label).iso r.second).toFun r.C ∧
      (finalOrder Label).meet (((finalAction Label).iso h1).toFun r.D)
        (((finalAction Label).iso h2).toFun r.D) = ((finalAction Label).iso h1).toFun r.B := by
  rcases rectangle_data_in_stage Label r X with ⟨a, t, Y, hC, hB, hD, hg1, hg2, hY⟩
  rcases final_rectangles_at Label a t Y with ⟨h, agreeC, agreeB, rootMeet, pairMeet⟩
  have actors (j : Bool) : finalGroupInclusion Label a ((stage Label a).rectangleOldActor t j) =
      if j then r.second else r.first := by
    cases j with
    | false => exact hg1
    | true => exact hg2
  have cAgree (j : Bool) (z : FinalPoint Label) (lower : (finalOrder Label).le z r.C) :
      ((finalAction Label).iso (h j)).toFun z =
        ((finalAction Label).iso (if j then r.second else r.first)).toFun z := by
    have eq := agreeC j z (hC.symm ▸ lower)
    rw [actors] at eq
    exact eq
  have mappedRoot (j : Bool) :
      (finalInclusion Label a).toFun ((stage Label a).order.meet
        (((stage Label a).action.iso ((stage Label a).rectangleOldActor t j)).toFun t.C) Y) =
      ((finalAction Label).iso (if j then r.second else r.first)).toFun r.C := by
    rw [(finalInclusion Label a).map_meet, ← final_action_stage, actors, hC, hY]
    apply meet_eq_left_of_le
    cases j with
    | false =>
      exact (finalOrder Label).trans
        ((((finalAction Label).iso r.first).le_iff _ _).mpr r.C_le_D) first_upper
    | true =>
      exact (finalOrder Label).trans
        ((((finalAction Label).iso r.second).le_iff _ _).mpr r.C_le_D) second_upper
  refine ⟨h false, h true, cAgree false, cAgree true, ?_, ?_, ?_, ?_⟩
  · simpa only [hB] using agreeB
  · simpa only [hD, hY, Bool.false_eq_true, ↓reduceIte] using
      (rootMeet false).trans (mappedRoot false)
  · simpa only [hD, hY, ↓reduceIte] using (rootMeet true).trans (mappedRoot true)
  · simpa only [hD, hB] using pairMeet

end PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

end OAI
