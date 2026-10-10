import OAI.SetTheory.PartitionPrinciple.Geometry.ExternalTranslation

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

theorem translate_one (z : f.Node a) : f.translate a 1 z = z := by
  rcases f.copy_cover a z with ⟨w, x, rfl⟩
  rw [f.translate_copy, one_mul]

theorem translate_mul (g h : External J f.Letters) (z : f.Node a) :
    f.translate a (g * h) z = f.translate a g (f.translate a h z) := by
  rcases f.copy_cover a z with ⟨w, x, rfl⟩
  rw [f.translate_copy, f.translate_copy, f.translate_copy, mul_assoc]

theorem translate_left_inverse (g : External J f.Letters) (z : f.Node a) :
    f.translate a g⁻¹ (f.translate a g z) = z := by
  rw [← f.translate_mul, inv_mul_cancel, f.translate_one]

theorem translate_right_inverse (g : External J f.Letters) (z : f.Node a) :
    f.translate a g (f.translate a g⁻¹ z) = z := by
  rw [← f.translate_mul, mul_inv_cancel, f.translate_one]

theorem translate_monotone (g : External J f.Letters) (x y : f.Node a)
    (h : (f.gluedOrder a).le x y) :
    (f.gluedOrder a).le (f.translate a g x) (f.translate a g y) := by
  rcases f.comparison_in_copy a x y h with ⟨w, b, c, rfl, rfl, hbc⟩
  rw [f.translate_copy, f.translate_copy]
  exact ((f.copy a (g * w)).le_iff b c).mpr hbc

theorem translate_le_iff (g : External J f.Letters) (x y : f.Node a) :
    (f.gluedOrder a).le (f.translate a g x) (f.translate a g y) ↔ (f.gluedOrder a).le x y := by
  constructor
  · intro h
    have back := f.translate_monotone a g⁻¹ _ _ h
    rw [f.translate_left_inverse, f.translate_left_inverse] at back
    exact back
  · exact f.translate_monotone a g x y

noncomputable def externalIso (g : External J f.Letters) : MeetIso (f.gluedOrder a) (f.gluedOrder a) :=
  isoOfOrder (f.translate a g) (f.translate a g⁻¹)
    (f.translate_left_inverse a g) (f.translate_right_inverse a g) (f.translate_le_iff a g)

noncomputable def externalAction : OrderAction (External J f.Letters) (f.gluedOrder a) where
  iso := f.externalIso a
  one := f.translate_one a
  mul := f.translate_mul a

theorem externalAction_copy (g w : External J f.Letters) (x : A) :
    ((f.externalAction a).iso g).toFun ((f.copy a w).toFun x) =
      (f.copy a (g * w)).toFun x := f.translate_copy a g w x

theorem externalAction_meet (g : External J f.Letters) (x y : f.Node a) :
    ((f.externalAction a).iso g).toFun ((f.gluedOrder a).meet x y) =
      (f.gluedOrder a).meet (((f.externalAction a).iso g).toFun x)
        (((f.externalAction a).iso g).toFun y) :=
  ((f.externalAction a).iso g).map_meet x y

theorem extends_old_action (j : J) (x : A) :
    ((f.externalAction a).iso (old J f.Letters j)).toFun ((f.copy a 1).toFun x) =
      (f.copy a 1).toFun ((a.iso j).toFun x) := by
  rw [f.externalAction_copy, mul_one]
  simpa only [one_mul] using f.copy_coordinate a 1 j x

theorem generator_on_root (s : f.Letters) (x : A) :
    ((f.externalAction a).iso (generator J f.Letters s)).toFun ((f.copy a 1).toFun x) =
      (f.copy a (generator J f.Letters s)).toFun x := by
  rw [f.externalAction_copy, mul_one]

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

end

end OAI
