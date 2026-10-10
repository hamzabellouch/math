import OAI.SetTheory.PartitionPrinciple.Geometry.ExternalCopyDescent

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family
open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

noncomputable def fromFlatQuotient : f.FlatQuotient a → f.Node a :=
  Quotient.lift (fun x => (f.copy a x.1).toFun x.2)
    (fun _ _ path => FlatPath.copy_eq f a path)

theorem fromFlatQuotient_class (w : External J f.Letters) (x : A) :
    f.fromFlatQuotient a (f.flatClass a w x) = (f.copy a w).toFun x := rfl

noncomputable def flatQuotientEquiv : f.FlatQuotient a ≃ f.Node a where
  toFun := f.fromFlatQuotient a
  invFun := f.toFlatQuotient a
  left_inv q := by
    induction q using Quotient.ind with
    | _ x => exact f.toFlatQuotient_copy a x.1 x.2
  right_inv z := by
    obtain ⟨w, x, rfl⟩ := f.copy_cover a z
    rw [f.toFlatQuotient_copy, f.fromFlatQuotient_class]

theorem flatQuotientEquiv_class (w : External J f.Letters) (x : A) :
    f.flatQuotientEquiv a (f.flatClass a w x) = (f.copy a w).toFun x := rfl

theorem FlatPath.translate (g : External J f.Letters) {x y : f.FlatLabel (J := J)}
    (path : f.FlatPath a x y) :
    f.FlatPath a (g * x.1, x.2) (g * y.1, y.2) := by
  apply (f.flatPath_iff_copy_eq a _ _).2
  have equal := congrArg (f.translate a g) ((f.flatPath_iff_copy_eq a x y).1 path)
  simpa only [f.translate_copy] using equal

theorem flatPath_translate_iff (g : External J f.Letters) (x y : f.FlatLabel (J := J)) :
    f.FlatPath a (g * x.1, x.2) (g * y.1, y.2) ↔ f.FlatPath a x y := by
  constructor
  · intro path
    have inverse := FlatPath.translate f a g⁻¹ path
    simpa only [Prod.fst, Prod.snd, inv_mul_cancel_left] using inverse
  · exact FlatPath.translate f a g

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

end

end OAI
