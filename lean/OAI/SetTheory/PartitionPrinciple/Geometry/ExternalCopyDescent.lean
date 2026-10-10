import OAI.SetTheory.PartitionPrinciple.Definability.ExternalCopyRelations

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family
open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

noncomputable def flatTileValue (w : External J f.Letters) (r : R)
    (z : (f.tile r).Space) : f.FlatQuotient a :=
  f.flatClass a (f.flatWord w r (Classical.choose (f.flatVertex_cover r z)))
    (Classical.choose (Classical.choose_spec (f.flatVertex_cover r z)))

theorem flatTileValue_vertex (w : External J f.Letters) (r : R)
    (i : Option (f.Child r)) (x : A) :
    f.flatTileValue a w r ((f.flatVertex r i).toFun x) =
      f.flatClass a (f.flatWord w r i) x := by
  unfold flatTileValue
  apply f.flatClass_tile a
  exact Classical.choose_spec (Classical.choose_spec (f.flatVertex_cover r _))

noncomputable def flatIncidenceValue :
    (v : TileStars.Vertex J f.Letters R) → f.Space v → f.FlatQuotient a
  | .inl v, x => f.flatClass a (representative J f.Letters v) x
  | .inr c, x => f.flatTileValue a c.1 c.2 x

theorem flatIncidenceValue_copy (w : External J f.Letters) (x : A) :
    f.flatIncidenceValue a (.inl (point J f.Letters w)) ((a.chart w).toFun x) =
      f.flatClass a w x := by
  change f.flatClass a (representative J f.Letters (point J f.Letters w))
    ((a.iso (coordinate J f.Letters w)).toFun x) = _
  rw [← f.flatClass_coordinate, coordinate_spec]

theorem flatIncidence_stem (w : External J f.Letters) (r : R) :
    (f.diagram a).Equation (f.flatIncidenceValue a) (.inl (w, r), true) := by
  intro x
  change f.flatIncidenceValue a (.inl (point J f.Letters w)) x.val =
    f.flatTileValue a w r ((f.tile r).root.toFun ((a.chart w).inverse x.val))
  have vertex := f.flatTileValue_vertex a w r none ((a.chart w).inverse x.val)
  change f.flatTileValue a w r ((f.tile r).root.toFun ((a.chart w).inverse x.val)) =
    f.flatClass a w ((a.chart w).inverse x.val) at vertex
  rw [vertex]
  have eq := f.flatIncidenceValue_copy a w ((a.chart w).inverse x.val)
  erw [(a.chart w).right_inverse] at eq
  exact eq

theorem flatIncidence_branch (w : External J f.Letters) (r : R) (j : f.Child r) :
    (f.diagram a).Equation (f.flatIncidenceValue a) (.inr (w, ⟨r, j⟩), true) := by
  intro x
  let i := f.vertexIdealIso ((f.tile r).child j)
  obtain ⟨y, rfl⟩ : ∃ y, i.toFun y = x := ⟨i.inverse x, i.right_inverse x⟩
  change f.flatTileValue a w r (((f.tile r).child j).toFun y) =
    f.flatIncidenceValue a (.inl (point J f.Letters (w * generator J f.Letters ⟨r, j⟩)))
      ((f.edgeOverlap a (.inr (w, ⟨r, j⟩))).toFun (i.toFun y)).val
  have formula : ((f.edgeOverlap a (.inr (w, ⟨r, j⟩))).toFun (i.toFun y)).val =
      (a.chart (w * generator J f.Letters ⟨r, j⟩)).toFun y := f.branch_formula a w r j y
  rw [formula, f.flatIncidenceValue_copy]
  exact f.flatTileValue_vertex a w r (some j) y

theorem flatIncidence_edges (d : TileStars.Dart J f.Letters R) :
    (f.diagram a).Equation (f.flatIncidenceValue a) d := by
  rcases d with ⟨e, b⟩
  have forward : (f.diagram a).Equation (f.flatIncidenceValue a) (e, true) := by
    cases e with
    | inl c => exact f.flatIncidence_stem a c.1 c.2
    | inr c => exact f.flatIncidence_branch a c.1 c.2.1 c.2.2
  cases b
  · exact (f.diagram a).equation_of_reverse (f.flatIncidenceValue a) (e, false) forward
  · exact forward

noncomputable def toFlatQuotient (z : f.Node a) : f.FlatQuotient a :=
  (f.diagram a).descend (f.flatIncidenceValue a) (f.flatIncidence_edges a) z

theorem toFlatQuotient_copy (w : External J f.Letters) (x : A) :
    f.toFlatQuotient a ((f.copy a w).toFun x) = f.flatClass a w x := by
  change (f.diagram a).descend (f.flatIncidenceValue a) (f.flatIncidence_edges a)
    (((f.diagram a).vertex (.inl (point J f.Letters w))).toFun ((a.chart w).toFun x)) = _
  erw [(f.diagram a).descend_vertex, f.flatIncidenceValue_copy]

theorem flatPath_iff_copy_eq (x y : f.FlatLabel (J := J)) :
    f.FlatPath a x y ↔ (f.copy a x.1).toFun x.2 = (f.copy a y.1).toFun y.2 := by
  constructor
  · exact FlatPath.copy_eq f a
  · intro equal
    have classes := congrArg (f.toFlatQuotient a) equal
    rw [f.toFlatQuotient_copy, f.toFlatQuotient_copy] at classes
    exact Quotient.exact classes

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

end

end OAI
