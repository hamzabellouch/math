import OAI.SetTheory.PartitionPrinciple.Forcing.ExternalAction

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family
open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

abbrev FlatLabel := External J f.Letters × A

noncomputable def flatVertex (r : R) : Option (f.Child r) → IdealEmbedding P (f.tile r).order
  | none => (f.tile r).root
  | some j => (f.tile r).child j

def flatWord (w : External J f.Letters) (r : R) : Option (f.Child r) → External J f.Letters
  | none => w
  | some j => w * generator J f.Letters ⟨r, j⟩

theorem flatVertex_cover (r : R) (z : (f.tile r).Space) :
    ∃ i x, (f.flatVertex r i).toFun x = z := by
  rcases (f.tile r).cover z with ⟨x, eq⟩ | ⟨j, x, eq⟩
  · exact ⟨none, x, eq⟩
  · exact ⟨some j, x, eq⟩

theorem flatVertex_copy (w : External J f.Letters) (r : R) (i : Option (f.Child r)) (x : A) :
    (f.placedTile a w r).toFun ((f.flatVertex r i).toFun x) =
      (f.copy a (f.flatWord w r i)).toFun x := by
  cases i with
  | none => exact f.root_identification a w r x
  | some j => exact f.child_identification a w r j x

inductive FlatStep : f.FlatLabel (J := J) → f.FlatLabel (J := J) → Prop
  | coordinate (w : External J f.Letters) (j : J) (x : A) :
      FlatStep (w * old J f.Letters j, x) (w, (a.iso j).toFun x)
  | tile (w : External J f.Letters) (r : R) (i j : Option (f.Child r)) (x y : A)
      (equal : (f.flatVertex r i).toFun x = (f.flatVertex r j).toFun y) :
      FlatStep (f.flatWord w r i, x) (f.flatWord w r j, y)
  | symm {x y} : FlatStep x y → FlatStep y x

def FlatPath : f.FlatLabel (J := J) → f.FlatLabel (J := J) → Prop := Relation.ReflTransGen (f.FlatStep a)

theorem FlatPath.symm {x y : f.FlatLabel (J := J)} (h : f.FlatPath a x y) : f.FlatPath a y x := by
  let : Std.Symm (f.FlatStep a) := ⟨fun _ _ step => FlatStep.symm step⟩
  exact (Relation.ReflTransGen.stdSymm (r := f.FlatStep a)).symm x y h

theorem FlatStep.copy_eq {x y : f.FlatLabel (J := J)} (h : f.FlatStep a x y) :
    (f.copy a x.1).toFun x.2 = (f.copy a y.1).toFun y.2 := by
  induction h with
  | coordinate w j x => exact f.copy_coordinate a w j x
  | tile w r i j x y equal =>
    rw [← f.flatVertex_copy a w r i x, ← f.flatVertex_copy a w r j y, equal]
  | symm h ih => exact ih.symm

theorem FlatPath.copy_eq {x y : f.FlatLabel (J := J)} (h : f.FlatPath a x y) :
    (f.copy a x.1).toFun x.2 = (f.copy a y.1).toFun y.2 := by
  induction h with
  | refl => rfl
  | tail path step ih => exact ih.trans (FlatStep.copy_eq f a step)

def flatSetoid : Setoid (f.FlatLabel (J := J)) where
  r := f.FlatPath a
  iseqv := ⟨fun _ => Relation.ReflTransGen.refl,
    fun h => FlatPath.symm f a h, fun h k => h.trans k⟩

def FlatQuotient := Quotient (f.flatSetoid a)

def flatClass (w : External J f.Letters) (x : A) : f.FlatQuotient a :=
  Quotient.mk (f.flatSetoid a) (w, x)

theorem flatClass_coordinate (w : External J f.Letters) (j : J) (x : A) :
    f.flatClass a (w * old J f.Letters j) x = f.flatClass a w ((a.iso j).toFun x) :=
  Quotient.sound (Relation.ReflTransGen.single (FlatStep.coordinate w j x))

theorem flatClass_tile (w : External J f.Letters) (r : R) (i j : Option (f.Child r)) (x y : A)
    (equal : (f.flatVertex r i).toFun x = (f.flatVertex r j).toFun y) :
    f.flatClass a (f.flatWord w r i) x = f.flatClass a (f.flatWord w r j) y :=
  Quotient.sound (Relation.ReflTransGen.single (FlatStep.tile w r i j x y equal))

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

end

end OAI
