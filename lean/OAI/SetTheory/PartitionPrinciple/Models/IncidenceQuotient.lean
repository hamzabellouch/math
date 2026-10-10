import OAI.SetTheory.PartitionPrinciple.Geometry.GluingHeights

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars.Spaces

universe u
variable {J S R : Type u} [Group J] {request : S → R} (g : Spaces J S R request)
variable {B : Type u} (value : ∀ v, g.Space v → B)

theorem realizes_of_equation (d : Dart J S R) (h : g.Equation value d) :
    g.Realizes value (source J S R request d) (target J S R request d) (g.edgeInput d) := by
  intro x
  have eq := h ((g.arrow d).inverse x)
  erw [(g.arrow d).right_inverse] at eq
  exact eq.symm

theorem parents_of_equations (edges : ∀ d, g.Equation value d)
    (v : Vertex J S R) (h : depth J S R request v ≠ 0) :
    g.Realizes value (parent J S R request v) v (g.localGlue v h) := by
  have nonroot : v ≠ root J S R := fun eq => h ((depth_zero_iff J S R request v).mpr eq)
  exact (g.realizes_reindex value (parent_eq J S R request v nonroot).symm
    (incoming_target J S R request v nonroot) _).mpr
      (g.realizes_of_equation value _ (edges _))

inductive EdgeRelated : g.scheme.Label → g.scheme.Label → Prop
  | edge (d : Dart J S R)
      (x : {x : g.Space (source J S R request d) //
        (g.order (source J S R request d)).le x (g.anchor d)}) :
      EdgeRelated ⟨source J S R request d, x.val⟩
        ⟨target J S R request d, ((g.arrow d).toFun x).val⟩
  | refl (x) : EdgeRelated x x
  | symm {x y} : EdgeRelated x y → EdgeRelated y x
  | trans {x y z} : EdgeRelated x y → EdgeRelated y z → EdgeRelated x z

def edgeSetoid : Setoid g.scheme.Label :=
  ⟨g.EdgeRelated, EdgeRelated.refl, EdgeRelated.symm, EdgeRelated.trans⟩

def EdgeQuotient := Quotient g.edgeSetoid
def edgeClass (v : Vertex J S R) (x : g.Space v) : g.EdgeQuotient :=
  Quotient.mk g.edgeSetoid ⟨v, x⟩

theorem edge_class_equation (d : Dart J S R) : g.Equation g.edgeClass d :=
  fun x => Quotient.sound (EdgeRelated.edge d x)

theorem parent_related_edge {x y : g.scheme.Label} (h : g.scheme.Related x y) :
    g.EdgeRelated x y := by
  induction h with
  | parent v hv x =>
    exact Quotient.exact (g.parents_of_equations g.edgeClass g.edge_class_equation v hv x)
  | refl => exact EdgeRelated.refl _
  | symm h ih => exact EdgeRelated.symm ih
  | trans h1 h2 ih1 ih2 => exact EdgeRelated.trans ih1 ih2

theorem edge_related_sound {x y : g.scheme.Label} (h : g.EdgeRelated x y) :
    (g.vertex x.1).toFun x.2 = (g.vertex y.1).toFun y.2 := by
  induction h with
  | edge d x => exact g.edge_identification d x
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem exact_edge_identifications (v w : Vertex J S R) (x : g.Space v) (y : g.Space w) :
    (g.vertex v).toFun x = (g.vertex w).toFun y ↔ g.EdgeRelated ⟨v, x⟩ ⟨w, y⟩ := by
  constructor
  · intro eq
    exact g.parent_related_edge ((g.scheme.exact_identifications v w x y).mp eq)
  · exact g.edge_related_sound

theorem edge_related_iff_parent (x y : g.scheme.Label) :
    g.EdgeRelated x y ↔ g.scheme.Related x y := by
  constructor
  · intro h
    exact (g.scheme.exact_identifications x.1 y.1 x.2 y.2).mp (g.edge_related_sound h)
  · exact g.parent_related_edge

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars.Spaces

end

end OAI
