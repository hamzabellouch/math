import OAI.SetTheory.PartitionPrinciple.Models.IncidenceQuotient

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps

namespace TileRequests.Family

open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

def fullIdeal : MeetIso (idealOrder P f.top) P where
  toFun := Subtype.val
  le_iff _ _ := Iff.rfl
  map_meet _ _ := rfl
  inverse x := ⟨x, f.greatest x⟩
  left_inverse _ := rfl
  right_inverse _ := rfl

noncomputable def vertexIdealIso {B : Type u} {Q : MeetOrder B} (i : IdealEmbedding P Q) :
    MeetIso P (idealOrder Q (i.toFun f.top)) :=
  RootedGluing.chainIso (inverseIso f.fullIdeal) (i.principalIso f.top)

def Space : TileStars.Vertex J f.Letters R → Type u
  | .inl _ => A
  | .inr c => (f.tile c.2).Space

noncomputable def localOrder : (v : TileStars.Vertex J f.Letters R) → MeetOrder (f.Space v)
  | .inl _ => P
  | .inr c => (f.tile c.2).order

noncomputable def leftAnchor (e : TileStars.Edge J f.Letters R) :
    f.Space (TileStars.source J f.Letters R Sigma.fst (e, true)) := by
  cases e with
  | inl c => exact f.top
  | inr e => exact ((f.tile e.2.1).child e.2.2).toFun f.top

noncomputable def rightAnchor (e : TileStars.Edge J f.Letters R) :
    f.Space (TileStars.target J f.Letters R Sigma.fst (e, true)) := by
  cases e with
  | inl c => exact (f.tile c.2).root.toFun f.top
  | inr e => exact f.top

noncomputable def edgeOverlap (e : TileStars.Edge J f.Letters R) : MeetIso
    (idealOrder (f.localOrder (TileStars.source J f.Letters R Sigma.fst (e, true))) (f.leftAnchor e))
    (idealOrder (f.localOrder (TileStars.target J f.Letters R Sigma.fst (e, true))) (f.rightAnchor e)) := by
  cases e with
  | inl c =>
    exact RootedGluing.chainIso f.fullIdeal (RootedGluing.chainIso
      (inverseIso (a.chart c.1)) (f.vertexIdealIso (f.tile c.2).root))
  | inr e =>
    exact RootedGluing.chainIso (inverseIso (f.vertexIdealIso ((f.tile e.2.1).child e.2.2)))
      (RootedGluing.chainIso (a.chart (e.1 * generator J f.Letters e.2)) (inverseIso f.fullIdeal))

noncomputable def diagram : TileStars.Spaces J f.Letters R Sigma.fst where
  Space := f.Space
  order := f.localOrder
  leftAnchor := f.leftAnchor
  rightAnchor := f.rightAnchor
  overlap := f.edgeOverlap a

def Node := (f.diagram a).Node
noncomputable def gluedOrder : MeetOrder (f.Node a) := (f.diagram a).gluedOrder

noncomputable def copy (w : External J f.Letters) : IdealEmbedding P (f.gluedOrder a) :=
  (a.ideal (coordinate J f.Letters w)).comp ((f.diagram a).vertex (.inl (point J f.Letters w)))

noncomputable def placedTile (w : External J f.Letters) (r : R) :
    IdealEmbedding (f.tile r).order (f.gluedOrder a) := (f.diagram a).vertex (.inr (w, r))

theorem copy_coordinate (w : External J f.Letters) (j : J) (x : A) :
    (f.copy a (w * old J f.Letters j)).toFun x = (f.copy a w).toFun ((a.iso j).toFun x) := by
  change ((f.diagram a).vertex (.inl (point J f.Letters (w * old J f.Letters j)))).toFun
    ((a.chart (w * old J f.Letters j)).toFun x) = _
  rw [point_mul_old, a.chart_mul_old]
  rfl

theorem copy_one (x : A) : (f.copy a 1).toFun x =
    ((f.diagram a).vertex (.inl (root J f.Letters))).toFun x := by
  change ((f.diagram a).vertex (.inl (root J f.Letters))).toFun ((a.chart 1).toFun x) = _
  rw [a.chart_one]

theorem stem_formula (w : External J f.Letters) (r : R) (x : A) :
    ((f.edgeOverlap a (.inl (w, r))).toFun ⟨(a.chart w).toFun x, f.greatest _⟩).val =
      (f.tile r).root.toFun x := by
  change (f.tile r).root.toFun ((a.chart w).inverse ((a.chart w).toFun x)) = _
  rw [(a.chart w).left_inverse]

theorem branch_formula (w : External J f.Letters) (r : R) (j : f.Child r) (x : A) :
    ((f.edgeOverlap a (.inr (w, ⟨r, j⟩))).toFun
      ⟨((f.tile r).child j).toFun x, (((f.tile r).child j).le_iff _ _).mpr (f.greatest x)⟩).val =
      (a.chart (w * generator J f.Letters ⟨r, j⟩)).toFun x := by
  have inv := (f.vertexIdealIso ((f.tile r).child j)).left_inverse x
  change (a.chart (w * generator J f.Letters ⟨r, j⟩)).toFun
    ((f.vertexIdealIso ((f.tile r).child j)).inverse
      ((f.vertexIdealIso ((f.tile r).child j)).toFun x)) = _
  rw [inv]

theorem root_identification (w : External J f.Letters) (r : R) (x : A) :
    (f.placedTile a w r).toFun ((f.tile r).root.toFun x) = (f.copy a w).toFun x := by
  have eq := (f.diagram a).edge_identification (.inl (w, r), true)
    ⟨(a.chart w).toFun x, f.greatest _⟩
  change (f.copy a w).toFun x = (f.placedTile a w r).toFun
    ((f.edgeOverlap a (.inl (w, r))).toFun ⟨(a.chart w).toFun x, f.greatest _⟩).val at eq
  rw [f.stem_formula] at eq
  exact eq.symm

theorem child_identification (w : External J f.Letters) (r : R) (j : f.Child r) (x : A) :
    (f.placedTile a w r).toFun (((f.tile r).child j).toFun x) =
      (f.copy a (w * generator J f.Letters ⟨r, j⟩)).toFun x := by
  have eq := (f.diagram a).edge_identification (.inr (w, ⟨r, j⟩), true)
    ⟨((f.tile r).child j).toFun x, (((f.tile r).child j).le_iff _ _).mpr (f.greatest x)⟩
  change (f.placedTile a w r).toFun (((f.tile r).child j).toFun x) =
    ((f.diagram a).vertex (.inl (point J f.Letters (w * generator J f.Letters ⟨r, j⟩)))).toFun
      ((f.edgeOverlap a (.inr (w, ⟨r, j⟩))).toFun
        ⟨((f.tile r).child j).toFun x, (((f.tile r).child j).le_iff _ _).mpr (f.greatest x)⟩).val at eq
  rw [f.branch_formula] at eq
  exact eq

theorem copy_principal (w : External J f.Letters) (z : f.Node a) :
    (f.gluedOrder a).le z ((f.copy a w).toFun f.top) ↔ ∃ x, (f.copy a w).toFun x = z :=
  (f.copy a w).principal f.top f.greatest z

theorem copy_greatest_part (w : External J f.Letters) (z : f.Node a) (x : A) :
    (f.gluedOrder a).le ((f.copy a w).toFun x) z ↔
      P.le x ((f.copy a w).projection f.top z) :=
  (f.copy a w).greatest_part f.top f.greatest z x

theorem copy_cover (z : f.Node a) : ∃ w x, (f.copy a w).toFun x = z := by
  rcases (f.diagram a).cover z with ⟨v, x, rfl⟩
  cases v with
  | inl v =>
    refine ⟨representative J f.Letters v, (a.chart (representative J f.Letters v)).inverse x, ?_⟩
    change ((f.diagram a).vertex (.inl (point J f.Letters (representative J f.Letters v)))).toFun
      ((a.chart (representative J f.Letters v)).toFun
        ((a.chart (representative J f.Letters v)).inverse x)) = _
    erw [(a.chart (representative J f.Letters v)).right_inverse, representative_spec]
  | inr c =>
    rcases (f.tile c.2).cover x with ⟨y, rfl⟩ | ⟨j, y, rfl⟩
    · exact ⟨c.1, y, (f.root_identification a c.1 c.2 y).symm⟩
    · exact ⟨c.1 * generator J f.Letters ⟨c.2, j⟩, y,
        (f.child_identification a c.1 c.2 j y).symm⟩

theorem comparison_in_copy (x y : f.Node a) (h : (f.gluedOrder a).le x y) :
    ∃ w b c, (f.copy a w).toFun b = x ∧ (f.copy a w).toFun c = y ∧ P.le b c := by
  rcases f.copy_cover a y with ⟨w, c, rfl⟩
  rcases (f.copy a w).ideal c x h with ⟨b, rfl⟩
  exact ⟨w, b, c, rfl, rfl, ((f.copy a w).le_iff b c).mp h⟩

theorem copy_injective (w : External J f.Letters) (x y : A) :
    (f.copy a w).toFun x = (f.copy a w).toFun y ↔ x = y := by
  constructor
  · exact embedding_injective (f.copy a w).toMeetEmbedding
  · exact congrArg (f.copy a w).toFun

end TileRequests.Family



namespace TileRequests

open Attachment CosetGeometry
universe u
variable {A J : Type u} [Group J] {P : MeetOrder A}

namespace Family
variable {R : Type u} (f : Family P R) (a : OrderAction J P)

theorem transfer_child_root (w : External J f.Letters) (r : R) (j : f.Child r) (x y : A)
    (h : ((f.tile r).child j).toFun x = (f.tile r).root.toFun y) :
    (f.copy a (w * generator J f.Letters ⟨r, j⟩)).toFun x = (f.copy a w).toFun y := by
  rw [← f.child_identification, ← f.root_identification, h]

theorem transfer_child_root_meet (w : External J f.Letters) (r : R) (j : f.Child r) (x y z : A)
    (h : (f.tile r).order.meet (((f.tile r).child j).toFun x) ((f.tile r).root.toFun y) =
      (f.tile r).root.toFun z) :
    (f.gluedOrder a).meet ((f.copy a (w * generator J f.Letters ⟨r, j⟩)).toFun x)
      ((f.copy a w).toFun y) = (f.copy a w).toFun z := by
  rw [← f.child_identification, ← f.root_identification, ← f.root_identification,
    ← (f.placedTile a w r).map_meet, h]

theorem transfer_child_child_meet (w : External J f.Letters) (r : R)
    (j k : f.Child r) (x y z : A)
    (h : (f.tile r).order.meet (((f.tile r).child j).toFun x) (((f.tile r).child k).toFun y) =
      ((f.tile r).child j).toFun z) :
    (f.gluedOrder a).meet ((f.copy a (w * generator J f.Letters ⟨r, j⟩)).toFun x)
      ((f.copy a (w * generator J f.Letters ⟨r, k⟩)).toFun y) =
      (f.copy a (w * generator J f.Letters ⟨r, j⟩)).toFun z := by
  rw [← f.child_identification, ← f.child_identification, ← f.child_identification,
    ← (f.placedTile a w r).map_meet, h]

end Family

namespace AllGeometry
variable (T : A) (greatest : ∀ x, P.le x T) (a : OrderAction J P)

noncomputable abbrev family : Family P (Request P) := Family.all T greatest
abbrev Letters := (family T greatest).Letters

theorem separation_fixes (w : External J (Letters T greatest)) (W x : A) (below : P.le x W) :
    ((family T greatest).copy a
      (w * generator J (Letters T greatest) ⟨.separation W, ⟨()⟩⟩)).toFun x =
      ((family T greatest).copy a w).toFun x :=
  (family T greatest).transfer_child_root a w (.separation W) ⟨()⟩ x x
    (Request.separation_agrees T greatest W x below)

theorem separation_meet (w : External J (Letters T greatest)) (W D X : A)
    (belowD : P.le W D) (belowX : P.le W X) :
    ((family T greatest).gluedOrder a).meet
      (((family T greatest).copy a
        (w * generator J (Letters T greatest) ⟨.separation W, ⟨()⟩⟩)).toFun D)
      (((family T greatest).copy a w).toFun X) = ((family T greatest).copy a w).toFun W :=
  (family T greatest).transfer_child_root_meet a w (.separation W) ⟨()⟩ D X W
    (BinaryTiles.separation_cross_meet P W D X belowD belowX)

theorem compression_restriction (w : External J (Letters T greatest)) (K : A)
    (S : MeetIso P (idealOrder P K)) (x : A) :
    ((family T greatest).copy a
      (w * generator J (Letters T greatest) ⟨.compression K S, ⟨()⟩⟩)).toFun x =
      ((family T greatest).copy a w).toFun (S.toFun x).val :=
  (family T greatest).transfer_child_root a w (.compression K S) ⟨()⟩ x (S.toFun x).val
    (Request.compression_agrees T greatest K S x)

theorem compression_top (w : External J (Letters T greatest)) (K : A)
    (S : MeetIso P (idealOrder P K)) :
    ((family T greatest).copy a
      (w * generator J (Letters T greatest) ⟨.compression K S, ⟨()⟩⟩)).toFun T =
      ((family T greatest).copy a w).toFun K :=
  (family T greatest).transfer_child_root a w (.compression K S) ⟨()⟩ T K
    (BinaryTiles.compression_top P T K greatest S)

theorem rectangle_first_agrees (w : External J (Letters T greatest)) (r : Rectangle.Input P)
    (x : A) (below : P.le x r.C) :
    ((family T greatest).copy a
      (w * generator J (Letters T greatest) ⟨.rectangle r, ⟨false⟩⟩)).toFun x =
      ((family T greatest).copy a w).toFun (r.g1.toFun x) :=
  (family T greatest).transfer_child_root a w (.rectangle r) ⟨false⟩ x (r.g1.toFun x)
    (r.first_agrees x below)

theorem rectangle_second_agrees (w : External J (Letters T greatest)) (r : Rectangle.Input P)
    (x : A) (below : P.le x r.C) :
    ((family T greatest).copy a
      (w * generator J (Letters T greatest) ⟨.rectangle r, ⟨true⟩⟩)).toFun x =
      ((family T greatest).copy a w).toFun (r.g2.toFun x) :=
  (family T greatest).transfer_child_root a w (.rectangle r) ⟨true⟩ x (r.g2.toFun x)
    (r.second_agrees x below)

theorem rectangle_children_intersection (w : External J (Letters T greatest))
    (r : Rectangle.Input P) (x y : A) :
    ((family T greatest).copy a
      (w * generator J (Letters T greatest) ⟨.rectangle r, ⟨false⟩⟩)).toFun x =
      ((family T greatest).copy a
        (w * generator J (Letters T greatest) ⟨.rectangle r, ⟨true⟩⟩)).toFun y ↔
        P.le x r.B ∧ x = y := by
  erw [← (family T greatest).child_identification, ← (family T greatest).child_identification]
  constructor
  · intro h
    exact (r.children_intersection x y).mp
      (embedding_injective ((family T greatest).placedTile a w (.rectangle r)).toMeetEmbedding h)
  · intro h
    exact congrArg ((family T greatest).placedTile a w (.rectangle r)).toFun
      ((r.children_intersection x y).mpr h)

theorem rectangle_first_meet_root (w : External J (Letters T greatest))
    (r : Rectangle.Input P) (x : A) :
    ((family T greatest).gluedOrder a).meet
      (((family T greatest).copy a
        (w * generator J (Letters T greatest) ⟨.rectangle r, ⟨false⟩⟩)).toFun r.D)
      (((family T greatest).copy a w).toFun x) =
      ((family T greatest).copy a w).toFun (P.meet (r.g1.toFun r.C) x) :=
  (family T greatest).transfer_child_root_meet a w (.rectangle r) ⟨false⟩ r.D x _
    (r.first_meet_root x)

theorem rectangle_second_meet_root (w : External J (Letters T greatest))
    (r : Rectangle.Input P) (x : A) :
    ((family T greatest).gluedOrder a).meet
      (((family T greatest).copy a
        (w * generator J (Letters T greatest) ⟨.rectangle r, ⟨true⟩⟩)).toFun r.D)
      (((family T greatest).copy a w).toFun x) =
      ((family T greatest).copy a w).toFun (P.meet (r.g2.toFun r.C) x) :=
  (family T greatest).transfer_child_root_meet a w (.rectangle r) ⟨true⟩ r.D x _
    (r.second_meet_root x)

theorem rectangle_children_meet (w : External J (Letters T greatest)) (r : Rectangle.Input P) :
    ((family T greatest).gluedOrder a).meet
      (((family T greatest).copy a
        (w * generator J (Letters T greatest) ⟨.rectangle r, ⟨false⟩⟩)).toFun r.D)
      (((family T greatest).copy a
        (w * generator J (Letters T greatest) ⟨.rectangle r, ⟨true⟩⟩)).toFun r.D) =
      ((family T greatest).copy a
        (w * generator J (Letters T greatest) ⟨.rectangle r, ⟨false⟩⟩)).toFun r.B :=
  (family T greatest).transfer_child_child_meet a w (.rectangle r) ⟨false⟩ ⟨true⟩ r.D r.D r.B
    r.children_meet

end AllGeometry

end TileRequests



namespace CosetGeometry.TileStars.Spaces

universe u
variable {J S R : Type u} [Group J] {request : S → R} (g : Spaces J S R request)
variable {B : Type u} (value : ∀ v, g.Space v → B)
variable (edges : ∀ d, g.Equation value d)

include edges in
theorem values_respect_parents {x y : g.scheme.Label} (h : g.scheme.Related x y) :
    value x.1 x.2 = value y.1 y.2 := by
  induction h with
  | parent v hv x => exact g.parents_of_equations value edges v hv x
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

noncomputable def descend (z : g.Node) : B :=
  Quotient.lift (fun x => value x.1 x.2)
    (fun _ _ h => g.values_respect_parents value edges h) (g.scheme.toGenerated z)

theorem descend_vertex (v : Vertex J S R) (x : g.Space v) :
    g.descend value edges ((g.vertex v).toFun x) = value v x := by
  change Quotient.lift _ _ (g.scheme.toGenerated ((g.scheme.vertex v).toFun x)) = _
  erw [g.scheme.toGenerated_vertex]
  rfl

theorem descend_unique (h : g.Node → B) (vertices : ∀ v x, h ((g.vertex v).toFun x) = value v x) :
    h = g.descend value edges := by
  funext z
  rcases g.cover z with ⟨v, x, rfl⟩
  exact (vertices v x).trans (g.descend_vertex value edges v x).symm

end CosetGeometry.TileStars.Spaces



namespace TileRequests.Family

open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

noncomputable def translationValue (g : External J f.Letters) :
    (v : TileStars.Vertex J f.Letters R) → f.Space v → f.Node a
  | .inl v, x => (f.copy a (g * representative J f.Letters v)).toFun x
  | .inr c, x => (f.placedTile a (g * c.1) c.2).toFun x

theorem translationValue_copy (g w : External J f.Letters) (x : A) :
    f.translationValue a g (.inl (point J f.Letters w)) ((a.chart w).toFun x) =
      (f.copy a (g * w)).toFun x := by
  change (f.copy a (g * representative J f.Letters (point J f.Letters w))).toFun
    ((a.iso (coordinate J f.Letters w)).toFun x) = _
  rw [← f.copy_coordinate, mul_assoc, coordinate_spec]

theorem translation_stem (g w : External J f.Letters) (r : R) :
    (f.diagram a).Equation (f.translationValue a g) (.inl (w, r), true) := by
  intro x
  change f.translationValue a g (.inl (point J f.Letters w)) x.val =
    (f.placedTile a (g * w) r).toFun ((f.tile r).root.toFun ((a.chart w).inverse x.val))
  rw [f.root_identification]
  have eq := f.translationValue_copy a g w ((a.chart w).inverse x.val)
  erw [(a.chart w).right_inverse] at eq
  exact eq

theorem translation_branch (g w : External J f.Letters) (r : R) (j : f.Child r) :
    (f.diagram a).Equation (f.translationValue a g) (.inr (w, ⟨r, j⟩), true) := by
  intro x
  let i := f.vertexIdealIso ((f.tile r).child j)
  obtain ⟨y, rfl⟩ : ∃ y, i.toFun y = x := ⟨i.inverse x, i.right_inverse x⟩
  change (f.placedTile a (g * w) r).toFun (((f.tile r).child j).toFun y) =
    f.translationValue a g (.inl (point J f.Letters (w * generator J f.Letters ⟨r, j⟩)))
      ((f.edgeOverlap a (.inr (w, ⟨r, j⟩))).toFun (i.toFun y)).val
  have formula : ((f.edgeOverlap a (.inr (w, ⟨r, j⟩))).toFun (i.toFun y)).val =
      (a.chart (w * generator J f.Letters ⟨r, j⟩)).toFun y := f.branch_formula a w r j y
  rw [formula, f.translationValue_copy, ← mul_assoc]
  exact f.child_identification a (g * w) r j y

theorem translation_edges (g : External J f.Letters) (d : TileStars.Dart J f.Letters R) :
    (f.diagram a).Equation (f.translationValue a g) d := by
  rcases d with ⟨e, b⟩
  have forward : (f.diagram a).Equation (f.translationValue a g) (e, true) := by
    cases e with
    | inl c => exact f.translation_stem a g c.1 c.2
    | inr c => exact f.translation_branch a g c.1 c.2.1 c.2.2
  cases b
  · exact (f.diagram a).equation_of_reverse (f.translationValue a g) (e, false) forward
  · exact forward

noncomputable def translate (g : External J f.Letters) : f.Node a → f.Node a :=
  (f.diagram a).descend (f.translationValue a g) (f.translation_edges a g)

theorem translate_vertex (g : External J f.Letters) (v : TileStars.Vertex J f.Letters R)
    (x : f.Space v) :
    f.translate a g (((f.diagram a).vertex v).toFun x) = f.translationValue a g v x :=
  (f.diagram a).descend_vertex (f.translationValue a g) (f.translation_edges a g) v x

theorem translate_copy (g w : External J f.Letters) (x : A) :
    f.translate a g ((f.copy a w).toFun x) = (f.copy a (g * w)).toFun x := by
  change f.translate a g (((f.diagram a).vertex (.inl (point J f.Letters w))).toFun
    ((a.chart w).toFun x)) = _
  erw [f.translate_vertex, f.translationValue_copy]

theorem translate_tile (g w : External J f.Letters) (r : R) (x : (f.tile r).Space) :
    f.translate a g ((f.placedTile a w r).toFun x) = (f.placedTile a (g * w) r).toFun x :=
  f.translate_vertex a g (.inr (w, r)) x

end TileRequests.Family

end PartitionPilot.Compression.RecursiveMaps

end OAI
