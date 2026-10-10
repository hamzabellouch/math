import OAI.SetTheory.PartitionPrinciple.Geometry.CompatibleCopies

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data

universe u v

variable {A : Type u} {I : Type v} {P : MeetOrder A} (d : Data P I)

def Node := Quotient d.setoid

def point (i : I) (x : A) : d.Node := Quotient.mk d.setoid (i, x)

def nodeLe : d.Node → d.Node → Prop :=
  Quotient.lift₂ d.Le (fun _ _ _ _ ha hb => propext
    ⟨fun h => d.le_trans (d.related_le (d.related_symm ha)) (d.le_trans h (d.related_le hb)),
     fun h => d.le_trans (d.related_le ha) (d.le_trans h (d.related_le (d.related_symm hb)))⟩)

theorem mk_le_mk (i j : I) (x y : A) : d.nodeLe (d.point i x) (d.point j y) ↔ d.Le (i, x) (j, y) :=
  Iff.rfl

theorem mk_eq_mk (i j : I) (x y : A) : d.point i x = d.point j y ↔ d.Related (i, x) (j, y) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem node_refl (x : d.Node) : d.nodeLe x x := by
  induction x using Quotient.ind with
  | _ x => exact d.le_refl x

theorem node_trans {x y z : d.Node} (hxy : d.nodeLe x y) (hyz : d.nodeLe y z) : d.nodeLe x z := by
  induction x, y, z using Quotient.inductionOn₃ with
  | _ x y z => exact d.le_trans hxy hyz

theorem node_antisymm {x y : d.Node} (hxy : d.nodeLe x y) (hyx : d.nodeLe y x) : x = y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ x y => exact Quotient.sound (d.le_antisymm_related hxy hyx)

theorem vertex_le (i : I) (x y : A) : d.nodeLe (d.point i x) (d.point i y) ↔ P.le x y :=
  d.same_vertex_le i x y

theorem vertex_below (i j : I) (x y : A) :
    d.nodeLe (d.point i x) (d.point j y) ↔ P.le x (d.part i j y) :=
  d.below_iff_part i j x y

theorem cover (x : d.Node) : ∃ i y, d.point i y = x := by
  induction x using Quotient.ind with
  | _ x => exact ⟨x.1, x.2, rfl⟩

theorem vertex_ideal (i : I) (y : A) (x : d.Node) (lower : d.nodeLe x (d.point i y)) :
    ∃ z, d.point i z = x := by
  induction x using Quotient.ind with
  | _ x =>
    have moved := d.move_to_upper_vertex lower
    exact ⟨(d.change x.1 i).toFun x.2, (Quotient.sound moved.1).symm⟩

def IsMeet (x y m : d.Node) : Prop :=
  d.nodeLe m x ∧ d.nodeLe m y ∧ ∀ z, d.nodeLe z x → d.nodeLe z y → d.nodeLe z m

theorem cross_meet_spec (i j : I) (x y : A) :
    d.IsMeet (d.point i x) (d.point j y) (d.point i (P.meet x (d.part i j y))) := by
  refine ⟨(d.vertex_le i _ _).mpr (P.meet_le_left _ _),
    (d.vertex_below i j _ _).mpr (P.meet_le_right _ _), ?_⟩
  intro z hx hy
  rcases d.vertex_ideal i x z hx with ⟨a, rfl⟩
  exact (d.vertex_le i _ _).mpr
    (P.le_meet ((d.vertex_le i _ _).mp hx) ((d.vertex_below i j _ _).mp hy))

theorem all_meets (x y : d.Node) : ∃ m, d.IsMeet x y m := by
  induction x, y using Quotient.inductionOn₂ with
  | _ x y => exact ⟨_, d.cross_meet_spec x.1 y.1 x.2 y.2⟩

noncomputable def order : MeetOrder d.Node where
  le := d.nodeLe
  meet x y := Classical.choose (d.all_meets x y)
  refl := d.node_refl
  trans := d.node_trans
  antisymm := d.node_antisymm
  meet_le_left x y := (Classical.choose_spec (d.all_meets x y)).1
  meet_le_right x y := (Classical.choose_spec (d.all_meets x y)).2.1
  le_meet hx hy := (Classical.choose_spec (d.all_meets _ _)).2.2 _ hx hy

theorem meet_eq {x y m : d.Node} (h : d.IsMeet x y m) : d.order.meet x y = m :=
  d.node_antisymm (h.2.2 _ (d.order.meet_le_left x y) (d.order.meet_le_right x y))
    (d.order.le_meet h.1 h.2.1)

theorem vertex_meet_spec (i : I) (x y : A) :
    d.IsMeet (d.point i x) (d.point i y) (d.point i (P.meet x y)) := by
  refine ⟨(d.vertex_le i _ _).mpr (P.meet_le_left _ _),
    (d.vertex_le i _ _).mpr (P.meet_le_right _ _), ?_⟩
  intro z hx hy
  rcases d.vertex_ideal i x z hx with ⟨a, rfl⟩
  exact (d.vertex_le i _ _).mpr
    (P.le_meet ((d.vertex_le i _ _).mp hx) ((d.vertex_le i _ _).mp hy))

noncomputable def vertex (i : I) : MeetEmbedding P d.order where
  toFun := d.point i
  le_iff := d.vertex_le i
  map_meet x y := (d.meet_eq (d.vertex_meet_spec i x y)).symm

theorem vertex_injective (i : I) : Function.Injective (d.vertex i).toFun :=
  fun _ _ h => embedding_injective (d.vertex i) h

theorem exact_overlap (i j : I) (x y : A) :
    (d.vertex i).toFun x = (d.vertex j).toFun y ↔
      P.le x (d.anchor i j) ∧ (d.change i j).toFun x = y :=
  d.mk_eq_mk i j x y

theorem cross_meet (i j : I) (x y : A) :
    d.order.meet ((d.vertex i).toFun x) ((d.vertex j).toFun y) =
      (d.vertex i).toFun (P.meet x (d.part i j y)) :=
  d.meet_eq (d.cross_meet_spec i j x y)

theorem part_respects (i : I) {x y : d.Label} (h : d.Related x y) :
    d.part i x.1 x.2 = d.part i y.1 y.2 := by
  apply P.antisymm
  · exact (d.below_iff_part i y.1 _ _).mp
      (d.le_trans (d.part_below i x.1 x.2) (d.related_le h))
  · exact (d.below_iff_part i x.1 _ _).mp
      (d.le_trans (d.part_below i y.1 y.2) (d.related_le (d.related_symm h)))

def projection (i : I) : d.Node → A :=
  Quotient.lift (fun x => d.part i x.1 x.2) (fun _ _ h => d.part_respects i h)

theorem greatest_part (i : I) (x : d.Node) (a : A) :
    d.order.le ((d.vertex i).toFun a) x ↔ P.le a (d.projection i x) := by
  induction x using Quotient.ind with
  | _ x => exact d.below_iff_part i x.1 a x.2

theorem projection_formula (i j : I) (x : A) :
    d.projection i ((d.vertex j).toFun x) = (d.change j i).toFun (P.meet x (d.anchor j i)) := rfl

theorem vertex_principal (i : I) (x : d.Node) :
    d.order.le x ((d.vertex i).toFun d.top) ↔ ∃ a, (d.vertex i).toFun a = x := by
  constructor
  · exact d.vertex_ideal i d.top x
  · rintro ⟨a, rfl⟩
    exact (d.vertex_le i _ _).mpr (d.greatest a)

theorem bottom_preserved (i : I) (zero : A) (least : ∀ x, P.le zero x) :
    ∀ x, d.order.le ((d.vertex i).toFun zero) x :=
  fun x => (d.greatest_part i x zero).mpr (least _)

theorem comparison_in_vertex (x y : d.Node) (lower : d.order.le x y) :
    ∃ i a b, (d.vertex i).toFun a = x ∧ (d.vertex i).toFun b = y ∧ P.le a b := by
  rcases d.cover y with ⟨i, b, rfl⟩
  rcases d.vertex_ideal i b x lower with ⟨a, rfl⟩
  exact ⟨i, a, b, rfl, rfl, (d.vertex_le i _ _).mp lower⟩

end PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data

end

end OAI
