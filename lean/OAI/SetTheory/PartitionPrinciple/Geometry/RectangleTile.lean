import OAI.SetTheory.PartitionPrinciple.Models.CopyQuotient

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.Rectangle

universe u

inductive Vertex where
  | root | one | two
  deriving DecidableEq

instance : Countable Vertex := by
  apply Function.Injective.countable
    (f := fun v => match v with | .root => (0 : Nat) | .one => 1 | .two => 2)
  intro x y eq
  cases x <;> cases y <;> simp_all

structure Input {A : Type u} (P : MeetOrder A) where
  top : A
  greatest : ∀ x, P.le x top
  C : A
  B : A
  D : A
  C_le_D : P.le C D
  B_le_D : P.le B D
  g1 : MeetIso P P
  g2 : MeetIso P P
  agree : ∀ x, P.le x (P.meet C B) → g1.toFun x = g2.toFun x
  separated : P.meet (g1.toFun D) (g2.toFun D) = g1.toFun (P.meet C B)

namespace Input

variable {A : Type u} {P : MeetOrder A} (r : Input P)

def W : A := P.meet r.C r.B

theorem agree_W : r.g1.toFun r.W = r.g2.toFun r.W := r.agree r.W (P.refl r.W)

theorem root_intersection : P.meet (r.g1.toFun r.C) (r.g2.toFun r.C) = r.g1.toFun r.W := by
  apply P.antisymm
  · have separated : P.meet (r.g1.toFun r.D) (r.g2.toFun r.D) = r.g1.toFun r.W := r.separated
    rw [← separated]
    exact P.le_meet
      (P.trans (P.meet_le_left _ _) ((r.g1.le_iff _ _).mpr r.C_le_D))
      (P.trans (P.meet_le_right _ _) ((r.g2.le_iff _ _).mpr r.C_le_D))
  · apply P.le_meet
    · exact (r.g1.le_iff _ _).mpr (P.meet_le_left _ _)
    · rw [r.agree_W]
      exact (r.g2.le_iff _ _).mpr (P.meet_le_left _ _)

private theorem image_bound (f g : MeetIso P P)
    (intersection : P.meet (f.toFun r.C) (g.toFun r.C) = f.toFun r.W)
    (x : A) (hx : P.le x r.C) : P.le (f.toFun x) (g.toFun r.C) ↔ P.le x r.B := by
  constructor
  · intro h
    have lower := P.le_meet ((f.le_iff _ _).mpr hx) h
    rw [intersection] at lower
    exact P.trans ((f.le_iff _ _).mp lower) (P.meet_le_right _ _)
  · intro h
    have lower : P.le (f.toFun x) (f.toFun r.W) := (f.le_iff _ _).mpr (P.le_meet hx h)
    rw [← intersection] at lower
    exact P.trans lower (P.meet_le_right _ _)

theorem g1_bound (x : A) (hx : P.le x r.C) :
    P.le (r.g1.toFun x) (r.g2.toFun r.C) ↔ P.le x r.B :=
  r.image_bound r.g1 r.g2 r.root_intersection x hx

theorem g2_bound (x : A) (hx : P.le x r.C) :
    P.le (r.g2.toFun x) (r.g1.toFun r.C) ↔ P.le x r.B := by
  apply r.image_bound r.g2 r.g1
  rw [meet_comm, r.root_intersection, r.agree_W]
  exact hx

theorem inverse1_C (x : A) (hx : P.le x (r.g1.toFun r.C)) : P.le (r.g1.inverse x) r.C := by
  apply (r.g1.le_iff _ _).mp
  rw [r.g1.right_inverse]
  exact hx

theorem inverse2_C (x : A) (hx : P.le x (r.g2.toFun r.C)) : P.le (r.g2.inverse x) r.C := by
  apply (r.g2.le_iff _ _).mp
  rw [r.g2.right_inverse]
  exact hx

theorem root_domain1 (x : A) (hx : P.le x (r.g1.toFun r.C)) :
    P.le (r.g1.inverse x) r.B ↔ P.le x (r.g2.toFun r.C) := by
  have h := (r.g1_bound (r.g1.inverse x) (r.inverse1_C x hx)).symm
  rw [r.g1.right_inverse] at h
  exact h

theorem root_domain2 (x : A) (hx : P.le x (r.g2.toFun r.C)) :
    P.le (r.g2.inverse x) r.B ↔ P.le x (r.g1.toFun r.C) := by
  have h := (r.g2_bound (r.g2.inverse x) (r.inverse2_C x hx)).symm
  rw [r.g2.right_inverse] at h
  exact h

theorem inverses_agree (x : A) (h1 : P.le x (r.g1.toFun r.C))
    (h2 : P.le x (r.g2.toFun r.C)) : r.g1.inverse x = r.g2.inverse x := by
  have hx : P.le (r.g1.inverse x) r.W :=
    P.le_meet (r.inverse1_C x h1) ((r.root_domain1 x h1).mpr h2)
  have eq : r.g2.toFun (r.g1.inverse x) = x :=
    (r.agree _ hx).symm.trans (r.g1.right_inverse x)
  have inv := congrArg r.g2.inverse eq
  rw [r.g2.left_inverse] at inv
  exact inv

def anchor : Vertex → Vertex → A
  | .root, .root => r.top
  | .one, .one => r.top
  | .two, .two => r.top
  | .root, .one => r.g1.toFun r.C
  | .one, .root => r.C
  | .root, .two => r.g2.toFun r.C
  | .two, .root => r.C
  | .one, .two => r.B
  | .two, .one => r.B

def transition : Vertex → Vertex → MeetIso P P
  | .root, .one => inverseIso r.g1
  | .one, .root => r.g1
  | .root, .two => inverseIso r.g2
  | .two, .root => r.g2
  | _, _ => identityIso P

theorem triangle_domain (i j k : Vertex) (ij : i ≠ j) (jk : j ≠ k) (ik : i ≠ k)
    (x : A) (hx : P.le x (r.anchor i j)) :
    P.le ((r.transition i j).toFun x) (r.anchor j k) ↔ P.le x (r.anchor i k) := by
  cases i <;> cases j <;> cases k <;> try contradiction
  · exact r.root_domain1 x hx
  · exact r.root_domain2 x hx
  · exact r.g1_bound x hx
  · exact Iff.rfl
  · exact r.g2_bound x hx
  · exact Iff.rfl

theorem triangle_change (i j k : Vertex) (ij : i ≠ j) (jk : j ≠ k) (ik : i ≠ k)
    (x : A) (hx : P.le x (r.anchor i j)) (hy : P.le x (r.anchor i k)) :
    (r.transition j k).toFun ((r.transition i j).toFun x) = (r.transition i k).toFun x := by
  cases i <;> cases j <;> cases k <;> try contradiction
  · exact r.inverses_agree x hx hy
  · exact (r.inverses_agree x hy hx).symm
  · change r.g2.inverse (r.g1.toFun x) = x
    rw [r.agree x (P.le_meet hx hy), r.g2.left_inverse]
  · exact (r.agree x (P.le_meet hy hx)).symm
  · change r.g1.inverse (r.g2.toFun x) = x
    rw [← r.agree x (P.le_meet hx hy), r.g1.left_inverse]
  · exact r.agree x (P.le_meet hy hx)

def copies : CompatibleCopies.Data P Vertex where
  top := r.top
  greatest := r.greatest
  anchor := r.anchor
  change := r.transition
  self_anchor := by intro i; cases i <;> rfl
  self_change := by intro i x; cases i <;> rfl
  reverse := by
    intro i j x
    cases i <;> cases j
    · rfl
    · exact r.g1.right_inverse x
    · exact r.g2.right_inverse x
    · exact r.g1.left_inverse x
    · rfl
    · rfl
    · exact r.g2.left_inverse x
    · rfl
    · rfl
  anchor_change := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact r.g1.left_inverse r.C
    · exact r.g2.left_inverse r.C
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  triangle_domain := r.triangle_domain
  triangle_change := r.triangle_change

end Input
end PartitionPilot.Compression.RecursiveMaps.Rectangle

end

section

namespace PartitionPilot.Compression.RecursiveMaps.Rectangle.Input

universe u

variable {A : Type u} {P : MeetOrder A} (r : Input P)

noncomputable def root : MeetEmbedding P r.copies.order := r.copies.vertex .root
noncomputable def first : MeetEmbedding P r.copies.order := r.copies.vertex .one
noncomputable def second : MeetEmbedding P r.copies.order := r.copies.vertex .two

theorem first_agrees (x : A) (below : P.le x r.C) :
    r.first.toFun x = r.root.toFun (r.g1.toFun x) :=
  (r.copies.exact_overlap .one .root x (r.g1.toFun x)).mpr ⟨below, rfl⟩

theorem second_agrees (x : A) (below : P.le x r.C) :
    r.second.toFun x = r.root.toFun (r.g2.toFun x) :=
  (r.copies.exact_overlap .two .root x (r.g2.toFun x)).mpr ⟨below, rfl⟩

theorem children_agree (x : A) (below : P.le x r.B) :
    r.first.toFun x = r.second.toFun x :=
  (r.copies.exact_overlap .one .two x x).mpr ⟨below, rfl⟩

theorem first_root_intersection (x y : A) :
    r.first.toFun x = r.root.toFun y ↔ P.le x r.C ∧ r.g1.toFun x = y :=
  r.copies.exact_overlap .one .root x y

theorem second_root_intersection (x y : A) :
    r.second.toFun x = r.root.toFun y ↔ P.le x r.C ∧ r.g2.toFun x = y :=
  r.copies.exact_overlap .two .root x y

theorem children_intersection (x y : A) :
    r.first.toFun x = r.second.toFun y ↔ P.le x r.B ∧ x = y :=
  r.copies.exact_overlap .one .two x y

theorem meet_D_C : P.meet r.D r.C = r.C :=
  P.antisymm (P.meet_le_right _ _) (P.le_meet r.C_le_D (P.refl _))

theorem meet_D_B : P.meet r.D r.B = r.B :=
  P.antisymm (P.meet_le_right _ _) (P.le_meet r.B_le_D (P.refl _))

theorem first_root_part : r.copies.projection .root (r.first.toFun r.D) = r.g1.toFun r.C := by
  change r.g1.toFun (P.meet r.D r.C) = r.g1.toFun r.C
  rw [r.meet_D_C]

theorem second_root_part : r.copies.projection .root (r.second.toFun r.D) = r.g2.toFun r.C := by
  change r.g2.toFun (P.meet r.D r.C) = r.g2.toFun r.C
  rw [r.meet_D_C]

theorem first_meet_root (x : A) :
    r.copies.order.meet (r.first.toFun r.D) (r.root.toFun x) =
      r.root.toFun (P.meet (r.g1.toFun r.C) x) := by
  rw [meet_comm r.copies.order]
  have eq := r.copies.cross_meet .root .one x r.D
  change r.copies.order.meet (r.root.toFun x) (r.first.toFun r.D) =
    r.root.toFun (P.meet x (r.g1.toFun (P.meet r.D r.C))) at eq
  rw [r.meet_D_C, meet_comm P x] at eq
  exact eq

theorem second_meet_root (x : A) :
    r.copies.order.meet (r.second.toFun r.D) (r.root.toFun x) =
      r.root.toFun (P.meet (r.g2.toFun r.C) x) := by
  rw [meet_comm r.copies.order]
  have eq := r.copies.cross_meet .root .two x r.D
  change r.copies.order.meet (r.root.toFun x) (r.second.toFun r.D) =
    r.root.toFun (P.meet x (r.g2.toFun (P.meet r.D r.C))) at eq
  rw [r.meet_D_C, meet_comm P x] at eq
  exact eq

theorem children_meet :
    r.copies.order.meet (r.first.toFun r.D) (r.second.toFun r.D) = r.first.toFun r.B := by
  have eq := r.copies.cross_meet .one .two r.D r.D
  change r.copies.order.meet (r.first.toFun r.D) (r.second.toFun r.D) =
    r.first.toFun (P.meet r.D (P.meet r.D r.B)) at eq
  rw [r.meet_D_B, r.meet_D_B] at eq
  exact eq

theorem children_meet_both :
    r.copies.order.meet (r.first.toFun r.D) (r.second.toFun r.D) = r.first.toFun r.B ∧
      r.first.toFun r.B = r.second.toFun r.B :=
  ⟨r.children_meet, r.children_agree r.B (P.refl _)⟩

theorem three_vertex_cover (x : r.copies.Node) :
    ∃ i y, (r.copies.vertex i).toFun y = x := r.copies.cover x

open Chronological in

noncomputable def incoming_layer {O Stage : Type u} [LinearOrder Stage] {Q : MeetOrder O}
    (g : PrincipalAmalgamation.Input Q r.copies.order)
    (Space : Stage → Type u) (order : ∀ t, MeetOrder (Space t))
    (oldBirth : O → Stage) (s t : Stage) (old : ∀ a, oldBirth a < s) (earlier : t < s)
    (template : MeetIso (order t) P) :
    GrowthLayer Space order g.order (g.birth oldBirth s) s := by
  apply g.incoming_layer Space order oldBirth s old (ULift.{u} Vertex)
    (fun _ => t) (fun _ => earlier)
    (fun i => compose template.toMeetEmbedding (r.copies.vertex i.down))
  intro x
  rcases r.three_vertex_cover x with ⟨i, y, eq⟩
  refine ⟨⟨i⟩, template.inverse y, ?_⟩
  change (r.copies.vertex i).toFun (template.toFun (template.inverse y)) = x
  rw [template.right_inverse]
  exact eq

end PartitionPilot.Compression.RecursiveMaps.Rectangle.Input

end

end OAI
