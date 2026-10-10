import OAI.SetTheory.PartitionPrinciple.Transfinite.AttachmentCoinitiality

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.PrincipalAmalgamation

open Attachment

universe u v

structure Input {A : Type u} {B : Type v} (P : MeetOrder A) (Q : MeetOrder B) where
  leftAnchor : A
  rightAnchor : B
  overlap : MeetIso (idealOrder Q rightAnchor) (idealOrder P leftAnchor)

namespace Input

variable {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B} (g : Input P Q)

def Fresh := {b : B // ¬ Q.le b g.rightAnchor}

def Node := A ⊕ g.Fresh

def shadow (b : B) : A := (g.overlap.toFun (cut Q g.rightAnchor b)).val

theorem shadow_le_anchor (b : B) : P.le (g.shadow b) g.leftAnchor :=
  (g.overlap.toFun (cut Q g.rightAnchor b)).property

theorem shadow_mono {b c : B} (h : Q.le b c) : P.le (g.shadow b) (g.shadow c) :=
  (g.overlap.le_iff _ _).mpr (cut_mono Q g.rightAnchor h)

theorem shadow_meet (b c : B) : g.shadow (Q.meet b c) = P.meet (g.shadow b) (g.shadow c) := by
  unfold shadow
  rw [cut_meet, g.overlap.map_meet]
  rfl

def data : Data P g.Fresh Unit where
  component _ := ()
  base _ := g.leftAnchor
  upper _ _ := False
  upper_up := by intro _ _ _ h _; exact h
  upper_meet := by intro _ _ _ h _; exact h
  base_le_upper _ _ h := False.elim h
  base_not_upper _ h := h
  shadow x := g.shadow x.val
  shadow_le_base x := g.shadow_le_anchor x.val
  inside x y := Q.le x.val y.val
  inside_refl x := Q.refl x.val
  inside_trans := Q.trans
  inside_antisymm hxy hyx := Subtype.ext (Q.antisymm hxy hyx)
  inside_component _ := rfl
  inside_shadow := g.shadow_mono

theorem component_meets : ComponentMeets g.data := by
  classical
  intro x y _
  by_cases old : Q.le (Q.meet x.val y.val) g.rightAnchor
  · exact Or.inr (fun z hx hy => z.property (Q.trans (Q.le_meet hx hy) old))
  · exact Or.inl ⟨⟨Q.meet x.val y.val, old⟩, Q.meet_le_left _ _, Q.meet_le_right _ _,
      fun _ hx hy => Q.le_meet hx hy, g.shadow_meet x.val y.val⟩

noncomputable def order : MeetOrder g.Node := meetOrder g.data g.component_meets

noncomputable def left : MeetEmbedding P g.order := oldEmbedding g.data g.component_meets

noncomputable def represent (b : B) : g.Node := by
  classical
  exact if h : Q.le b g.rightAnchor then .inl (g.overlap.toFun ⟨b, h⟩).val
    else .inr ⟨b, h⟩

theorem represent_old (b : B) (h : Q.le b g.rightAnchor) :
    g.represent b = .inl (g.overlap.toFun ⟨b, h⟩).val := by
  unfold represent
  exact dite_eq_left h

theorem represent_new (b : B) (h : ¬ Q.le b g.rightAnchor) :
    g.represent b = .inr ⟨b, h⟩ := by
  unfold represent
  exact dite_eq_right h

theorem represent_le_iff (b c : B) : g.order.le (g.represent b) (g.represent c) ↔ Q.le b c := by
  classical
  by_cases hb : Q.le b g.rightAnchor
  · rw [g.represent_old b hb]
    by_cases hc : Q.le c g.rightAnchor
    · rw [g.represent_old c hc]
      exact g.overlap.le_iff _ _
    · rw [g.represent_new c hc]
      change P.le (g.overlap.toFun ⟨b, hb⟩).val (g.overlap.toFun (cut Q g.rightAnchor c)).val ↔ _
      change (idealOrder P g.leftAnchor).le (g.overlap.toFun ⟨b, hb⟩)
        (g.overlap.toFun (cut Q g.rightAnchor c)) ↔ _
      rw [g.overlap.le_iff]
      exact ⟨fun h => Q.trans h (Q.meet_le_left _ _), fun h => Q.le_meet h hb⟩
  · rw [g.represent_new b hb]
    by_cases hc : Q.le c g.rightAnchor
    · rw [g.represent_old c hc]
      exact ⟨False.elim, fun h => hb (Q.trans h hc)⟩
    · rw [g.represent_new c hc]
      exact ⟨fun h => h.elim id False.elim, Or.inl⟩

theorem old_below_represent (a : A) (b : B) :
    g.order.le (.inl a) (g.represent b) ↔ P.le a (g.shadow b) := by
  classical
  by_cases h : Q.le b g.rightAnchor
  · rw [g.represent_old b h]
    unfold shadow
    rw [cut_of_le Q g.rightAnchor b h]
    exact Iff.rfl
  · rw [g.represent_new b h]
    exact Iff.rfl

theorem represented_meet (b c : B) :
    IsMeet g.data (g.represent b) (g.represent c) (g.represent (Q.meet b c)) := by
  refine ⟨(g.represent_le_iff _ _).mpr (Q.meet_le_left _ _),
    (g.represent_le_iff _ _).mpr (Q.meet_le_right _ _), ?_⟩
  intro x hx hy
  cases x with
  | inl a =>
    apply (g.old_below_represent a _).mpr
    rw [g.shadow_meet]
    exact P.le_meet ((g.old_below_represent a b).mp hx) ((g.old_below_represent a c).mp hy)
  | inr x =>
    have represented : g.represent x.val = Sum.inr x := g.represent_new x.val x.property
    rw [← represented] at hx hy ⊢
    exact (g.represent_le_iff _ _).mpr
      (Q.le_meet ((g.represent_le_iff _ _).mp hx) ((g.represent_le_iff _ _).mp hy))

noncomputable def right : MeetEmbedding Q g.order where
  toFun := g.represent
  le_iff := g.represent_le_iff
  map_meet b c := (meet_eq g.data g.component_meets (g.represented_meet b c)).symm

theorem cover (x : g.Node) : (∃ a, g.left.toFun a = x) ∨ (∃ b, g.right.toFun b = x) := by
  cases x with
  | inl a => exact Or.inl ⟨a, rfl⟩
  | inr b => exact Or.inr ⟨b.val, g.represent_new b.val b.property⟩

theorem left_ideal (a : A) (x : g.Node) (h : g.order.le x (g.left.toFun a)) :
    ∃ b, g.left.toFun b = x := by
  cases x with
  | inl b => exact ⟨b, rfl⟩
  | inr x => exact False.elim h

theorem overlap_exact (a : A) (b : B) :
    g.right.toFun b = g.left.toFun a ↔
      ∃ h : Q.le b g.rightAnchor, (g.overlap.toFun ⟨b, h⟩).val = a := by
  classical
  change g.represent b = Sum.inl a ↔ _
  by_cases h : Q.le b g.rightAnchor
  · rw [g.represent_old b h]
    constructor
    · intro eq
      exact ⟨h, Sum.inl.inj eq⟩
    · rintro ⟨_, eq⟩
      exact congrArg Sum.inl eq
  · rw [g.represent_new b h]
    exact ⟨(fun eq => by cases eq), fun ⟨hb, _⟩ => False.elim (h hb)⟩

theorem old_in_right (a : A) :
    (∃ b, g.right.toFun b = g.left.toFun a) ↔ P.le a g.leftAnchor := by
  constructor
  · rintro ⟨b, eq⟩
    rcases (g.overlap_exact a b).mp eq with ⟨hb, val⟩
    exact val ▸ (g.overlap.toFun ⟨b, hb⟩).property
  · intro ha
    let b := g.overlap.inverse ⟨a, ha⟩
    refine ⟨b.val, (g.overlap_exact a b.val).mpr ⟨b.property, ?_⟩⟩
    exact congrArg Subtype.val (g.overlap.right_inverse ⟨a, ha⟩)

theorem right_ideal (b : B) (x : g.Node) (h : g.order.le x (g.right.toFun b)) :
    ∃ c, g.right.toFun c = x := by
  cases x with
  | inl a =>
    apply (g.old_in_right a).mpr
    exact P.trans ((g.old_below_represent a b).mp h) (g.shadow_le_anchor b)
  | inr x => exact ⟨x.val, g.represent_new x.val x.property⟩

theorem cross_meet (a : A) (b : B) :
    g.order.meet (g.left.toFun a) (g.right.toFun b) = .inl (P.meet a (g.shadow b)) := by
  apply meet_eq g.data g.component_meets
  refine ⟨P.meet_le_left _ _, (g.old_below_represent _ b).mpr (P.meet_le_right _ _), ?_⟩
  intro x hx hy
  rcases g.left_ideal a x hx with ⟨c, rfl⟩
  exact P.le_meet hx ((g.old_below_represent c b).mp hy)

theorem new_shadow_meet (b : g.Fresh) (a : A) :
    g.order.meet (.inr b) (.inl a) = .inl (P.meet (g.shadow b.val) a) :=
  meet_eq g.data g.component_meets (Attachment.shadow_meet g.data b a (fun h => h))

theorem principal_cross_meet (a : A) (b : B) :
    g.order.meet (g.left.toFun a) (g.right.toFun b) =
      g.left.toFun (P.meet (P.meet a g.leftAnchor) (g.shadow b)) := by
  rw [g.cross_meet]
  apply congrArg Sum.inl
  apply P.antisymm
  · exact P.le_meet
      (P.le_meet (P.meet_le_left _ _)
        (P.trans (P.meet_le_right _ _) (g.shadow_le_anchor b)))
      (P.meet_le_right _ _)
  · exact P.le_meet
      (P.trans (P.meet_le_left _ _) (P.meet_le_left _ _)) (P.meet_le_right _ _)

theorem greatest_old_part (b : B) :
    ∀ a, g.order.le (g.left.toFun a) (g.right.toFun b) ↔ P.le a (g.shadow b) :=
  fun a => g.old_below_represent a b

theorem left_principal (top : A) (greatest : ∀ a, P.le a top) (x : g.Node) :
    g.order.le x (g.left.toFun top) ↔ ∃ a, g.left.toFun a = x := by
  constructor
  · exact g.left_ideal top x
  · rintro ⟨a, rfl⟩
    exact (g.left.le_iff _ _).mpr (greatest a)

theorem right_principal (top : B) (greatest : ∀ b, Q.le b top) (x : g.Node) :
    g.order.le x (g.right.toFun top) ↔ ∃ b, g.right.toFun b = x := by
  constructor
  · exact g.right_ideal top x
  · rintro ⟨b, rfl⟩
    exact (g.right.le_iff _ _).mpr (greatest b)

theorem least_preserved (zero : A) (least : ∀ a, P.le zero a) :
    ∀ x, g.order.le (g.left.toFun zero) x := by
  intro x
  cases x with
  | inl a => exact least a
  | inr b => exact least (g.shadow b.val)

theorem bottoms_agree (zeroA : A) (zeroB : B)
    (leastA : ∀ a, P.le zeroA a) (leastB : ∀ b, Q.le zeroB b) :
    g.right.toFun zeroB = g.left.toFun zeroA := by
  have lower := g.least_preserved zeroA leastA (g.right.toFun zeroB)
  rcases g.right_ideal zeroB (g.left.toFun zeroA) lower with ⟨b, eq⟩
  apply g.order.antisymm
  · rw [← eq]
    exact (g.right.le_iff _ _).mpr (leastB b)
  · exact lower

theorem comparison_in_vertex (x y : g.Node) (lower : g.order.le x y) :
    (∃ a b, g.left.toFun a = x ∧ g.left.toFun b = y ∧ P.le a b) ∨
    (∃ a b, g.right.toFun a = x ∧ g.right.toFun b = y ∧ Q.le a b) := by
  rcases g.cover y with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · rcases g.left_ideal b x lower with ⟨a, rfl⟩
    exact Or.inl ⟨a, b, rfl, rfl, (g.left.le_iff _ _).mp lower⟩
  · rcases g.right_ideal b x lower with ⟨a, rfl⟩
    exact Or.inr ⟨a, b, rfl, rfl, (g.right.le_iff _ _).mp lower⟩

end Input

end PartitionPilot.Compression.RecursiveMaps.PrincipalAmalgamation



namespace PartitionPilot.Compression.RecursiveMaps.BinaryTiles

open Attachment PrincipalAmalgamation

universe u

variable {A : Type u} (P : MeetOrder A)

noncomputable def vertex (g : Input P P) : Bool → MeetEmbedding P g.order
  | false => g.left
  | true => g.right

theorem vertex_cover (g : Input P P) (x : g.Node) :
    ∃ i y, (vertex P g i).toFun y = x := by
  rcases g.cover x with ⟨y, eq⟩ | ⟨y, eq⟩
  · exact ⟨false, y, eq⟩
  · exact ⟨true, y, eq⟩

def separation (W : A) : Input P P where
  leftAnchor := W
  rightAnchor := W
  overlap :=
    { toFun := id
      le_iff := fun _ _ => Iff.rfl
      map_meet := fun _ _ => rfl
      inverse := id
      left_inverse := fun _ => rfl
      right_inverse := fun _ => rfl }

theorem separation_fixes (W x : A) (below : P.le x W) :
    (separation P W).right.toFun x = (separation P W).left.toFun x :=
  (separation P W).represent_old x below

theorem separation_intersection (W x : A) :
    (∃ y, (separation P W).right.toFun y = (separation P W).left.toFun x) ↔ P.le x W :=
  (separation P W).old_in_right x

theorem separation_cross_meet (W D X : A) (belowD : P.le W D) (belowX : P.le W X) :
    (separation P W).order.meet ((separation P W).right.toFun D)
      ((separation P W).left.toFun X) = (separation P W).left.toFun W := by
  rw [meet_comm, (separation P W).cross_meet]
  change Sum.inl (P.meet X (P.meet D W)) = Sum.inl W
  have dw : P.meet D W = W :=
    P.antisymm (P.meet_le_right _ _) (P.le_meet belowD (P.refl W))
  have xw : P.meet X W = W :=
    P.antisymm (P.meet_le_right _ _) (P.le_meet belowX (P.refl W))
  rw [dw, xw]

def compression (T K : A) (top : ∀ x, P.le x T) (S : MeetIso P (idealOrder P K)) :
    Input P P where
  leftAnchor := K
  rightAnchor := T
  overlap :=
    { toFun := fun x => S.toFun x.val
      le_iff := fun x y => S.le_iff x.val y.val
      map_meet := fun x y => S.map_meet x.val y.val
      inverse := fun y => ⟨S.inverse y, top _⟩
      left_inverse := fun x => Subtype.ext (S.left_inverse x.val)
      right_inverse := fun y => S.right_inverse y }

theorem compression_identification (T K : A) (top : ∀ x, P.le x T)
    (S : MeetIso P (idealOrder P K)) (x : A) :
    (compression P T K top S).right.toFun x =
      (compression P T K top S).left.toFun (S.toFun x).val :=
  (compression P T K top S).represent_old x (top x)

theorem compression_no_new_nodes (T K : A) (top : ∀ x, P.le x T)
    (S : MeetIso P (idealOrder P K)) (x : (compression P T K top S).Node) :
    ∃ a, (compression P T K top S).left.toFun a = x := by
  cases x with
  | inl a => exact ⟨a, rfl⟩
  | inr b => exact False.elim (b.property (top b.val))

theorem compression_top (T K : A) (top : ∀ x, P.le x T)
    (S : MeetIso P (idealOrder P K)) :
    (compression P T K top S).right.toFun T =
      (compression P T K top S).left.toFun K := by
  rw [compression_identification]
  apply congrArg (compression P T K top S).left.toFun
  apply P.antisymm (S.toFun T).property
  have bound := (S.le_iff (S.inverse ⟨K, P.refl K⟩) T).mpr (top _)
  rw [S.right_inverse] at bound
  exact bound

end PartitionPilot.Compression.RecursiveMaps.BinaryTiles

end

end OAI
