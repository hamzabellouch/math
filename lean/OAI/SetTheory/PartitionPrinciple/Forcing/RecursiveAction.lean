import OAI.SetTheory.PartitionPrinciple.Transfinite.RecursiveMaps

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Attachment

universe u v w z

def isoOfOrder {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B}
    (f : A → B) (g : B → A) (left : ∀ x, g (f x) = x)
    (right : ∀ y, f (g y) = y)
    (order : ∀ x y, Q.le (f x) (f y) ↔ P.le x y) : MeetIso P Q where
  toFun := f
  le_iff := order
  map_meet x y := by
    apply Q.antisymm
    · exact Q.le_meet ((order _ _).mpr (P.meet_le_left x y))
        ((order _ _).mpr (P.meet_le_right x y))
    · have hx : P.le (g (Q.meet (f x) (f y))) x := by
        apply (order _ _).mp
        rw [right]
        exact Q.meet_le_left _ _
      have hy : P.le (g (Q.meet (f x) (f y))) y := by
        apply (order _ _).mp
        rw [right]
        exact Q.meet_le_right _ _
      have h := (order _ _).mpr (P.le_meet hx hy)
      rw [right] at h
      exact h
  inverse := g
  left_inverse := left
  right_inverse := right

def inverseIso {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B}
    (f : MeetIso P Q) : MeetIso Q P :=
  isoOfOrder f.inverse f.toFun f.right_inverse f.left_inverse (by
    intro x y
    have h := f.le_iff (f.inverse x) (f.inverse y)
    rw [f.right_inverse, f.right_inverse] at h
    exact h.symm)

structure TaskSymmetry {O : Type u} {I : Type w} {P : MeetOrder O}
    {b : Templates.{u,v,w} P I} {Task : Type z} (d : Inputs b Task) where
  perm : Task → Task
  inverse : Task → Task
  left_inverse : ∀ i, inverse (perm i) = i
  right_inverse : ∀ i, perm (inverse i) = i
  current : MeetIso b.extension b.extension
  source : ∀ i, d.source (perm i) = d.source i
  intertwine : ∀ i p, current.toFun ((d.previous i).toFun p) =
    (d.previous (perm i)).toFun p

namespace TaskSymmetry

variable {O : Type u} {I : Type w} {P : MeetOrder O}
    {b : Templates.{u,v,w} P I} {Task : Type z} {d : Inputs b Task}
    (s : TaskSymmetry d)

noncomputable def symm : TaskSymmetry d where
  perm := s.inverse
  inverse := s.perm
  left_inverse := s.right_inverse
  right_inverse := s.left_inverse
  current := inverseIso s.current
  source i := by
    have h := s.source (s.inverse i)
    rw [s.right_inverse] at h
    exact h.symm
  intertwine i p := by
    have h := congrArg s.current.inverse (s.intertwine (s.inverse i) p)
    rw [s.current.left_inverse, s.right_inverse] at h
    exact h.symm

def renameLabel (label : d.Labels) : d.Labels :=
  ⟨s.perm label.1, ⟨label.2.val, by
    rw [s.source]
    exact label.2.property⟩⟩

def renameFresh (x : d.nextBatch.Fresh) : d.nextBatch.Fresh :=
  ⟨s.renameLabel x.1, x.2⟩

def act : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh →
    (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh
  | .inl x => .inl (s.current.toFun x)
  | .inr x => .inr (s.renameFresh x)

theorem fresh_task_eq {i j : Task} {h : I}
    {hi : ¬ b.upper h (d.source i)} {hj : ¬ b.upper h (d.source j)}
    {y : b.Space h} {outside : ¬ (b.order h).le y (b.anchor h)} (eq : i = j) :
    (⟨⟨i, ⟨h, hi⟩⟩, ⟨y, outside⟩⟩ : d.nextBatch.Fresh) =
      ⟨⟨j, ⟨h, hj⟩⟩, ⟨y, outside⟩⟩ := by
  cases eq
  rfl

theorem rename_left (x : d.nextBatch.Fresh) :
    s.symm.renameFresh (s.renameFresh x) = x := by
  rcases x with ⟨⟨i, ⟨h, eligible⟩⟩, ⟨y, outside⟩⟩
  change (⟨⟨s.inverse (s.perm i), ⟨h, _⟩⟩, ⟨y, outside⟩⟩ : d.nextBatch.Fresh) = _
  exact fresh_task_eq (s.left_inverse i)

theorem rename_right (x : d.nextBatch.Fresh) :
    s.renameFresh (s.symm.renameFresh x) = x := by
  rcases x with ⟨⟨i, ⟨h, eligible⟩⟩, ⟨y, outside⟩⟩
  change (⟨⟨s.perm (s.inverse i), ⟨h, _⟩⟩, ⟨y, outside⟩⟩ : d.nextBatch.Fresh) = _
  exact fresh_task_eq (s.right_inverse i)

theorem act_left (x : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh) :
    s.symm.act (s.act x) = x := by
  cases x with
  | inl x => exact congrArg Sum.inl (s.current.left_inverse x)
  | inr x => exact congrArg Sum.inr (s.rename_left x)

theorem act_right (x : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh) :
    s.act (s.symm.act x) = x := by
  cases x with
  | inl x => exact congrArg Sum.inl (s.current.right_inverse x)
  | inr x => exact congrArg Sum.inr (s.rename_right x)

theorem shadow_covariant (x : d.nextBatch.Fresh) :
    d.nextBatch.shadow (s.renameFresh x) =
      s.current.toFun (d.nextBatch.shadow x) :=
  (s.intertwine x.1.1
    ((b.embed x.1.2.val).toFun (cut (b.order x.1.2.val)
      (b.anchor x.1.2.val) x.2.val))).symm

theorem upper_covariant (label : d.Labels) (x : O ⊕ b.Fresh) :
    d.nextBatch.upper (s.renameLabel label) (s.current.toFun x) ↔
      d.nextBatch.upper label x := by
  change (∃ p, b.upper label.2.val p ∧
    b.extension.le ((d.previous (s.perm label.1)).toFun p) (s.current.toFun x)) ↔
    (∃ p, b.upper label.2.val p ∧ b.extension.le ((d.previous label.1).toFun p) x)
  constructor
  · rintro ⟨p, hp, hpx⟩
    rw [← s.intertwine] at hpx
    exact ⟨p, hp, (s.current.le_iff _ _).mp hpx⟩
  · rintro ⟨p, hp, hpx⟩
    refine ⟨p, hp, ?_⟩
    rw [← s.intertwine]
    exact (s.current.le_iff _ _).mpr hpx

theorem inside_forward {x y : d.nextBatch.Fresh} (h : d.nextBatch.Inside x y) :
    d.nextBatch.Inside (s.renameFresh x) (s.renameFresh y) := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases h with ⟨eq, h⟩
  cases eq
  exact ⟨rfl, h⟩

theorem inside_iff (x y : d.nextBatch.Fresh) :
    d.nextBatch.Inside (s.renameFresh x) (s.renameFresh y) ↔
      d.nextBatch.Inside x y := by
  constructor
  · intro h
    have h' := s.symm.inside_forward h
    rw [s.rename_left, s.rename_left] at h'
    exact h'
  · exact s.inside_forward

theorem act_order (x y : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh) :
    d.nextBatch.extension.le (s.act x) (s.act y) ↔ d.nextBatch.extension.le x y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact s.current.le_iff x y
    | inr y =>
      change b.extension.le (s.current.toFun x) (d.nextBatch.shadow (s.renameFresh y)) ↔ _
      rw [s.shadow_covariant]
      exact s.current.le_iff _ _
  | inr x =>
    cases y with
    | inl y => exact s.upper_covariant x.1 y
    | inr y =>
      change (d.nextBatch.Inside (s.renameFresh x) (s.renameFresh y) ∨
        d.nextBatch.upper (s.renameLabel x.1) (d.nextBatch.shadow (s.renameFresh y))) ↔
        (d.nextBatch.Inside x y ∨ d.nextBatch.upper x.1 (d.nextBatch.shadow y))
      rw [s.inside_iff, s.shadow_covariant, s.upper_covariant]

noncomputable def nextIso : MeetIso d.nextBatch.extension d.nextBatch.extension :=
  isoOfOrder s.act s.symm.act s.act_left s.act_right s.act_order

theorem nextIso_old (x : O ⊕ b.Fresh) :
    s.nextIso.toFun (.inl x) = .inl (s.current.toFun x) := rfl

theorem nextIso_fresh (x : d.nextBatch.Fresh) :
    s.nextIso.toFun (.inr x) = .inr (s.renameFresh x) := rfl

theorem nextIso_meet (x y : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh) :
    s.nextIso.toFun (d.nextBatch.extension.meet x y) =
      d.nextBatch.extension.meet (s.nextIso.toFun x) (s.nextIso.toFun y) :=
  s.nextIso.map_meet x y

noncomputable def identity : TaskSymmetry d where
  perm i := i
  inverse i := i
  left_inverse _ := rfl
  right_inverse _ := rfl
  current := isoOfOrder (fun x => x) (fun x => x) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ => Iff.rfl)
  source _ := rfl
  intertwine _ _ := rfl

noncomputable def comp (t : TaskSymmetry d) : TaskSymmetry d where
  perm i := s.perm (t.perm i)
  inverse i := t.inverse (s.inverse i)
  left_inverse i := by rw [s.left_inverse, t.left_inverse]
  right_inverse i := by rw [t.right_inverse, s.right_inverse]
  current := {
    toMeetEmbedding := compose t.current.toMeetEmbedding s.current.toMeetEmbedding
    inverse x := t.current.inverse (s.current.inverse x)
    left_inverse x := by
      change t.current.inverse (s.current.inverse (s.current.toFun (t.current.toFun x))) = x
      rw [s.current.left_inverse, t.current.left_inverse]
    right_inverse x := by
      change s.current.toFun (t.current.toFun (t.current.inverse (s.current.inverse x))) = x
      rw [t.current.right_inverse, s.current.right_inverse] }
  source i := by rw [s.source, t.source]
  intertwine i p := by
    change s.current.toFun (t.current.toFun ((d.previous i).toFun p)) = _
    rw [t.intertwine, s.intertwine]

theorem next_identity (x : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh) :
    (identity (d := d)).nextIso.toFun x = x := by
  cases x <;> rfl

theorem next_composition (t : TaskSymmetry d)
    (x : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh) :
    (s.comp t).nextIso.toFun x = s.nextIso.toFun (t.nextIso.toFun x) := by
  cases x <;> rfl

theorem next_inverse (x : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh) :
    s.symm.nextIso.toFun (s.nextIso.toFun x) = x :=
  s.act_left x

theorem lift_equivariant
    (compatible : ∀ i x, b.extension.le x (.inl (d.source i)) →
      s.current.toFun ((d.representative i).toFun x) =
        (d.representative (s.perm i)).toFun x)
    (i : Task) (x : O ⊕ b.Fresh) :
    s.nextIso.toFun (d.lift i x) = d.lift (s.perm i) x := by
  cases x with
  | inl p => exact congrArg Sum.inl (s.intertwine i p)
  | inr x =>
    classical
    by_cases h : b.upper x.1 (d.source i)
    · have h' : b.upper x.1 (d.source (s.perm i)) := by rw [s.source]; exact h
      rw [d.lift_new_inside i x h, d.lift_new_inside (s.perm i) x h', s.nextIso_old]
      exact congrArg Sum.inl (compatible i (.inr x) h)
    · have h' : ¬ b.upper x.1 (d.source (s.perm i)) := by rw [s.source]; exact h
      rw [d.lift_new_outside i x h, d.lift_new_outside (s.perm i) x h', s.nextIso_fresh]
      rfl

theorem fresh_positive (T : O) (top : ∀ p, P.le p T) (v : O)
    (positive : Task → Prop)
    (negative : ∀ i, ¬ positive i →
      b.extension.le (b.extension.meet ((d.previous i).toFun T) (.inl v))
        ((d.previous i).toFun (d.source i)))
    (x : d.nextBatch.Fresh)
    (below : d.nextBatch.extension.le (.inr x) (.inl (.inl v))) :
    positive x.1.1 := by
  classical
  apply Classical.byContradiction
  intro hn
  rcases x with ⟨⟨i, ⟨h, eligible⟩⟩, y⟩
  have cap := d.fresh_below_cap i ⟨h, y⟩ eligible T top
  have lower := d.nextBatch.extension.le_meet cap below
  have hm : d.nextBatch.extension.meet (.inl ((d.previous i).toFun T)) (.inl (.inl v)) =
      .inl (b.extension.meet ((d.previous i).toFun T) (.inl v)) :=
    (d.nextBatch.oldEmbedding.map_meet _ _).symm
  rw [hm] at lower
  have neg := (d.nextBatch.oldEmbedding.le_iff _ _).mpr (negative i hn)
  exact d.fresh_outside_base i ⟨h, y⟩ eligible (d.nextBatch.extension.trans lower neg)

theorem agreement_persists (t : TaskSymmetry d)
    (T : O) (top : ∀ p, P.le p T) (v : O) (positive : Task → Prop)
    (negative : ∀ i, ¬ positive i →
      b.extension.le (b.extension.meet ((d.previous i).toFun T) (.inl v))
        ((d.previous i).toFun (d.source i)))
    (current_agree : ∀ x, b.extension.le x (.inl v) →
      s.current.toFun x = t.current.toFun x)
    (task_agree : ∀ i, positive i → s.perm i = t.perm i)
    (x : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh)
    (below : d.nextBatch.extension.le x (.inl (.inl v))) :
    s.nextIso.toFun x = t.nextIso.toFun x := by
  cases x with
  | inl x => exact congrArg Sum.inl (current_agree x below)
  | inr x =>
    have pos := fresh_positive T top v positive negative x below
    have eq := task_agree x.1.1 pos
    rcases x with ⟨⟨i, ⟨h, eligible⟩⟩, ⟨y, outside⟩⟩
    apply congrArg Sum.inr
    exact fresh_task_eq eq

end TaskSymmetry

namespace Inputs

variable {O : Type u} {I : Type w} {P : MeetOrder O}
    {b : Templates.{u,v,w} P I} {Task : Type z} (d : Inputs b Task)

noncomputable def nextInputs (reps : Task → TaskSymmetry d)
    (current_reps : ∀ i x, (reps i).current.toFun x = (d.representative i).toFun x) :
    Inputs d.nextBatch Task where
  source i := .inl (d.source i)
  previous := d.liftedEmbedding
  representative i := (reps i).nextIso
  agree i x hx := by
    change d.lift i x = .inl ((reps i).current.toFun x)
    rw [current_reps]
    exact d.lift_agrees_on_base i x hx

noncomputable def nextSymmetry (reps : Task → TaskSymmetry d)
    (current_reps : ∀ i x, (reps i).current.toFun x = (d.representative i).toFun x)
    (s : TaskSymmetry d)
    (compatible : ∀ i x, b.extension.le x (.inl (d.source i)) →
      s.current.toFun ((d.representative i).toFun x) =
        (d.representative (s.perm i)).toFun x) :
    TaskSymmetry (d.nextInputs reps current_reps) where
  perm := s.perm
  inverse := s.inverse
  left_inverse := s.left_inverse
  right_inverse := s.right_inverse
  current := s.nextIso
  source i := congrArg Sum.inl (s.source i)
  intertwine := s.lift_equivariant compatible

end Inputs
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
