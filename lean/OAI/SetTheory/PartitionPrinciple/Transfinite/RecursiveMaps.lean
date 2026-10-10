import OAI.SetTheory.PartitionPrinciple.Geometry.Compression

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Attachment

universe u v w z

def compose {A : Type u} {B : Type v} {C : Type w}
    {P : MeetOrder A} {Q : MeetOrder B} {R : MeetOrder C}
    (f : MeetEmbedding P Q) (g : MeetEmbedding Q R) : MeetEmbedding P R where
  toFun x := g.toFun (f.toFun x)
  le_iff x y := (g.le_iff _ _).trans (f.le_iff x y)
  map_meet x y := by rw [f.map_meet, g.map_meet]

def componentFilter {O : Type u} {I : Type w} {P : MeetOrder O}
    (b : Templates.{u,v,w} P I) (h : I) : MeetFilter P where
  mem := b.upper h
  nonempty := b.upper_nonempty h
  upward := b.upper_up h
  closed_meet := b.upper_meet h

structure Inputs {O : Type u} {I : Type w} {P : MeetOrder O}
    (b : Templates.{u,v,w} P I) (Task : Type z) where
  source : Task → O
  previous : Task → MeetEmbedding P b.extension
  representative : Task → MeetIso b.extension b.extension
  agree : ∀ i p, P.le p (source i) →
    (previous i).toFun p = (representative i).toFun (.inl p)

namespace Inputs

variable {O : Type u} {I : Type w} {P : MeetOrder O}
    {b : Templates.{u,v,w} P I} {Task : Type z} (d : Inputs b Task)

def Eligible (i : Task) := {h : I // ¬ b.upper h (d.source i)}
def Labels := (i : Task) × d.Eligible i

noncomputable def nextBatch : Templates b.extension d.Labels where
  Space label := b.Space label.2.val
  order label := b.order label.2.val
  anchor label := b.anchor label.2.val
  embed label := compose (b.embed label.2.val) (d.previous label.1)
  upper label := (pushFilter (d.previous label.1) (componentFilter b label.2.val)).mem
  upper_nonempty label := (pushFilter (d.previous label.1) (componentFilter b label.2.val)).nonempty
  upper_up label := (pushFilter (d.previous label.1) (componentFilter b label.2.val)).upward
  upper_meet label := (pushFilter (d.previous label.1) (componentFilter b label.2.val)).closed_meet
  separator label := (d.previous label.1).toFun (b.separator label.2.val)
  base_le_separator label := ((d.previous label.1).le_iff _ _).mpr (b.base_le_separator label.2.val)
  separator_not_le_base label h :=
    b.separator_not_le_base label.2.val (((d.previous label.1).le_iff _ _).mp h)
  separator_le_upper label y h :=
    pushFilter_lower_bound (d.previous label.1) (componentFilter b label.2.val)
      (b.separator label.2.val) (b.separator_le_upper label.2.val) y h

def freshImage (i : Task) (x : b.Fresh) (eligible : ¬ b.upper x.1 (d.source i)) :
    d.nextBatch.Fresh := ⟨⟨i, ⟨x.1, eligible⟩⟩, x.2⟩

noncomputable def lift (i : Task) : O ⊕ b.Fresh → (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh := by
  classical
  exact fun x => match x with
    | .inl p => .inl ((d.previous i).toFun p)
    | .inr y => if h : b.upper y.1 (d.source i) then
        .inl ((d.representative i).toFun (.inr y))
      else .inr (d.freshImage i y h)

theorem lift_old (i : Task) (p : O) :
    d.lift i (.inl p) = .inl ((d.previous i).toFun p) := rfl

theorem lift_new_inside (i : Task) (x : b.Fresh) (h : b.upper x.1 (d.source i)) :
    d.lift i (.inr x) = .inl ((d.representative i).toFun (.inr x)) := by
  simp only [lift, dite_eq_left h]

theorem lift_new_outside (i : Task) (x : b.Fresh) (h : ¬ b.upper x.1 (d.source i)) :
    d.lift i (.inr x) = .inr (d.freshImage i x h) := by
  simp only [lift, dite_eq_right h]

theorem fresh_shadow (i : Task) (x : b.Fresh) (h : ¬ b.upper x.1 (d.source i)) :
    d.nextBatch.shadow (d.freshImage i x h) = (d.previous i).toFun (b.shadow x) := rfl

theorem fresh_old_iff (i : Task) (x : b.Fresh) (h : ¬ b.upper x.1 (d.source i)) (p : O) :
    d.nextBatch.extension.le (.inr (d.freshImage i x h)) (.inl ((d.previous i).toFun p)) ↔
    b.extension.le (.inr x) (.inl p) :=
  pushFilter_trace (d.previous i) (componentFilter b x.1) p

theorem old_fresh_iff (i : Task) (x : b.Fresh) (h : ¬ b.upper x.1 (d.source i)) (p : O) :
    d.nextBatch.extension.le (.inl ((d.previous i).toFun p)) (.inr (d.freshImage i x h)) ↔
    b.extension.le (.inl p) (.inr x) :=
  (d.previous i).le_iff p (b.shadow x)

theorem lift_agrees_on_base (i : Task) (x : O ⊕ b.Fresh)
    (h : b.extension.le x (.inl (d.source i))) :
    d.lift i x = .inl ((d.representative i).toFun x) := by
  cases x with
  | inl p => exact congrArg Sum.inl (d.agree i p h)
  | inr x => exact d.lift_new_inside i x h

theorem lift_template (i : Task) (h : I) (eligible : ¬ b.upper h (d.source i))
    (y : b.Space h) :
    d.lift i (b.represent h y) = d.nextBatch.represent ⟨i, ⟨h, eligible⟩⟩ y := by
  classical
  by_cases old : (b.order h).le y (b.anchor h)
  · rw [b.represent_old h y old, d.lift_old,
      d.nextBatch.represent_old ⟨i, ⟨h, eligible⟩⟩ y old]
    rfl
  · rw [b.represent_new h y old, d.lift_new_outside i ⟨h, ⟨y, old⟩⟩ eligible,
      d.nextBatch.represent_new ⟨i, ⟨h, eligible⟩⟩ y old]
    rfl

theorem fresh_pair_iff (i : Task) (x y : b.Fresh)
    (hx : ¬ b.upper x.1 (d.source i)) (hy : ¬ b.upper y.1 (d.source i)) :
    d.nextBatch.extension.le (.inr (d.freshImage i x hx)) (.inr (d.freshImage i y hy)) ↔
    b.extension.le (.inr x) (.inr y) := by
  classical
  by_cases same : x.1 = y.1
  · rcases x with ⟨h, x, xout⟩
    rcases y with ⟨k, y, yout⟩
    change h = k at same
    cases same
    have tx := d.nextBatch.represent_new ⟨i, ⟨h, hx⟩⟩ x xout
    have ty := d.nextBatch.represent_new ⟨i, ⟨h, hy⟩⟩ y yout
    have sx := b.represent_new h x xout
    have sy := b.represent_new h y yout
    change d.nextBatch.extension.le (Sum.inr ⟨⟨i, ⟨h, hx⟩⟩, ⟨x, xout⟩⟩)
      (Sum.inr ⟨⟨i, ⟨h, hy⟩⟩, ⟨y, yout⟩⟩) ↔ _
    rw [← tx, ← ty, ← sx, ← sy]
    exact (d.nextBatch.represent_le_iff ⟨i, ⟨h, hx⟩⟩ x y).trans
      (b.represent_le_iff h x y).symm
  · have different : (d.freshImage i x hx).1 ≠ (d.freshImage i y hy).1 := by
      intro h
      exact same (congrArg (fun label : d.Labels => label.2.val) h)
    rw [d.nextBatch.cross_le_iff _ _ different, b.cross_le_iff x y same]
    exact pushFilter_trace (d.previous i) (componentFilter b x.1) (b.shadow y)

theorem meet_lift_old_old (i : Task) (p q : O) :
    d.nextBatch.extension.meet (d.lift i (.inl p)) (d.lift i (.inl q)) =
    d.lift i (b.extension.meet (.inl p) (.inl q)) := by
  calc
    d.nextBatch.extension.meet (d.lift i (.inl p)) (d.lift i (.inl q)) =
        .inl (b.extension.meet ((d.previous i).toFun p) ((d.previous i).toFun q)) :=
      (d.nextBatch.oldEmbedding.map_meet _ _).symm
    _ = .inl ((d.previous i).toFun (P.meet p q)) :=
      congrArg Sum.inl ((d.previous i).map_meet p q).symm
    _ = d.lift i (.inl (P.meet p q)) := rfl
    _ = d.lift i (b.extension.meet (.inl p) (.inl q)) :=
      congrArg (d.lift i) (b.oldEmbedding.map_meet p q)

theorem meet_lift_fresh_old (i : Task) (x : b.Fresh)
    (eligible : ¬ b.upper x.1 (d.source i)) (p : O) :
    d.nextBatch.extension.meet (d.lift i (.inr x)) (d.lift i (.inl p)) =
    d.lift i (b.extension.meet (.inr x) (.inl p)) := by
  classical
  by_cases hp : b.upper x.1 p
  · rw [meet_eq_left_of_le b.extension (x := .inr x) (y := .inl p) hp,
      d.lift_new_outside i x eligible, d.lift_old]
    exact meet_eq_left_of_le d.nextBatch.extension ((d.fresh_old_iff i x eligible p).mpr hp)
  · have target_not : ¬ d.nextBatch.extension.le (.inr (d.freshImage i x eligible))
        (.inl ((d.previous i).toFun p)) :=
      fun h => hp ((d.fresh_old_iff i x eligible p).mp h)
    rw [d.lift_new_outside i x eligible, d.lift_old]
    calc
      d.nextBatch.extension.meet (.inr (d.freshImage i x eligible))
          (.inl ((d.previous i).toFun p)) =
          .inl (b.extension.meet ((d.previous i).toFun (b.shadow x)) ((d.previous i).toFun p)) :=
        d.nextBatch.shadow_meet_eq _ _ target_not
      _ = .inl ((d.previous i).toFun (P.meet (b.shadow x) p)) :=
        congrArg Sum.inl ((d.previous i).map_meet _ _).symm
      _ = d.lift i (.inl (P.meet (b.shadow x) p)) := rfl
      _ = d.lift i (b.extension.meet (.inr x) (.inl p)) :=
        congrArg (d.lift i) (b.shadow_meet_eq x p hp).symm

theorem meet_lift_template (i : Task) (h : I) (eligible : ¬ b.upper h (d.source i))
    (x y : b.Space h) :
    d.nextBatch.extension.meet (d.lift i (b.represent h x)) (d.lift i (b.represent h y)) =
    d.lift i (b.extension.meet (b.represent h x) (b.represent h y)) := by
  rw [d.lift_template i h eligible x, d.lift_template i h eligible y]
  calc
    d.nextBatch.extension.meet (d.nextBatch.represent ⟨i, ⟨h, eligible⟩⟩ x)
        (d.nextBatch.represent ⟨i, ⟨h, eligible⟩⟩ y) =
        d.nextBatch.represent ⟨i, ⟨h, eligible⟩⟩ ((b.order h).meet x y) :=
      ((d.nextBatch.templateEmbedding ⟨i, ⟨h, eligible⟩⟩).map_meet x y).symm
    _ = d.lift i (b.represent h ((b.order h).meet x y)) :=
      (d.lift_template i h eligible _).symm
    _ = d.lift i (b.extension.meet (b.represent h x) (b.represent h y)) :=
      congrArg (d.lift i) ((b.templateEmbedding h).map_meet x y)

theorem meet_lift_fresh_pair (i : Task) (x y : b.Fresh)
    (hx : ¬ b.upper x.1 (d.source i)) (hy : ¬ b.upper y.1 (d.source i)) :
    d.nextBatch.extension.meet (d.lift i (.inr x)) (d.lift i (.inr y)) =
    d.lift i (b.extension.meet (.inr x) (.inr y)) := by
  classical
  by_cases same : x.1 = y.1
  · rcases x with ⟨h, x, xout⟩
    rcases y with ⟨k, y, yout⟩
    change h = k at same
    cases same
    rw [← b.represent_new h x xout, ← b.represent_new h y yout]
    exact d.meet_lift_template i h hx x y
  · by_cases hxy : b.extension.le (.inr x) (.inr y)
    · rw [meet_eq_left_of_le b.extension hxy, d.lift_new_outside i x hx,
        d.lift_new_outside i y hy]
      exact meet_eq_left_of_le d.nextBatch.extension ((d.fresh_pair_iff i x y hx hy).mpr hxy)
    · by_cases hyx : b.extension.le (.inr y) (.inr x)
      · rw [meet_comm b.extension (.inr x) (.inr y), meet_eq_left_of_le b.extension hyx,
          d.lift_new_outside i x hx, d.lift_new_outside i y hy,
          meet_comm d.nextBatch.extension]
        exact meet_eq_left_of_le d.nextBatch.extension ((d.fresh_pair_iff i y x hy hx).mpr hyx)
      · have different : (d.freshImage i x hx).1 ≠ (d.freshImage i y hy).1 := by
          intro h
          exact same (congrArg (fun label : d.Labels => label.2.val) h)
        have target_xy := fun h => hxy ((d.fresh_pair_iff i x y hx hy).mp h)
        have target_yx := fun h => hyx ((d.fresh_pair_iff i y x hy hx).mp h)
        rw [d.lift_new_outside i x hx, d.lift_new_outside i y hy]
        calc
          d.nextBatch.extension.meet (.inr (d.freshImage i x hx)) (.inr (d.freshImage i y hy)) =
              .inl (b.extension.meet ((d.previous i).toFun (b.shadow x))
                ((d.previous i).toFun (b.shadow y))) :=
            d.nextBatch.cross_meet_eq _ _ different target_xy target_yx
          _ = .inl ((d.previous i).toFun (P.meet (b.shadow x) (b.shadow y))) :=
            congrArg Sum.inl ((d.previous i).map_meet _ _).symm
          _ = d.lift i (.inl (P.meet (b.shadow x) (b.shadow y))) := rfl
          _ = d.lift i (b.extension.meet (.inr x) (.inr y)) :=
            congrArg (d.lift i) (b.cross_meet_eq x y same hxy hyx).symm

theorem image_base_iff (i : Task) (x : O ⊕ b.Fresh) :
    d.nextBatch.extension.le (d.lift i x) (.inl ((d.previous i).toFun (d.source i))) ↔
    b.extension.le x (.inl (d.source i)) := by
  classical
  cases x with
  | inl p => exact (d.previous i).le_iff p (d.source i)
  | inr x =>
    by_cases hx : b.upper x.1 (d.source i)
    · rw [d.lift_new_inside i x hx]
      constructor
      · intro _
        exact hx
      · intro _
        change b.extension.le ((d.representative i).toFun (.inr x))
          ((d.previous i).toFun (d.source i))
        rw [d.agree i (d.source i) (P.refl _)]
        exact ((d.representative i).le_iff _ _).mpr hx
    · rw [d.lift_new_outside i x hx]
      exact d.fresh_old_iff i x hx (d.source i)

theorem cut_identity (i : Task) (x : O ⊕ b.Fresh) :
    d.nextBatch.extension.meet (d.lift i x) (.inl ((d.previous i).toFun (d.source i))) =
    d.lift i (b.extension.meet x (.inl (d.source i))) := by
  classical
  cases x with
  | inl p => exact d.meet_lift_old_old i p (d.source i)
  | inr x =>
    by_cases hx : b.upper x.1 (d.source i)
    · rw [meet_eq_left_of_le b.extension (x := .inr x) (y := .inl (d.source i)) hx]
      exact meet_eq_left_of_le d.nextBatch.extension ((d.image_base_iff i (.inr x)).mpr hx)
    · exact d.meet_lift_fresh_old i x hx (d.source i)

noncomputable def baseEmbedding (i : Task) : MeetEmbedding b.extension d.nextBatch.extension :=
  compose (d.representative i).toMeetEmbedding d.nextBatch.oldEmbedding

theorem meet_lift_with_base (i : Task) (x y : O ⊕ b.Fresh)
    (hy : b.extension.le y (.inl (d.source i))) :
    d.nextBatch.extension.meet (d.lift i x) (d.lift i y) = d.lift i (b.extension.meet x y) := by
  apply base_meet_patch b.extension d.nextBatch.extension (d.lift i) (d.baseEmbedding i)
    (.inl (d.source i)) (.inl ((d.previous i).toFun (d.source i)))
  · exact congrArg Sum.inl (d.agree i (d.source i) (P.refl _)).symm
  · exact d.lift_agrees_on_base i
  · exact d.cut_identity i
  · exact hy

theorem lift_preserves_meets (i : Task) (x y : O ⊕ b.Fresh) :
    d.nextBatch.extension.meet (d.lift i x) (d.lift i y) = d.lift i (b.extension.meet x y) := by
  classical
  by_cases hy : b.extension.le y (.inl (d.source i))
  · exact d.meet_lift_with_base i x y hy
  · by_cases hx : b.extension.le x (.inl (d.source i))
    · calc
        d.nextBatch.extension.meet (d.lift i x) (d.lift i y) =
            d.nextBatch.extension.meet (d.lift i y) (d.lift i x) := meet_comm _ _ _
        _ = d.lift i (b.extension.meet y x) := d.meet_lift_with_base i y x hx
        _ = d.lift i (b.extension.meet x y) := congrArg (d.lift i) (meet_comm _ _ _)
    · cases x with
      | inl p =>
        cases y with
        | inl q => exact d.meet_lift_old_old i p q
        | inr y =>
          calc
            d.nextBatch.extension.meet (d.lift i (.inl p)) (d.lift i (.inr y)) =
                d.nextBatch.extension.meet (d.lift i (.inr y)) (d.lift i (.inl p)) := meet_comm _ _ _
            _ = d.lift i (b.extension.meet (.inr y) (.inl p)) := d.meet_lift_fresh_old i y hy p
            _ = d.lift i (b.extension.meet (.inl p) (.inr y)) := congrArg (d.lift i) (meet_comm _ _ _)
      | inr x =>
        cases y with
        | inl q => exact d.meet_lift_fresh_old i x hx q
        | inr y => exact d.meet_lift_fresh_pair i x y hx hy

theorem lift_monotone (i : Task) {x y : O ⊕ b.Fresh}
    (h : b.extension.le x y) : d.nextBatch.extension.le (d.lift i x) (d.lift i y) := by
  have hm := (d.lift_preserves_meets i x y).trans
    (congrArg (d.lift i) (meet_eq_left_of_le b.extension h))
  have lower := d.nextBatch.extension.meet_le_right (d.lift i x) (d.lift i y)
  rw [hm] at lower
  exact lower

theorem lift_reflects_order (i : Task) {x y : O ⊕ b.Fresh}
    (h : d.nextBatch.extension.le (d.lift i x) (d.lift i y)) : b.extension.le x y := by
  classical
  by_cases hx : b.extension.le x (.inl (d.source i))
  · have hxc := (d.image_base_iff i x).mpr hx
    have hcut : d.nextBatch.extension.le (d.lift i x)
        (d.lift i (b.extension.meet y (.inl (d.source i)))) := by
      rw [← d.cut_identity i y]
      exact d.nextBatch.extension.le_meet h hxc
    rw [d.lift_agrees_on_base i x hx,
      d.lift_agrees_on_base i _ (b.extension.meet_le_right y (.inl (d.source i)))] at hcut
    have source_cut := ((d.representative i).le_iff x (b.extension.meet y (.inl (d.source i)))).mp hcut
    exact b.extension.trans source_cut (b.extension.meet_le_left _ _)
  · by_cases hy : b.extension.le y (.inl (d.source i))
    · exact False.elim (hx ((d.image_base_iff i x).mp
        (d.nextBatch.extension.trans h ((d.image_base_iff i y).mpr hy))))
    · cases x with
      | inl p =>
        cases y with
        | inl q => exact ((d.previous i).le_iff p q).mp h
        | inr y =>
          rw [d.lift_old, d.lift_new_outside i y hy] at h
          exact (d.old_fresh_iff i y hy p).mp h
      | inr x =>
        cases y with
        | inl q =>
          rw [d.lift_new_outside i x hx, d.lift_old] at h
          exact (d.fresh_old_iff i x hx q).mp h
        | inr y =>
          rw [d.lift_new_outside i x hx, d.lift_new_outside i y hy] at h
          exact (d.fresh_pair_iff i x y hx hy).mp h

noncomputable def liftedEmbedding (i : Task) : MeetEmbedding b.extension d.nextBatch.extension where
  toFun := d.lift i
  le_iff _ _ := ⟨d.lift_reflects_order i, d.lift_monotone i⟩
  map_meet x y := (d.lift_preserves_meets i x y).symm

theorem lift_injective (i : Task) {x y : O ⊕ b.Fresh} (h : d.lift i x = d.lift i y) : x = y :=
  embedding_injective (d.liftedEmbedding i) h

theorem fresh_below_cap (i : Task) (x : b.Fresh) (eligible : ¬ b.upper x.1 (d.source i))
    (T : O) (top : ∀ p, P.le p T) :
    d.nextBatch.extension.le (.inr (d.freshImage i x eligible)) (.inl ((d.previous i).toFun T)) := by
  apply (d.fresh_old_iff i x eligible T).mpr
  rcases b.upper_nonempty x.1 with ⟨p, hp⟩
  exact b.upper_up x.1 hp (top p)

theorem fresh_outside_base (i : Task) (x : b.Fresh) (eligible : ¬ b.upper x.1 (d.source i)) :
    ¬ d.nextBatch.extension.le (.inr (d.freshImage i x eligible))
      (.inl ((d.previous i).toFun (d.source i))) :=
  fun h => eligible ((d.fresh_old_iff i x eligible (d.source i)).mp h)

theorem range_below_cap (i : Task) (T : O) (top : ∀ p, P.le p T) :
    ∀ x, d.nextBatch.extension.le (d.lift i x) (.inl ((d.previous i).toFun T)) := by
  intro x
  exact d.lift_monotone i (b.greatest_preserved T top x)

theorem fresh_accounting (T : O) (top : ∀ p, P.le p T) (z : d.nextBatch.Fresh) :
    ∃ i x, d.lift i x = .inr z ∧
      d.nextBatch.extension.le (.inr z) (.inl ((d.previous i).toFun T)) ∧
      ¬ d.nextBatch.extension.le (.inr z) (.inl ((d.previous i).toFun (d.source i))) := by
  rcases z with ⟨⟨i, ⟨h, eligible⟩⟩, y⟩
  refine ⟨i, .inr ⟨h, y⟩, d.lift_new_outside i ⟨h, y⟩ eligible, ?_, ?_⟩
  · exact d.fresh_below_cap i ⟨h, y⟩ eligible T top
  · exact d.fresh_outside_base i ⟨h, y⟩ eligible

end Inputs
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
