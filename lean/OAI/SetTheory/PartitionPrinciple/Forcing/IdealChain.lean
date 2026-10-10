import OAI.SetTheory.PartitionPrinciple.Geometry.PrincipalBatch

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u

structure IdealChain where
  Point : Nat → Type u
  order : ∀ n, MeetOrder (Point n)
  next : ∀ n, IdealEmbedding (order n) (order (n + 1))

namespace IdealChain
variable (c : IdealChain.{u})

noncomputable def up {n m : Nat} (h : n ≤ m) (x : c.Point n) : c.Point m :=
  Nat.leRecOn h (fun {k} x => (c.next k).toFun x) x

theorem up_self (n : Nat) (x : c.Point n) : c.up (Nat.le_refl n) x = x :=
  Nat.leRecOn_self x

theorem up_succ {n m : Nat} (h : n ≤ m) (x : c.Point n) :
    c.up (Nat.le_succ_of_le h) x = (c.next m).toFun (c.up h x) :=
  Nat.leRecOn_succ h x

theorem up_comp {n m k : Nat} (hnm : n ≤ m) (hmk : m ≤ k) (x : c.Point n) :
    c.up (Nat.le_trans hnm hmk) x = c.up hmk (c.up hnm x) :=
  Nat.leRecOn_trans hnm hmk x

theorem up_le {n m : Nat} (h : n ≤ m) (x y : c.Point n) :
    (c.order m).le (c.up h x) (c.up h y) ↔ (c.order n).le x y := by
  induction h with
  | refl => rw [c.up_self, c.up_self]
  | @step m h ih => rw [c.up_succ h, c.up_succ h, (c.next m).le_iff, ih]

theorem up_ideal {n m : Nat} (h : n ≤ m) (a : c.Point n) (x : c.Point m)
    (lower : (c.order m).le x (c.up h a)) : ∃ b, c.up h b = x := by
  induction h with
  | refl => exact ⟨x, c.up_self _ _⟩
  | @step m h ih =>
    rw [c.up_succ h] at lower
    rcases (c.next m).ideal (c.up h a) x lower with ⟨y, rfl⟩
    rcases ih y (((c.next m).le_iff _ _).mp lower) with ⟨b, eq⟩
    exact ⟨b, by rw [c.up_succ h, eq]⟩

noncomputable def raise {n m : Nat} (h : n ≤ m) : IdealEmbedding (c.order n) (c.order m) :=
  IdealEmbedding.ofOrderMap (c.up h) (c.up_le h) (c.up_ideal h)

def Label := (n : Nat) × c.Point n

def Related (x y : c.Label) : Prop :=
  ∃ (k : Nat) (hx : x.1 ≤ k) (hy : y.1 ≤ k), c.up hx x.2 = c.up hy y.2

theorem related_refl (x : c.Label) : c.Related x x := ⟨x.1, le_refl _, le_refl _, rfl⟩

theorem related_symm {x y : c.Label} (h : c.Related x y) : c.Related y x := by
  rcases h with ⟨k, hx, hy, eq⟩
  exact ⟨k, hy, hx, eq.symm⟩

theorem related_trans {x y z : c.Label} (hxy : c.Related x y) (hyz : c.Related y z) :
    c.Related x z := by
  rcases hxy with ⟨k, hx, hy, eq1⟩
  rcases hyz with ⟨l, hy', hz, eq2⟩
  refine ⟨max k l, le_trans hx (Nat.le_max_left _ _), le_trans hz (Nat.le_max_right _ _), ?_⟩
  calc
    c.up _ x.2 = c.up (Nat.le_max_left k l) (c.up hx x.2) := c.up_comp _ _ _
    _ = c.up (Nat.le_max_left k l) (c.up hy y.2) := congrArg _ eq1
    _ = c.up (Nat.le_max_right k l) (c.up hy' y.2) :=
      (c.up_comp _ _ _).symm.trans (c.up_comp _ _ _)
    _ = c.up (Nat.le_max_right k l) (c.up hz z.2) := congrArg _ eq2
    _ = c.up _ z.2 := (c.up_comp _ _ _).symm

def setoid : Setoid c.Label := ⟨c.Related, c.related_refl, c.related_symm, c.related_trans⟩
def Union := Quotient c.setoid
def point (n : Nat) (x : c.Point n) : c.Union := Quotient.mk c.setoid ⟨n, x⟩

theorem include_up {n m : Nat} (h : n ≤ m) (x : c.Point n) :
    c.point m (c.up h x) = c.point n x := by
  apply Quotient.sound
  exact ⟨m, le_refl _, h, c.up_self _ _⟩

theorem include_injective (n : Nat) : Function.Injective (c.point n) := by
  intro x y eq
  rcases Quotient.exact eq with ⟨k, hx, hy, same⟩
  exact embedding_injective (c.raise hx).toMeetEmbedding same

theorem cover (x : c.Union) : ∃ n a, c.point n a = x := by
  induction x using Quotient.ind with
  | _ x => exact ⟨x.1, x.2, rfl⟩

theorem pair_cover (x y : c.Union) :
    ∃ n a b, c.point n a = x ∧ c.point n b = y := by
  rcases c.cover x with ⟨n, a, rfl⟩
  rcases c.cover y with ⟨m, b, rfl⟩
  exact ⟨max n m, c.up (Nat.le_max_left _ _) a, c.up (Nat.le_max_right _ _) b,
    c.include_up _ _, c.include_up _ _⟩

def Le (x y : c.Union) : Prop :=
  ∃ n a b, c.point n a = x ∧ c.point n b = y ∧ (c.order n).le a b

theorem le_stage (n : Nat) (a b : c.Point n) :
    c.Le (c.point n a) (c.point n b) ↔ (c.order n).le a b := by
  constructor
  · rintro ⟨m, x, y, hx, hy, lower⟩
    let k := max n m
    have ex : c.up (Nat.le_max_right n m) x = c.up (Nat.le_max_left n m) a := by
      apply c.include_injective k
      rw [c.include_up, c.include_up]
      exact hx
    have ey : c.up (Nat.le_max_right n m) y = c.up (Nat.le_max_left n m) b := by
      apply c.include_injective k
      rw [c.include_up, c.include_up]
      exact hy
    have lifted := (c.up_le (Nat.le_max_right n m) x y).mpr lower
    rw [ex, ey] at lifted
    exact (c.up_le (Nat.le_max_left n m) a b).mp lifted
  · intro h
    exact ⟨n, a, b, rfl, rfl, h⟩

theorem le_refl (x : c.Union) : c.Le x x := by
  rcases c.cover x with ⟨n, a, rfl⟩
  exact (c.le_stage n a a).mpr ((c.order n).refl a)

theorem le_trans {x y z : c.Union} (hxy : c.Le x y) (hyz : c.Le y z) : c.Le x z := by
  rcases hxy with ⟨n, a, b, ha, hb, lower1⟩
  rcases hyz with ⟨m, d, e, hd, he, lower2⟩
  have middle : c.up (Nat.le_max_left n m) b = c.up (Nat.le_max_right n m) d := by
    apply c.include_injective (max n m)
    rw [c.include_up, c.include_up]
    exact hb.trans hd.symm
  have left := (c.up_le (Nat.le_max_left n m) a b).mpr lower1
  rw [middle] at left
  exact ⟨max n m, _, _, (c.include_up _ _).trans ha, (c.include_up _ _).trans he,
    (c.order _).trans left ((c.up_le (Nat.le_max_right n m) d e).mpr lower2)⟩

theorem le_antisymm {x y : c.Union} (hxy : c.Le x y) (hyx : c.Le y x) : x = y := by
  rcases c.pair_cover x y with ⟨n, a, b, rfl, rfl⟩
  exact congrArg (c.point n) ((c.order n).antisymm
    ((c.le_stage _ _ _).mp hxy) ((c.le_stage _ _ _).mp hyx))

theorem include_ideal (n : Nat) (a : c.Point n) (x : c.Union) (lower : c.Le x (c.point n a)) :
    ∃ b, c.point n b = x := by
  rcases c.cover x with ⟨m, b, rfl⟩
  have lifted : c.Le (c.point (max n m) (c.up (Nat.le_max_right n m) b))
      (c.point (max n m) (c.up (Nat.le_max_left n m) a)) := by
    rw [c.include_up, c.include_up]
    exact lower
  rcases c.up_ideal (Nat.le_max_left n m) a _ ((c.le_stage _ _ _).mp lifted) with ⟨d, eq⟩
  refine ⟨d, ?_⟩
  rw [← c.include_up (Nat.le_max_left n m) d, eq, c.include_up]

theorem stage_meet_spec (n : Nat) (a b : c.Point n) :
    c.Le (c.point n ((c.order n).meet a b)) (c.point n a) ∧
    c.Le (c.point n ((c.order n).meet a b)) (c.point n b) ∧
    ∀ z, c.Le z (c.point n a) → c.Le z (c.point n b) →
      c.Le z (c.point n ((c.order n).meet a b)) := by
  refine ⟨(c.le_stage _ _ _).mpr ((c.order n).meet_le_left a b),
    (c.le_stage _ _ _).mpr ((c.order n).meet_le_right a b), ?_⟩
  intro z hza hzb
  rcases c.include_ideal n a z hza with ⟨d, rfl⟩
  exact (c.le_stage _ _ _).mpr ((c.order n).le_meet
    ((c.le_stage _ _ _).mp hza) ((c.le_stage _ _ _).mp hzb))

theorem meets_exist (x y : c.Union) :
    ∃ m, c.Le m x ∧ c.Le m y ∧ ∀ z, c.Le z x → c.Le z y → c.Le z m := by
  rcases c.pair_cover x y with ⟨n, a, b, rfl, rfl⟩
  exact ⟨c.point n ((c.order n).meet a b), c.stage_meet_spec n a b⟩

noncomputable def unionOrder : MeetOrder c.Union where
  le := c.Le
  meet x y := Classical.choose (c.meets_exist x y)
  refl := c.le_refl
  trans := c.le_trans
  antisymm := c.le_antisymm
  meet_le_left x y := (Classical.choose_spec (c.meets_exist x y)).1
  meet_le_right x y := (Classical.choose_spec (c.meets_exist x y)).2.1
  le_meet {z x y} := (Classical.choose_spec (c.meets_exist x y)).2.2 z

noncomputable def inclusion (n : Nat) : IdealEmbedding (c.order n) c.unionOrder :=
  IdealEmbedding.ofOrderMap (c.point n) (c.le_stage n) (c.include_ideal n)

theorem vertex_preserved (n : Nat) {V : Type u} {Q : MeetOrder V}
    (f : IdealEmbedding Q (c.order n)) :
    ∃ e : IdealEmbedding Q c.unionOrder, ∀ x, e.toFun x = c.point n (f.toFun x) :=
  ⟨f.comp (c.inclusion n), fun _ => rfl⟩

end IdealChain
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
