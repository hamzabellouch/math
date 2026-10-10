import Lean.Elab.Tactic.Omega
import OAI.SetTheory.PartitionPrinciple.Transfinite.CoherentTower

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps

namespace TaskSystem

universe u

variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)

def Union : Type u := A ⊕ ((n : Nat) × (f.stages n).batch.Fresh)

def birth : f.Union → Nat
  | .inl _ => 0
  | .inr x => x.1 + 1

noncomputable def inclusion : (n : Nat) → f.Point n → f.Union
  | 0, x => .inl x
  | n + 1, .inl x => inclusion n x
  | n + 1, .inr x => .inr ⟨n, x⟩

theorem inclusion_step (n : Nat) (x : f.Point n) :
    f.inclusion (n + 1) ((f.step n).toFun x) = f.inclusion n x := rfl

theorem inclusion_birth (n : Nat) (x : f.Point n) : f.birth (f.inclusion n x) ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    cases x with
    | inl x => exact Nat.le_trans (ih x) (Nat.le_succ n)
    | inr x => exact Nat.le_refl (n + 1)

theorem inclusion_injective (n : Nat) (x y : f.Point n)
    (eq : f.inclusion n x = f.inclusion n y) : x = y := by
  induction n with
  | zero => exact Sum.inl.inj eq
  | succ n ih =>
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (ih x y eq)
      | inr y =>
        have hb := f.inclusion_birth n x
        have he := congrArg f.birth eq
        change f.birth (f.inclusion n x) = n + 1 at he
        omega
    | inr x =>
      cases y with
      | inl y =>
        have hb := f.inclusion_birth n y
        have he := congrArg f.birth eq
        change n + 1 = f.birth (f.inclusion n y) at he
        omega
      | inr y =>
        have he := Sum.inr.inj eq
        have hy : x = y := eq_of_heq (Sigma.mk.inj he).2
        exact congrArg Sum.inr hy

theorem inclusion_original (n : Nat) (x : A) :
    f.inclusion n ((f.origin n).toFun x) = .inl x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← f.origins_coherent, f.inclusion_step, ih]

theorem raise_exists {n m : Nat} (h : n ≤ m) :
    ∃ e : MeetEmbedding (f.order n) (f.order m),
      ∀ x, f.inclusion m (e.toFun x) = f.inclusion n x := by
  induction h with
  | refl => exact ⟨(identityIso (f.order n)).toMeetEmbedding, fun _ => rfl⟩
  | @step m h ih =>
    rcases ih with ⟨e, he⟩
    exact ⟨compose e (f.step m), fun x => (f.inclusion_step m (e.toFun x)).trans (he x)⟩

theorem union_cover (x : f.Union) : ∃ (n : Nat) (a : f.Point n), f.inclusion n a = x := by
  cases x with
  | inl x => exact ⟨0, x, rfl⟩
  | inr x => exact ⟨x.1 + 1, .inr x.2, rfl⟩

theorem pair_cover (x y : f.Union) :
    ∃ (n : Nat) (a b : f.Point n), f.inclusion n a = x ∧ f.inclusion n b = y := by
  rcases f.union_cover x with ⟨n, a, ha⟩
  rcases f.union_cover y with ⟨m, b, hb⟩
  rcases f.raise_exists (Nat.le_max_left n m) with ⟨e, he⟩
  rcases f.raise_exists (Nat.le_max_right n m) with ⟨d, hd⟩
  exact ⟨max n m, e.toFun a, d.toFun b, (he a).trans ha, (hd b).trans hb⟩

def UnionLe (x y : f.Union) : Prop :=
  ∃ (n : Nat) (a b : f.Point n), f.inclusion n a = x ∧ f.inclusion n b = y ∧ (f.order n).le a b

theorem union_le_stage (n : Nat) (a b : f.Point n) :
    f.UnionLe (f.inclusion n a) (f.inclusion n b) ↔ (f.order n).le a b := by
  constructor
  · rintro ⟨m, x, y, hx, hy, hxy⟩
    rcases f.raise_exists (Nat.le_max_left n m) with ⟨e, he⟩
    rcases f.raise_exists (Nat.le_max_right n m) with ⟨d, hd⟩
    have ex : d.toFun x = e.toFun a := f.inclusion_injective _ _ _ ((hd x).trans (hx.trans (he a).symm))
    have ey : d.toFun y = e.toFun b := f.inclusion_injective _ _ _ ((hd y).trans (hy.trans (he b).symm))
    have h := (d.le_iff _ _).mpr hxy
    rw [ex, ey] at h
    exact (e.le_iff _ _).mp h
  · intro h
    exact ⟨n, a, b, rfl, rfl, h⟩

theorem union_le_refl (x : f.Union) : f.UnionLe x x := by
  rcases f.union_cover x with ⟨n, a, rfl⟩
  exact (f.union_le_stage n a a).mpr ((f.order n).refl a)

theorem union_le_trans {x y z : f.Union} (hxy : f.UnionLe x y) (hyz : f.UnionLe y z) :
    f.UnionLe x z := by
  rcases hxy with ⟨n, a, b, ha, hb, hab⟩
  rcases hyz with ⟨m, c, d, hc, hd, hcd⟩
  rcases f.raise_exists (Nat.le_max_left n m) with ⟨e, he⟩
  rcases f.raise_exists (Nat.le_max_right n m) with ⟨q, hq⟩
  have middle : e.toFun b = q.toFun c :=
    f.inclusion_injective _ _ _ ((he b).trans (hb.trans (hc.symm.trans (hq c).symm)))
  have lower := (e.le_iff _ _).mpr hab
  rw [middle] at lower
  exact ⟨max n m, e.toFun a, q.toFun d, (he a).trans ha, (hq d).trans hd,
    (f.order _).trans lower ((q.le_iff _ _).mpr hcd)⟩

theorem union_le_antisymm {x y : f.Union} (hxy : f.UnionLe x y) (hyx : f.UnionLe y x) : x = y := by
  rcases f.pair_cover x y with ⟨n, a, b, rfl, rfl⟩
  exact congrArg (f.inclusion n) ((f.order n).antisymm
    ((f.union_le_stage n a b).mp hxy) ((f.union_le_stage n b a).mp hyx))

theorem union_le_meet_stage (n : Nat) (a b : f.Point n) (z : f.Union)
    (hza : f.UnionLe z (f.inclusion n a)) (hzb : f.UnionLe z (f.inclusion n b)) :
    f.UnionLe z (f.inclusion n ((f.order n).meet a b)) := by
  rcases f.union_cover z with ⟨m, c, rfl⟩
  rcases f.raise_exists (Nat.le_max_left n m) with ⟨e, he⟩
  rcases f.raise_exists (Nat.le_max_right n m) with ⟨q, hq⟩
  have ha : f.UnionLe (f.inclusion (max n m) (q.toFun c)) (f.inclusion (max n m) (e.toFun a)) := by
    rw [hq, he]
    exact hza
  have hb : f.UnionLe (f.inclusion (max n m) (q.toFun c)) (f.inclusion (max n m) (e.toFun b)) := by
    rw [hq, he]
    exact hzb
  have lower := (f.order (max n m)).le_meet
    ((f.union_le_stage _ _ _).mp ha) ((f.union_le_stage _ _ _).mp hb)
  rw [← e.map_meet] at lower
  have result := (f.union_le_stage _ _ _).mpr lower
  rw [hq, he] at result
  exact result

theorem union_meet_exists (x y : f.Union) :
    ∃ m, f.UnionLe m x ∧ f.UnionLe m y ∧
      ∀ z, f.UnionLe z x → f.UnionLe z y → f.UnionLe z m := by
  rcases f.pair_cover x y with ⟨n, a, b, rfl, rfl⟩
  exact ⟨f.inclusion n ((f.order n).meet a b),
    (f.union_le_stage _ _ _).mpr ((f.order n).meet_le_left a b),
    (f.union_le_stage _ _ _).mpr ((f.order n).meet_le_right a b),
    f.union_le_meet_stage n a b⟩

noncomputable def unionMeet (x y : f.Union) : f.Union := Classical.choose (f.union_meet_exists x y)

noncomputable def unionOrder : MeetOrder f.Union where
  le := f.UnionLe
  meet := f.unionMeet
  refl := f.union_le_refl
  trans := f.union_le_trans
  antisymm := f.union_le_antisymm
  meet_le_left x y := (Classical.choose_spec (f.union_meet_exists x y)).1
  meet_le_right x y := (Classical.choose_spec (f.union_meet_exists x y)).2.1
  le_meet {z x y} := (Classical.choose_spec (f.union_meet_exists x y)).2.2 z

noncomputable def inclusionEmbedding (n : Nat) : MeetEmbedding (f.order n) f.unionOrder where
  toFun := f.inclusion n
  le_iff := f.union_le_stage n
  map_meet a b := by
    apply f.unionOrder.antisymm
    · exact f.unionOrder.le_meet
        ((f.union_le_stage n _ _).mpr ((f.order n).meet_le_left a b))
        ((f.union_le_stage n _ _).mpr ((f.order n).meet_le_right a b))
    · exact f.union_le_meet_stage n a b _
        (f.unionOrder.meet_le_left _ _) (f.unionOrder.meet_le_right _ _)

noncomputable def originalEmbedding : MeetEmbedding P f.unionOrder :=
  compose (f.origin 0) (f.inclusionEmbedding 0)

theorem union_top (x : f.Union) : f.unionOrder.le x (.inl f.top) := by
  rcases f.union_cover x with ⟨n, a, rfl⟩
  rw [← f.inclusion_original n f.top]
  exact (f.union_le_stage n _ _).mpr ((f.stages n).top a)

theorem union_bottom (zero : A) (bottom : ∀ x, P.le zero x) (x : f.Union) :
    f.unionOrder.le (.inl zero) x := by
  rcases f.union_cover x with ⟨n, a, rfl⟩
  rw [← f.inclusion_original n zero]
  exact (f.union_le_stage n _ _).mpr (f.stage_bottom n zero bottom a)







noncomputable def unionCompression (i : Task) : f.Union → f.Union
  | .inl x => f.inclusion 1 ((f.compression 0 i).toFun x)
  | .inr ⟨n, x⟩ => f.inclusion (n + 2) ((f.compression (n + 1) i).toFun (.inr x))

theorem unionCompression_inclusion (i : Task) (n : Nat) (x : f.Point n) :
    f.unionCompression i (f.inclusion n x) =
      f.inclusion (n + 1) ((f.compression n i).toFun x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases x with
    | inl x =>
      change f.unionCompression i (f.inclusion n x) =
        f.inclusion (n + 2) ((f.compression (n + 1) i).toFun ((f.step n).toFun x))
      exact (ih x).trans (congrArg (f.inclusion (n + 2)) (f.maps_coherent n i x))
    | inr x => rfl

noncomputable def unionAction (g : G) : f.Union → f.Union
  | .inl x => .inl ((f.action g).toFun x)
  | .inr ⟨n, x⟩ => f.inclusion (n + 1) ((f.stageAction (n + 1) g).toFun (.inr x))

theorem unionAction_inclusion (g : G) (n : Nat) (x : f.Point n) :
    f.unionAction g (f.inclusion n x) = f.inclusion n ((f.stageAction n g).toFun x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases x with
    | inl x =>
      change f.unionAction g (f.inclusion n x) =
        f.inclusion (n + 1) ((f.stageAction (n + 1) g).toFun ((f.step n).toFun x))
      exact (ih x).trans (congrArg (f.inclusion (n + 1)) (f.actions_coherent n g x))
    | inr x => rfl

theorem unionAction_one (x : f.Union) : f.unionAction f.group.one x = x := by
  rcases f.union_cover x with ⟨n, a, rfl⟩
  rw [f.unionAction_inclusion, f.stageAction_one]

theorem unionAction_mul (g h : G) (x : f.Union) :
    f.unionAction (f.group.mul g h) x = f.unionAction g (f.unionAction h x) := by
  rcases f.union_cover x with ⟨n, a, rfl⟩
  simp only [f.unionAction_inclusion, f.stageAction_mul]

theorem unionAction_left (g : G) (x : f.Union) :
    f.unionAction (f.group.inv g) (f.unionAction g x) = x := by
  rw [← f.unionAction_mul, f.group.inv_mul, f.unionAction_one]

theorem unionAction_right (g : G) (x : f.Union) :
    f.unionAction g (f.unionAction (f.group.inv g) x) = x := by
  rw [← f.unionAction_mul, f.group.mul_inv, f.unionAction_one]

theorem unionAction_order (g : G) (x y : f.Union) :
    f.unionOrder.le (f.unionAction g x) (f.unionAction g y) ↔ f.unionOrder.le x y := by
  rcases f.pair_cover x y with ⟨n, a, b, rfl, rfl⟩
  rw [f.unionAction_inclusion, f.unionAction_inclusion]
  exact ((f.inclusionEmbedding n).le_iff _ _).trans
    (((f.stageAction n g).le_iff a b).trans ((f.inclusionEmbedding n).le_iff a b).symm)

noncomputable def unionAutomorphism (g : G) : MeetIso f.unionOrder f.unionOrder :=
  isoOfOrder (f.unionAction g) (f.unionAction (f.group.inv g))
    (f.unionAction_left g) (f.unionAction_right g) (f.unionAction_order g)

theorem unionCompression_order (i : Task) (x y : f.Union) :
    f.unionOrder.le (f.unionCompression i x) (f.unionCompression i y) ↔ f.unionOrder.le x y := by
  rcases f.pair_cover x y with ⟨n, a, b, rfl, rfl⟩
  rw [f.unionCompression_inclusion, f.unionCompression_inclusion]
  exact ((f.inclusionEmbedding (n + 1)).le_iff _ _).trans
    (((f.compression n i).le_iff a b).trans ((f.inclusionEmbedding n).le_iff a b).symm)

theorem unionCompression_meet (i : Task) (x y : f.Union) :
    f.unionCompression i (f.unionOrder.meet x y) =
      f.unionOrder.meet (f.unionCompression i x) (f.unionCompression i y) := by
  rcases f.pair_cover x y with ⟨n, a, b, rfl, rfl⟩
  rw [f.unionCompression_inclusion i n a, f.unionCompression_inclusion i n b]
  calc
    f.unionCompression i (f.unionOrder.meet (f.inclusion n a) (f.inclusion n b)) =
        f.unionCompression i (f.inclusion n ((f.order n).meet a b)) :=
      congrArg (f.unionCompression i) ((f.inclusionEmbedding n).map_meet a b).symm
    _ = f.inclusion (n + 1) ((f.compression n i).toFun ((f.order n).meet a b)) :=
      f.unionCompression_inclusion i n _
    _ = f.inclusion (n + 1) ((f.order (n + 1)).meet
        ((f.compression n i).toFun a) ((f.compression n i).toFun b)) :=
      congrArg (f.inclusion (n + 1)) ((f.compression n i).map_meet a b)
    _ = _ := (f.inclusionEmbedding (n + 1)).map_meet _ _

noncomputable def unionCompressionEmbedding (i : Task) : MeetEmbedding f.unionOrder f.unionOrder where
  toFun := f.unionCompression i
  le_iff := f.unionCompression_order i
  map_meet := f.unionCompression_meet i

theorem union_equivariant (g : G) (i : Task) (x : f.Union) :
    (f.unionAutomorphism g).toFun (f.unionCompression i x) =
      f.unionCompression (f.perm g i) x := by
  rcases f.union_cover x with ⟨n, a, rfl⟩
  change f.unionAction g (f.unionCompression i (f.inclusion n a)) = _
  rw [f.unionCompression_inclusion, f.unionAction_inclusion, f.stage_equivariant,
    f.unionCompression_inclusion]

theorem union_agreement (g h : G) (v : A)
    (agree : ∀ x, P.le x v → (f.action g).toFun x = (f.action h).toFun x)
    (x : f.Union) (below : f.unionOrder.le x (.inl v)) :
    (f.unionAutomorphism g).toFun x = (f.unionAutomorphism h).toFun x := by
  rcases f.union_cover x with ⟨n, a, rfl⟩
  rw [← f.inclusion_original n v] at below
  have finite := ((f.inclusionEmbedding n).le_iff _ _).mp below
  change f.unionAction g (f.inclusion n a) = f.unionAction h (f.inclusion n a)
  rw [f.unionAction_inclusion, f.unionAction_inclusion, f.stage_agreement n g h v agree a finite]

noncomputable def unionCap (i : Task) : f.Union := f.unionCompression i (.inl f.top)

theorem unionCap_stage (n : Nat) (i : Task) :
    f.inclusion (n + 1) (f.cap n i) = f.unionCap i := by
  change f.inclusion (n + 1) ((f.compression n i).toFun ((f.origin n).toFun f.top)) = _
  rw [← f.unionCompression_inclusion, f.inclusion_original]
  rfl

theorem union_range_below_cap (i : Task) (x : f.Union) :
    f.unionOrder.le (f.unionCompression i x) (f.unionCap i) := by
  rcases f.union_cover x with ⟨n, a, rfl⟩
  rw [f.unionCompression_inclusion, ← f.unionCap_stage n i]
  exact ((f.inclusionEmbedding (n + 1)).le_iff _ _).mpr (f.range_below_cap n i a)

theorem union_base_agreement (i : Task) (x : f.Union)
    (below : f.unionOrder.le x (.inl (f.datum i).source)) :
    f.unionCompression i x = (f.unionAutomorphism (f.representative i)).toFun x := by
  rcases f.union_cover x with ⟨n, a, rfl⟩
  rw [← f.inclusion_original n (f.datum i).source] at below
  have finite := ((f.inclusionEmbedding n).le_iff _ _).mp below
  change f.unionCompression i (f.inclusion n a) = f.unionAction (f.representative i) (f.inclusion n a)
  rw [f.unionCompression_inclusion, f.stage_base_agreement n i a finite,
    f.inclusion_step, f.unionAction_inclusion]

theorem union_action_source (i : Task) :
    (f.unionAutomorphism (f.representative i)).toFun (.inl (f.datum i).source) =
      .inl (f.datum i).target :=
  congrArg Sum.inl (f.representative_target i)

theorem union_maps_base (i : Task) :
    f.unionCompression i (.inl (f.datum i).source) = .inl (f.datum i).target :=
  (f.union_base_agreement i _ (f.unionOrder.refl _)).trans (f.union_action_source i)







def UnionOriginal (x : f.Union) : Prop := ∃ a : A, Sum.inl a = x

theorem union_cap_separation (i j : Task) (different : i ≠ j) :
    f.unionOrder.le (f.unionCap i) (.inl (f.datum j).target) ∨
    f.unionOrder.le (f.unionCap j) (.inl (f.datum i).target) ∨
    f.unionOrder.meet (f.unionCap i) (f.unionCap j) =
      f.unionOrder.meet (.inl (f.datum i).target) (.inl (f.datum j).target) := by
  rcases f.cap_separation 0 i j different with h | h | h
  · have result := ((f.inclusionEmbedding 1).le_iff _ _).mpr h
    change f.unionOrder.le (f.inclusion 1 (f.cap 0 i))
      (f.inclusion 1 ((f.origin 1).toFun (f.datum j).target)) at result
    rw [f.unionCap_stage, f.inclusion_original] at result
    exact Or.inl result
  · have result := ((f.inclusionEmbedding 1).le_iff _ _).mpr h
    change f.unionOrder.le (f.inclusion 1 (f.cap 0 j))
      (f.inclusion 1 ((f.origin 1).toFun (f.datum i).target)) at result
    rw [f.unionCap_stage, f.inclusion_original] at result
    exact Or.inr (Or.inl result)
  · have result := congrArg (f.inclusionEmbedding 1).toFun h
    rw [(f.inclusionEmbedding 1).map_meet, (f.inclusionEmbedding 1).map_meet] at result
    change f.unionOrder.meet (f.inclusion 1 (f.cap 0 i)) (f.inclusion 1 (f.cap 0 j)) =
      f.unionOrder.meet (f.inclusion 1 ((f.origin 1).toFun (f.datum i).target))
        (f.inclusion 1 ((f.origin 1).toFun (f.datum j).target)) at result
    rw [f.unionCap_stage, f.unionCap_stage, f.inclusion_original, f.inclusion_original] at result
    exact Or.inr (Or.inr result)

theorem union_original_below_cap (i : Task) (v : A) :
    f.unionOrder.le (.inl v) (f.unionCap i) ↔ P.le v (f.datum i).target := by
  rw [← f.unionCap_stage 0 i, ← f.inclusion_original 1 v]
  exact ((f.inclusionEmbedding 1).le_iff _ _).trans (f.original_below_cap 0 i v)

theorem union_cap_strict (i : Task) :
    f.unionOrder.le (.inl (f.datum i).target) (f.unionCap i) ∧
    ¬ f.unionOrder.le (f.unionCap i) (.inl (f.datum i).target) := by
  constructor
  · exact (f.union_original_below_cap i _).mpr (P.refl _)
  · intro h
    rw [← f.union_maps_base i] at h
    have lower := (f.unionCompression_order i (.inl f.top) (.inl (f.datum i).source)).mp h
    exact f.source_proper i ((f.originalEmbedding.le_iff _ _).mp lower)

theorem union_separator_not_below_cap (i : Task) :
    ¬ f.unionOrder.le (.inl (f.datum i).separator) (f.unionCap i) :=
  fun h => (f.geometry i).separator_not_le_base ((f.union_original_below_cap i _).mp h)

theorem union_original_shadow (i : Task) (x : f.Union) (original : f.UnionOriginal x)
    (below : f.unionOrder.le x (f.unionCap i)) :
    f.unionOrder.le x (.inl (f.datum i).target) := by
  rcases original with ⟨v, rfl⟩
  exact (f.originalEmbedding.le_iff _ _).mpr ((f.union_original_below_cap i v).mp below)

theorem union_accounting (x : f.Union) :
    f.UnionOriginal x ∨ ∃ i y, f.unionCompression i y = x ∧
      f.unionOrder.le x (f.unionCap i) ∧ ¬ f.unionOrder.le x (.inl (f.datum i).target) := by
  cases x with
  | inl a => exact Or.inl ⟨a, rfl⟩
  | inr x =>
    rcases x with ⟨n, z⟩
    rcases f.stage_fresh_accounting n z with ⟨i, y, image, lower, outside⟩
    have image' : f.unionCompression i (f.inclusion n y) = .inr ⟨n, z⟩ :=
      (f.unionCompression_inclusion i n y).trans (congrArg (f.inclusion (n + 1)) image)
    refine Or.inr ⟨i, f.inclusion n y, image', ?_, ?_⟩
    · have result := ((f.inclusionEmbedding (n + 1)).le_iff _ _).mpr lower
      change f.unionOrder.le (.inr ⟨n, z⟩) (f.inclusion (n + 1) (f.cap n i)) at result
      rw [f.unionCap_stage] at result
      exact result
    · intro h
      have h' : f.unionOrder.le (f.inclusion (n + 1) (.inr z))
          (f.inclusion (n + 1) ((f.origin (n + 1)).toFun (f.datum i).target)) := by
        rw [f.inclusion_original]
        exact h
      exact outside (((f.inclusionEmbedding (n + 1)).le_iff _ _).mp h')

theorem union_base_filled (i : Task) (x : f.Union)
    (below : f.unionOrder.le x (.inl (f.datum i).target)) :
    ∃ y, f.unionCompression i y = x := by
  have filled := base_ideal_filled f.unionOrder (f.unionCompression i)
    (f.unionAutomorphism (f.representative i)) (.inl (f.datum i).source)
    (f.union_base_agreement i) x
  rw [f.union_action_source] at filled
  exact filled below

theorem union_surjective_ideal (i : Task) (x : f.Union)
    (below : f.unionOrder.le x (f.unionCap i)) : ∃ y, f.unionCompression i y = x :=
  range_completion_from_accounting f.unionOrder f.UnionOriginal
    (fun i => .inl (f.datum i).target) f.unionCap f.unionCompression
    f.union_base_filled f.union_original_shadow f.union_cap_separation f.union_accounting i x below

noncomputable def unionCompressionIso (i : Task) :
    MeetIso f.unionOrder (Attachment.idealOrder f.unionOrder (f.unionCap i)) :=
  isoOntoIdeal f.unionOrder (f.unionCompressionEmbedding i) (f.unionCap i)
    (f.union_range_below_cap i) (f.union_surjective_ideal i)

theorem unionCompressionIso_value (i : Task) (x : f.Union) :
    ((f.unionCompressionIso i).toFun x).val = f.unionCompression i x := rfl

end TaskSystem



section

universe u

def imageFamily {A B : Type u} {P : MeetOrder A} {Q : MeetOrder B}
    (e : MeetEmbedding P Q) (F : A → Prop) (x : B) : Prop :=
  ∃ a, F a ∧ e.toFun a = x

theorem positive_imageFamily {A B : Type u} {P : MeetOrder A} {Q : MeetOrder B}
    (e : MeetEmbedding P Q) (F : A → Prop) (x : B) :
    Positive Q (imageFamily e F) x ↔ PositiveOver e F x := by
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hy⟩
    exact ⟨a, ha, hy⟩
  · rintro ⟨a, ha, hy⟩
    exact ⟨e.toFun a, ⟨a, ha, rfl⟩, hy⟩

theorem positiveOver_imageFamily {A B C : Type u}
    {P : MeetOrder A} {Q : MeetOrder B} {R : MeetOrder C}
    (e : MeetEmbedding P Q) (j : MeetEmbedding Q R) (F : A → Prop) (x : C) :
    PositiveOver j (imageFamily e F) x ↔ PositiveOver (compose e j) F x := by
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hy⟩
    exact ⟨a, ha, hy⟩
  · rintro ⟨a, ha, hy⟩
    exact ⟨e.toFun a, ⟨a, ha, rfl⟩, hy⟩

namespace TaskSystem

open Attachment

variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)

def StageProfile (n : Nat) (i : Task) : Prop :=
  ∀ x : f.Point (n + 1), (f.order (n + 1)).le ((f.origin (n + 1)).toFun (f.datum i).separator) x →
    (PositiveOver (f.origin (n + 1)) (f.datum i).filter.mem x → (f.order (n + 1)).le (f.cap n i) x) ∧
    (¬ PositiveOver (f.origin (n + 1)) (f.datum i).filter.mem x →
      (f.order (n + 1)).meet (f.cap n i) x = (f.origin (n + 1)).toFun (f.datum i).target)

theorem first_stage_profile (i : Task) : f.StageProfile 0 i := by
  have profile := f.initial.copy_initial_profile f.top f.greatest f.source_proper i
  change Profile (f.order 1) (.inl ((f.action (f.representative i)).toFun (f.datum i).source))
    (.inl (f.datum i).separator) (f.cap 0 i) (f.initial.batch.originalFamily i) at profile
  rw [f.representative_target] at profile
  intro x above
  have positive : Positive (f.order 1) (f.initial.batch.originalFamily i) x ↔
      PositiveOver (f.origin 1) (f.datum i).filter.mem x := by
    constructor
    · rintro ⟨y, hy, hxy⟩
      cases y with
      | inl y => exact ⟨y, hy, hxy⟩
      | inr y => exact False.elim hy
    · rintro ⟨y, hy, hxy⟩
      exact ⟨.inl y, hy, hxy⟩
  exact ⟨fun h => (profile x above).1 (positive.mpr h),
    fun h => (profile x above).2 (fun hp => h (positive.mp hp))⟩

theorem stage_profile (n : Nat) (i : Task) : f.StageProfile n i := by
  induction n with
  | zero => exact f.first_stage_profile i
  | succ n ih =>
    have old : Profile (f.order (n + 1)) ((f.origin (n + 1)).toFun (f.datum i).target)
        ((f.origin (n + 1)).toFun (f.datum i).separator) (f.cap n i)
        (imageFamily (f.origin (n + 1)) (f.datum i).filter.mem) := by
      intro x above
      exact ⟨fun h => (ih x above).1 ((positive_imageFamily _ _ x).mp h),
        fun h => (ih x above).2 (fun hp => h ((positive_imageFamily _ _ x).mpr hp))⟩
    have nonempty : ∃ x, imageFamily (f.origin (n + 1)) (f.datum i).filter.mem x := by
      rcases (f.datum i).filter.nonempty with ⟨a, ha⟩
      exact ⟨(f.origin (n + 1)).toFun a, a, ha, rfl⟩
    have permitted : PermittedExtension (f.step (n + 1)) :=
      Attachment.permitted_extension (f.stages (n + 1)).batch.data
        (f.stages (n + 1)).batch.component_meets
    have persisted := profile_persists_one_step (f.step (n + 1))
      ((f.origin (n + 1)).toFun (f.datum i).target)
      ((f.origin (n + 1)).toFun (f.datum i).separator) (f.cap n i)
      (imageFamily (f.origin (n + 1)) (f.datum i).filter.mem) nonempty old
      (f.separator_not_below_cap n i) permitted
    intro x above
    have above' : (f.order (n + 2)).le
        ((f.step (n + 1)).toFun ((f.origin (n + 1)).toFun (f.datum i).separator)) x := by
      rw [f.origins_coherent]
      exact above
    have result := persisted x above'
    rw [f.caps_coherent, f.origins_coherent] at result
    have positive := positiveOver_imageFamily (f.origin (n + 1)) (f.step (n + 1))
      (f.datum i).filter.mem x
    exact ⟨fun h => result.1 (positive.mpr h),
      fun h => result.2 (fun hp => h (positive.mp hp))⟩

theorem union_positive_stage (i : Task) (n : Nat) (x : f.Point n) :
    (∃ a, (f.datum i).filter.mem a ∧ f.unionOrder.le (.inl a) (f.inclusion n x)) ↔
      PositiveOver (f.origin n) (f.datum i).filter.mem x := by
  constructor
  · rintro ⟨a, ha, hax⟩
    rw [← f.inclusion_original n a] at hax
    exact ⟨a, ha, ((f.inclusionEmbedding n).le_iff _ _).mp hax⟩
  · rintro ⟨a, ha, hax⟩
    refine ⟨a, ha, ?_⟩
    rw [← f.inclusion_original n a]
    exact ((f.inclusionEmbedding n).le_iff _ _).mpr hax

theorem union_profile_at_stage (i : Task) (n : Nat) (x : f.Point (n + 1))
    (above : f.unionOrder.le (.inl (f.datum i).separator) (f.inclusion (n + 1) x)) :
    ((∃ a, (f.datum i).filter.mem a ∧ f.unionOrder.le (.inl a) (f.inclusion (n + 1) x)) →
      f.unionOrder.le (f.unionCap i) (f.inclusion (n + 1) x)) ∧
    ((¬ ∃ a, (f.datum i).filter.mem a ∧ f.unionOrder.le (.inl a) (f.inclusion (n + 1) x)) →
      f.unionOrder.meet (f.unionCap i) (f.inclusion (n + 1) x) = .inl (f.datum i).target) := by
  rw [← f.inclusion_original (n + 1) (f.datum i).separator] at above
  have finite := ((f.inclusionEmbedding (n + 1)).le_iff ((f.origin (n + 1)).toFun (f.datum i).separator) x).mp above
  have profile := f.stage_profile n i x finite
  constructor
  · intro h
    have lower := profile.1 ((f.union_positive_stage i (n + 1) x).mp h)
    have result := ((f.inclusionEmbedding (n + 1)).le_iff _ _).mpr lower
    change f.unionOrder.le (f.inclusion (n + 1) (f.cap n i)) (f.inclusion (n + 1) x) at result
    rw [f.unionCap_stage] at result
    exact result
  · intro h
    have meet := profile.2 (fun hp => h ((f.union_positive_stage i (n + 1) x).mpr hp))
    have result := congrArg (f.inclusionEmbedding (n + 1)).toFun meet
    rw [(f.inclusionEmbedding (n + 1)).map_meet] at result
    change f.unionOrder.meet (f.inclusion (n + 1) (f.cap n i)) (f.inclusion (n + 1) x) =
      f.inclusion (n + 1) ((f.origin (n + 1)).toFun (f.datum i).target) at result
    rw [f.unionCap_stage, f.inclusion_original] at result
    exact result

theorem union_profile (i : Task) (x : f.Union)
    (above : f.unionOrder.le (.inl (f.datum i).separator) x) :
    ((∃ a, (f.datum i).filter.mem a ∧ f.unionOrder.le (.inl a) x) →
      f.unionOrder.le (f.unionCap i) x) ∧
    ((¬ ∃ a, (f.datum i).filter.mem a ∧ f.unionOrder.le (.inl a) x) →
      f.unionOrder.meet (f.unionCap i) x = .inl (f.datum i).target) := by
  rcases f.union_cover x with ⟨n, a, rfl⟩
  exact f.union_profile_at_stage i n ((f.step n).toFun a) above

end TaskSystem





structure CompressionAlgebra {A G Task Label : Type u} {P : MeetOrder A}
    (f : TaskSystem P G Task Label) where
  Space : Type u
  order : MeetOrder Space
  original : MeetEmbedding P order
  cap : Task → Space
  action : G → MeetIso order order
  compress : ∀ i, MeetIso order (Attachment.idealOrder order (cap i))
  top : ∀ x, order.le x (original.toFun f.top)
  bottom : ∀ zero, (∀ x, P.le zero x) → ∀ x, order.le (original.toFun zero) x
  action_one : ∀ x, (action f.group.one).toFun x = x
  action_mul : ∀ g h x, (action (f.group.mul g h)).toFun x =
    (action g).toFun ((action h).toFun x)
  action_original : ∀ g x, (action g).toFun (original.toFun x) =
    original.toFun ((f.action g).toFun x)
  strict : ∀ i, order.le (original.toFun (f.datum i).target) (cap i) ∧
    ¬ order.le (cap i) (original.toFun (f.datum i).target)
  separator : ∀ i, ¬ order.le (original.toFun (f.datum i).separator) (cap i)
  base_agreement : ∀ i x, order.le x (original.toFun (f.datum i).source) →
    ((compress i).toFun x).val = (action (f.representative i)).toFun x
  equivariant : ∀ g i x, (action g).toFun ((compress i).toFun x).val =
    ((compress (f.perm g i)).toFun x).val
  agreement : ∀ g h v,
    (∀ x, P.le x v → (f.action g).toFun x = (f.action h).toFun x) →
    ∀ x, order.le x (original.toFun v) → (action g).toFun x = (action h).toFun x
  separation : ∀ i j, i ≠ j →
    order.le (cap i) (original.toFun (f.datum j).target) ∨
    order.le (cap j) (original.toFun (f.datum i).target) ∨
    order.meet (cap i) (cap j) =
      order.meet (original.toFun (f.datum i).target) (original.toFun (f.datum j).target)
  profile : ∀ i x, order.le (original.toFun (f.datum i).separator) x →
    ((∃ a, (f.datum i).filter.mem a ∧ order.le (original.toFun a) x) → order.le (cap i) x) ∧
    ((¬ ∃ a, (f.datum i).filter.mem a ∧ order.le (original.toFun a) x) →
      order.meet (cap i) x = original.toFun (f.datum i).target)

namespace TaskSystem

variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)

noncomputable def compressionAlgebra : CompressionAlgebra f where
  Space := f.Union
  order := f.unionOrder
  original := f.originalEmbedding
  cap := f.unionCap
  action := f.unionAutomorphism
  compress := f.unionCompressionIso
  top := f.union_top
  bottom := f.union_bottom
  action_one := f.unionAction_one
  action_mul := f.unionAction_mul
  action_original _ _ := rfl
  strict := f.union_cap_strict
  separator := f.union_separator_not_below_cap
  base_agreement := f.union_base_agreement
  equivariant := f.union_equivariant
  agreement := f.union_agreement
  separation := f.union_cap_separation
  profile := f.union_profile

theorem union_equal_base_caps (i j : Task) (different : i ≠ j)
    (same_base : (f.datum i).target = (f.datum j).target) :
    f.unionOrder.meet (f.unionCap i) (f.unionCap j) = .inl (f.datum i).target := by
  rcases f.union_cap_separation i j different with h | h | h
  · rw [← same_base] at h
    exact False.elim ((f.union_cap_strict i).2 h)
  · rw [same_base] at h
    exact False.elim ((f.union_cap_strict j).2 h)
  · rw [← same_base] at h
    exact h.trans (meet_eq_left_of_le f.unionOrder (f.unionOrder.refl _))

end TaskSystem
end



namespace TaskSystem

universe u v

variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)

noncomputable def componentWord : (n : Nat) → (f.stages n).Components → List Task
  | 0, i => [i]
  | n + 1, i => i.1 :: componentWord n i.2.val

theorem componentWord_length (n : Nat) (i : (f.stages n).Components) :
    (f.componentWord n i).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (i.1 :: f.componentWord n i.2.val).length = n + 1 + 1
    rw [List.length_cons, ih]

theorem componentWord_injective (n : Nat) (i j : (f.stages n).Components)
    (eq : f.componentWord n i = f.componentWord n j) : i = j := by
  induction n with
  | zero => exact (List.cons.inj eq).1
  | succ n ih =>
    rcases i with ⟨i, ⟨h, hi⟩⟩
    rcases j with ⟨j, ⟨k, hj⟩⟩
    have head := (List.cons.inj eq).1
    have tail := ih h k (List.cons.inj eq).2
    cases head
    cases tail
    rfl

noncomputable def templateOriginal : (n : Nat) → (i : (f.stages n).Components) →
    MeetIso ((f.stages n).batch.order i) P
  | 0, _ => identityIso P
  | n + 1, i => templateOriginal n i.2.val

noncomputable def nodeCode : f.Union → List Task × A
  | .inl a => ([], a)
  | .inr ⟨n, x⟩ => (f.componentWord n x.1, (f.templateOriginal n x.1).toFun x.2.val)

theorem nodeCode_injective (x y : f.Union) (eq : f.nodeCode x = f.nodeCode y) : x = y := by
  cases x with
  | inl a =>
    cases y with
    | inl b => exact congrArg Sum.inl (congrArg Prod.snd eq)
    | inr y =>
      rcases y with ⟨n, h, y, hy⟩
      have length := congrArg (fun c : List Task × A => c.1.length) eq
      change 0 = (f.componentWord n h).length at length
      rw [f.componentWord_length] at length
      omega
  | inr x =>
    cases y with
    | inl b =>
      rcases x with ⟨n, h, x, hx⟩
      have length := congrArg (fun c : List Task × A => c.1.length) eq
      change (f.componentWord n h).length = 0 at length
      rw [f.componentWord_length] at length
      omega
    | inr y =>
      rcases x with ⟨n, h, x, hx⟩
      rcases y with ⟨m, k, y, hy⟩
      have length := congrArg (fun c : List Task × A => c.1.length) eq
      change (f.componentWord n h).length = (f.componentWord m k).length at length
      rw [f.componentWord_length, f.componentWord_length] at length
      have sameStage : n = m := by omega
      cases sameStage
      have sameComponent : h = k := f.componentWord_injective n h k (congrArg Prod.fst eq)
      cases sameComponent
      have sameNode : x = y := embedding_injective (f.templateOriginal n h).toMeetEmbedding
        (congrArg Prod.snd eq)
      cases sameNode
      rfl

theorem union_coding_bound : ∃ code : f.Union → List Task × A,
    ∀ x y, code x = code y → x = y :=
  ⟨f.nodeCode, f.nodeCode_injective⟩

theorem union_size_transfer {B : Type v} (pack : List Task × A → B)
    (injective : ∀ x y, pack x = pack y → x = y) :
    ∃ code : f.Union → B, ∀ x y, code x = code y → x = y :=
  ⟨fun x => pack (f.nodeCode x), fun x y eq => f.nodeCode_injective x y (injective _ _ eq)⟩

end TaskSystem

end PartitionPilot.Compression.RecursiveMaps

end OAI
