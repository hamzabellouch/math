import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.DiagramOrder
import OAI.SetTheory.PartitionConsistency.Algebra.MergerCones

namespace OAI

/-! ## Probe extension: direct-limit letters and cancellative normal forms -/

namespace PartitionConsistency.ProbeAlgebra
universe u
open DiagramOrder

/-- The actual nondecreasing sequence occurring in a probe datum. The
transition and terminal factors will be derived, not additionally chosen. -/
structure Path (M : Type u) [LeftCancelMonoid M] (a : M) where
  node : ℕ → M
  zero : node 0 = 1
  increasing : ∀ {i j}, i ≤ j → node i ∣ node j
  bounded : ∀ i, node i ∣ a

namespace Path
variable {M : Type u} [LeftCancelMonoid M] {a : M} (P : Path M a)

/-- The unique right factor between two nodes of the path. -/
noncomputable def factor (i j : ℕ) (h : i ≤ j) : M := (P.increasing h).choose

@[simp] theorem node_factor (i j : ℕ) (h : i ≤ j) :
    P.node i * P.factor i j h = P.node j := (P.increasing h).choose_spec.symm

@[simp] theorem factor_self (i : ℕ) : P.factor i i le_rfl = 1 := by
  apply mul_left_cancel (a := P.node i)
  rw [node_factor, mul_one]

@[simp] theorem factor_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    P.factor i j hij * P.factor j k hjk = P.factor i k (hij.trans hjk) := by
  apply mul_left_cancel (a := P.node i)
  rw [← mul_assoc, node_factor, node_factor, node_factor]

@[simp] theorem factor_zero (i : ℕ) : P.factor 0 i (Nat.zero_le i) = P.node i := by
  have h := P.node_factor 0 i (Nat.zero_le i)
  simpa only [P.zero, one_mul] using h

/-- The unique terminal factor from a node to `a`. -/
noncomputable def terminal (i : ℕ) : M := (P.bounded i).choose

@[simp] theorem node_terminal (i : ℕ) : P.node i * P.terminal i = a :=
  (P.bounded i).choose_spec.symm

@[simp] theorem factor_terminal {i j : ℕ} (hij : i ≤ j) :
    P.factor i j hij * P.terminal j = P.terminal i := by
  apply mul_left_cancel (a := P.node i)
  rw [← mul_assoc, node_factor, node_terminal, node_terminal]

@[simp] theorem terminal_zero : P.terminal 0 = a := by
  simpa only [P.zero, one_mul] using P.node_terminal 0

/-- Right multiplication by a transition factor. This map is deliberately
not assumed injective: the construction has only left cancellation. -/
noncomputable def transition (i j : ℕ) (h : i ≤ j) : M →[M] M where
  toFun x := x * P.factor i j h
  map_smul' _ _ := mul_assoc _ _ _

@[simp] theorem transition_apply (i j : ℕ) (h : i ≤ j) (x : M) :
    P.transition i j h x = x * P.factor i j h := rfl

instance : DirectedSystem (fun _ : ℕ => M) (P.transition · · ·) where
  map_self := by intro i x; simp only [transition_apply, factor_self, mul_one]
  map_map := by intro k j i hij hjk x; simp only [transition_apply, mul_assoc, factor_trans]

/-- The direct-limit letters `[x,i]` of the probe normal forms. -/
abbrev Letters := DirectLimit (fun _ : ℕ => M) P.transition

/-- The letter at a specified finite stage. Distinct stage elements need
not have distinct images. -/
noncomputable def letter (i : ℕ) (x : M) : P.Letters := Quotient.mk _ ⟨i, x⟩

/-- Equality in the direct limit is equality at some common finite stage. -/
theorem letter_eq_iff (i j : ℕ) (x y : M) :
    P.letter i x = P.letter j y ↔
      ∃ k, ∃ hi : i ≤ k, ∃ hj : j ≤ k,
        x * P.factor i k hi = y * P.factor j k hj := Quotient.eq

@[simp] theorem letter_transition {i j : ℕ} (hij : i ≤ j) (x : M) :
    P.letter j (x * P.factor i j hij) = P.letter i x :=
  DirectLimit.mk_apply (F := fun _ : ℕ => M) (f := P.transition) i j x hij

/-- Left multiplication commutes with the right transition maps. -/
noncomputable def act (x : M) : P.Letters → P.Letters :=
  DirectLimit.map P.transition P.transition (fun _ y => x * y)
    (fun _ _ _ _ => by simp only [transition_apply, mul_assoc])

@[simp] theorem act_letter (x : M) (i : ℕ) (y : M) :
    P.act x (P.letter i y) = P.letter i (x * y) := rfl

@[simp] theorem act_one (s : P.Letters) : P.act 1 s = s := by
  induction s using DirectLimit.induction with
  | ih i x =>
    change P.act 1 (P.letter i x) = P.letter i x
    simp only [act_letter, one_mul]

@[simp] theorem act_mul (x y : M) (s : P.Letters) :
    P.act (x * y) s = P.act x (P.act y s) := by
  induction s using DirectLimit.induction with
  | ih i z =>
    change P.act (x * y) (P.letter i z) = P.act x (P.act y (P.letter i z))
    simp only [act_letter, mul_assoc]

/-- Cancellation occurs at a common finite stage. No cancellation on the
right, nor injectivity of transition maps, is used here. -/
theorem act_injective (x : M) : Function.Injective (P.act x) := by
  intro s t
  induction s using DirectLimit.induction with
  | ih i y =>
    induction t using DirectLimit.induction with
    | ih j z =>
      intro he
      obtain ⟨k, hi, hj, hk⟩ := (P.letter_eq_iff i j (x * y) (x * z)).1 he
      apply (P.letter_eq_iff i j y z).2
      exact ⟨k, hi, hj, mul_left_cancel (by simpa only [mul_assoc] using hk)⟩

/-- The map `k([x,i]) = x c_i`; compatibility uses the terminal-factor
identity, not an incorrectly presumed injective transition map. -/
noncomputable def target : P.Letters → M :=
  DirectLimit.lift P.transition (fun i x => x * P.terminal i)
    (fun i j hij x => by simp only [transition_apply, mul_assoc, factor_terminal])

@[simp] theorem target_letter (i : ℕ) (x : M) :
    P.target (P.letter i x) = x * P.terminal i := rfl

@[simp] theorem target_act (x : M) (s : P.Letters) :
    P.target (P.act x s) = x * P.target s := by
  induction s using DirectLimit.induction with
  | ih i y =>
    change P.target (P.act x (P.letter i y)) = x * P.target (P.letter i y)
    simp only [act_letter, target_letter, mul_assoc]

/-- The old element `h(s) = k(s)e` at which a letter can be consumed. -/
noncomputable def exit (e : M) (s : P.Letters) : M := P.target s * e

@[simp] theorem exit_act (e x : M) (s : P.Letters) :
    P.exit e (P.act x s) = x * P.exit e s := by
  simp only [exit, target_act, mul_assoc]

/-- Membership in an old left-translation cone of letters. -/
def InCone (x : M) (s : P.Letters) : Prop := ∃ t : P.Letters, P.act x t = s

/-- Cone membership can also be tested at a finite stage, retaining the
actual quotient rather than just the existence of an old comparison. -/
theorem inCone_letter_iff (x : M) (i : ℕ) (y : M) :
    P.InCone x (P.letter i y) ↔
      ∃ j, ∃ hij : i ≤ j, x ∣ y * P.factor i j hij := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨j, z, rfl⟩ := DirectLimit.exists_eq_mk P.transition t
    obtain ⟨k, hj, hi, hk⟩ := (P.letter_eq_iff j i (x * z) y).1 ht
    exact ⟨k, hi, ⟨z * P.factor j k hj, by simpa only [mul_assoc] using hk.symm⟩⟩
  · rintro ⟨j, hij, z, hz⟩
    refine ⟨P.letter j z, ?_⟩
    rw [act_letter, ← hz, letter_transition]

/-- Every old divisor of a letter divides its target. -/
theorem dvd_target_of_inCone {x : M} {s : P.Letters} (h : P.InCone x s) : x ∣ P.target s := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨P.target t, P.target_act x t⟩

theorem one_inCone (s : P.Letters) : P.InCone 1 s := ⟨s, P.act_one s⟩

theorem inCone_of_dvd {x y : M} {s : P.Letters} (hxy : x ∣ y) (hys : P.InCone y s) :
    P.InCone x s := by
  obtain ⟨z, rfl⟩ := hxy
  obtain ⟨t, ht⟩ := hys
  exact ⟨P.act z t, (P.act_mul x z t).symm.trans ht⟩

/-- Old cone intersections lift exactly to the direct limit, including
empty intersections. -/
theorem inCone_intersection (x y j : M)
    (hj : ∀ z : M, x ∣ z ∧ y ∣ z ↔ j ∣ z) (s : P.Letters) :
    P.InCone x s ∧ P.InCone y s ↔ P.InCone j s := by
  constructor
  · rintro ⟨⟨t, ht⟩, ⟨v, hv⟩⟩
    obtain ⟨i, u, rfl⟩ := DirectLimit.exists_eq_mk P.transition t
    obtain ⟨l, w, rfl⟩ := DirectLimit.exists_eq_mk P.transition v
    have he : P.letter i (x * u) = P.letter l (y * w) := ht.trans hv.symm
    obtain ⟨k, hi, hl, hk⟩ := (P.letter_eq_iff i l (x * u) (y * w)).1 he
    have hc : j ∣ (x * u) * P.factor i k hi := by
      apply (hj _).1
      exact ⟨⟨u * P.factor i k hi, mul_assoc _ _ _⟩,
        ⟨w * P.factor l k hl, hk.trans (mul_assoc _ _ _)⟩⟩
    obtain ⟨r, hr⟩ := hc
    refine ⟨P.letter k r, ?_⟩
    rw [act_letter, ← hr, letter_transition]
    exact ht
  · intro hs
    have hs' := (hj j).2 (dvd_refl j)
    exact ⟨P.inCone_of_dvd hs'.1 hs, P.inCone_of_dvd hs'.2 hs⟩

/-- If two old cones meet in the letters, the old monoid already contains
a common right multiple. Thus a new letter creates no old nonjoin. -/
theorem old_common_multiple_of_cones {x y : M} {s : P.Letters}
    (hx : P.InCone x s) (hy : P.InCone y s) : ∃ z : M, x ∣ z ∧ y ∣ z :=
  ⟨P.target s, P.dvd_target_of_inCone hx, P.dvd_target_of_inCone hy⟩

/-- The initial new letter has exactly the old-divisor profile given by
the lower closure of the original countable path. -/
theorem initial_profile (x : M) : P.InCone x (P.letter 0 1) ↔ ∃ i : ℕ, x ∣ P.node i := by
  rw [inCone_letter_iff]
  simp only [factor_zero, one_mul, exists_prop, Nat.zero_le, true_and]

/-- The important separation between a head and its exit cone. It uses
conicality and left cancellation, but does not use right cancellation. -/
theorem head_separation [IsConical M] {e : M} (he : e ≠ 1) (s : P.Letters) :
    ¬ P.InCone (P.exit e s) s := by
  intro h
  obtain ⟨z, hz⟩ := P.dvd_target_of_inCone h
  have heq : e * z = 1 := by
    apply mul_left_cancel (a := P.target s)
    simpa only [exit, mul_assoc, mul_one] using hz.symm
  exact he (IsConical.eq_one_of_mul_eq_one heq).1

/-- Countably many old copies suffice for the direct-limit alphabet. -/
theorem letters_cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) : Cardinal.mk P.Letters ≤ μ := by
  calc
    Cardinal.mk P.Letters ≤ Cardinal.mk (Σ _ : ℕ, M) := Cardinal.mk_quotient_le
    _ = Cardinal.aleph0 * Cardinal.mk M := by simp [Cardinal.mk_sigma, Cardinal.sum_const]
    _ ≤ max (max Cardinal.aleph0 (Cardinal.mk M)) Cardinal.aleph0 := Cardinal.mul_le_max _ _
    _ ≤ μ := max_le (max_le hω hM) hω

end Path
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra
universe u v
open DiagramOrder

/-- The letter action and exit map used in the terminating probe normal
forms. These laws will be realized by the path direct limit above. -/
structure Alphabet (M : Type u) (S : Type v) [Monoid M] where
  act : M → S → S
  one_act : ∀ s, act 1 s = s
  mul_act : ∀ x y s, act (x * y) s = act x (act y s)
  act_injective : ∀ x, Function.Injective (act x)
  exit : S → M
  exit_act : ∀ x s, exit (act x s) = x * exit s
  separated : ∀ s, ¬ ∃ t, act (exit s) t = s

namespace Path
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}

/-- The direct limit supplies all the alphabet laws for the probe extension. -/
noncomputable def alphabet (P : Path M a) (he : e ≠ 1) : Alphabet M P.Letters where
  act := P.act
  one_act := P.act_one
  mul_act := P.act_mul
  act_injective := P.act_injective
  exit := P.exit e
  exit_act := P.exit_act e
  separated := P.head_separation he
end Path

/-- Unreduced strings, including a compulsory terminal old factor. -/
inductive Raw (M : Type u) (S : Type v) : Type (max u v)
  | old : M → Raw M S
  | cons : S → Raw M S → Raw M S

namespace Raw
variable {M : Type u} {S : Type v} [Monoid M] (A : Alphabet M S)

def headDiv (x : M) : Raw M S → Prop
  | .old y => x ∣ y
  | .cons s _ => ∃ t, A.act x t = s

def reduced (b : M) : Raw M S → Prop
  | .old _ => True
  | .cons _ w => w.reduced b ∧ ¬ w.headDiv A b

def oldAct (x : M) : Raw M S → Raw M S
  | .old y => .old (x * y)
  | .cons s w => .cons (A.act x s) w

@[simp] theorem oldAct_one (w : Raw M S) : oldAct A 1 w = w := by
  cases w with
  | old y => simp only [oldAct, one_mul]
  | cons s w => simp only [oldAct, A.one_act]

@[simp] theorem oldAct_mul (x y : M) (w : Raw M S) :
    oldAct A (x * y) w = oldAct A x (oldAct A y w) := by
  cases w with
  | old z => simp only [oldAct, mul_assoc]
  | cons s w => simp only [oldAct, A.mul_act]

@[simp] theorem reduced_oldAct (b x : M) (w : Raw M S) :
    (oldAct A x w).reduced A b ↔ w.reduced A b := by cases w <;> rfl

theorem headDiv_iff (x : M) (w : Raw M S) :
    w.headDiv A x ↔ ∃ v : Raw M S, oldAct A x v = w := by
  cases w with
  | old y =>
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨.old z, congrArg Raw.old hz.symm⟩
    · rintro ⟨v, hv⟩
      cases v with
      | old z => exact ⟨z, (Raw.old.inj hv).symm⟩
      | cons s v => cases hv
  | cons s w =>
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨.cons t w, congrArg (Raw.cons · w) ht⟩
    · rintro ⟨v, hv⟩
      cases v with
      | old z => cases hv
      | cons t v => exact ⟨t, (Raw.cons.inj hv).1⟩

theorem oldAct_injective [IsLeftCancelMul M] (x : M) :
    Function.Injective (oldAct A x) := by
  intro w v he
  cases w <;> cases v
  · exact congrArg Raw.old (mul_left_cancel (Raw.old.inj he))
  · cases he
  · cases he
  · obtain ⟨hs, hw⟩ := Raw.cons.inj he
    exact congrArg₂ Raw.cons (A.act_injective x hs) hw
end Raw

/-- Literal irreducibles for the reductions `s(bZ) ↦ h(s)Z`. -/
abbrev Word {M : Type u} {S : Type v} [Monoid M] (A : Alphabet M S) (b : M) :=
  {w : Raw M S // w.reduced A b}

namespace Word
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] (A : Alphabet M S) (b : M)

def old (x : M) : Word A b := ⟨.old x, trivial⟩

def headDiv (x : M) (w : Word A b) : Prop := w.val.headDiv A x

def cons (s : S) (w : Word A b) (hw : ¬ headDiv A b b w) : Word A b :=
  ⟨.cons s w.val, w.property, hw⟩

def oldAct (x : M) (w : Word A b) : Word A b :=
  ⟨w.val.oldAct A x, (Raw.reduced_oldAct A b x w.val).2 w.property⟩

@[simp] theorem oldAct_old (x y : M) : oldAct A b x (old A b y) = old A b (x * y) := rfl

@[simp] theorem oldAct_one (w : Word A b) : oldAct A b 1 w = w :=
  Subtype.ext (Raw.oldAct_one A w.val)

@[simp] theorem oldAct_mul (x y : M) (w : Word A b) :
    oldAct A b (x * y) w = oldAct A b x (oldAct A b y w) :=
  Subtype.ext (Raw.oldAct_mul A x y w.val)

@[simp] theorem oldAct_cons (x : M) (s : S) (w : Word A b) (hw) :
    oldAct A b x (cons A b s w hw) = cons A b (A.act x s) w hw := rfl

@[simp] theorem old_inj (x y : M) : old A b x = old A b y ↔ x = y := by
  constructor
  · exact fun h => Raw.old.inj (congrArg Subtype.val h)
  · exact congrArg (old A b)

@[simp] theorem cons_inj (s t : S) (w v : Word A b) (hw hv) :
    cons A b s w hw = cons A b t v hv ↔ s = t ∧ w = v := by
  constructor
  · intro h
    obtain ⟨hs, hv⟩ := Raw.cons.inj (congrArg Subtype.val h)
    exact ⟨hs, Subtype.ext hv⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem oldAct_injective (x : M) : Function.Injective (oldAct A b x) :=
  fun _ _ h => Subtype.ext (Raw.oldAct_injective A x (congrArg Subtype.val h))

theorem headDiv_iff (x : M) (w : Word A b) :
    headDiv A b x w ↔ ∃ v : Word A b, oldAct A b x v = w := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (Raw.headDiv_iff A x w.val).1 h
    have hred : v.reduced A b := (Raw.reduced_oldAct A b x v).1 (hv ▸ w.property)
    exact ⟨⟨v, hred⟩, Subtype.ext hv⟩
  · rintro ⟨v, hv⟩
    exact (Raw.headDiv_iff A x w.val).2 ⟨v.val, congrArg Subtype.val hv⟩

@[simp] theorem headDiv_oldAct (x : M) (w : Word A b) :
    headDiv A b x (oldAct A b x w) := (headDiv_iff A b x _).2 ⟨w, rfl⟩

noncomputable def quotient (x : M) (w : Word A b) (h : headDiv A b x w) : Word A b :=
  ((headDiv_iff A b x w).1 h).choose

@[simp] theorem oldAct_quotient (x : M) (w : Word A b) (h : headDiv A b x w) :
    oldAct A b x (quotient A b x w h) = w := ((headDiv_iff A b x w).1 h).choose_spec

@[simp] theorem quotient_oldAct (x : M) (w : Word A b) (h) :
    quotient A b x (oldAct A b x w) h = w := by
  apply oldAct_injective A b x
  exact oldAct_quotient A b x _ h

/-- Prepending a letter performs its only possible front reduction. -/
noncomputable def letterAct (s : S) (w : Word A b) : Word A b := by
  classical
  exact if h : headDiv A b b w then oldAct A b (A.exit s) (quotient A b b w h)
    else cons A b s w h

theorem letterAct_of_headDiv (s : S) (w : Word A b) (h : headDiv A b b w) :
    letterAct A b s w = oldAct A b (A.exit s) (quotient A b b w h) := dite_eq_left h

theorem letterAct_of_not_headDiv (s : S) (w : Word A b) (h : ¬ headDiv A b b w) :
    letterAct A b s w = cons A b s w h := dite_eq_right h

@[simp] theorem letterAct_oldAct_b (s : S) (w : Word A b) :
    letterAct A b s (oldAct A b b w) = oldAct A b (A.exit s) w := by
  rw [letterAct_of_headDiv A b s _ (headDiv_oldAct A b b w), quotient_oldAct]

theorem oldAct_letterAct (x : M) (s : S) (w : Word A b) :
    oldAct A b x (letterAct A b s w) = letterAct A b (A.act x s) w := by
  classical
  by_cases h : headDiv A b b w
  · simp only [letterAct_of_headDiv A b _ _ h, A.exit_act, oldAct_mul]
  · simp only [letterAct_of_not_headDiv A b _ _ h, oldAct_cons]

theorem not_headDiv_exit_cons (s : S) (w : Word A b) (hw) :
    ¬ headDiv A b (A.exit s) (cons A b s w hw) := A.separated s

/-- The two branches of prepending have disjoint ranges by head separation. -/
theorem oldAct_exit_ne_cons (s : S) (v w : Word A b) (hw) :
    oldAct A b (A.exit s) v ≠ cons A b s w hw := by
  intro h
  exact not_headDiv_exit_cons A b s w hw (h ▸ headDiv_oldAct A b (A.exit s) v)

theorem letterAct_injective (s : S) : Function.Injective (letterAct A b s) := by
  classical
  intro w v he
  by_cases hw : headDiv A b b w <;> by_cases hv : headDiv A b b v
  · rw [letterAct_of_headDiv A b s w hw, letterAct_of_headDiv A b s v hv] at he
    have hq := oldAct_injective A b (A.exit s) he
    exact (oldAct_quotient A b b w hw).symm.trans
      ((congrArg (oldAct A b b) hq).trans (oldAct_quotient A b b v hv))
  · rw [letterAct_of_headDiv A b s w hw, letterAct_of_not_headDiv A b s v hv] at he
    exact (oldAct_exit_ne_cons A b s _ v hv he).elim
  · rw [letterAct_of_not_headDiv A b s w hw, letterAct_of_headDiv A b s v hv] at he
    exact (oldAct_exit_ne_cons A b s _ w hw he.symm).elim
  · rw [letterAct_of_not_headDiv A b s w hw, letterAct_of_not_headDiv A b s v hv] at he
    exact ((cons_inj A b _ _ _ _ _ _).1 he).2

end Word
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra
universe u v
open DiagramOrder
namespace Raw
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] (A : Alphabet M S) (b : M)

/-- Evaluate a word by its successive left multipliers. -/
noncomputable def eval : Raw M S → Word A b → Word A b
  | .old x, w => Word.oldAct A b x w
  | .cons s v, w => Word.letterAct A b s (eval v w)

theorem eval_oldAct (x : M) (v : Raw M S) (w : Word A b) :
    eval A b (Raw.oldAct A x v) w = Word.oldAct A b x (eval A b v w) := by
  cases v with
  | old y => exact Word.oldAct_mul A b x y w
  | cons s v => exact (Word.oldAct_letterAct A b x s (eval A b v w)).symm

theorem eval_injective (v : Raw M S) : Function.Injective (eval A b v) := by
  induction v with
  | old x => exact Word.oldAct_injective A b x
  | cons s v ih => exact (Word.letterAct_injective A b s).comp ih
end Raw

namespace Word
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] (A : Alphabet M S) (b : M)

theorem eval_oldAct (x : M) (v w : Word A b) :
    (oldAct A b x v).val.eval A b w = oldAct A b x (v.val.eval A b w) :=
  Raw.eval_oldAct A b x v.val w

theorem eval_letterAct (s : S) (v w : Word A b) :
    (letterAct A b s v).val.eval A b w = letterAct A b s (v.val.eval A b w) := by
  classical
  by_cases h : headDiv A b b v
  · rw [letterAct_of_headDiv A b s v h, eval_oldAct]
    conv_rhs => rw [← oldAct_quotient A b b v h]
    rw [eval_oldAct, letterAct_oldAct_b]
  · rw [letterAct_of_not_headDiv A b s v h]
    rfl

noncomputable def mul (v w : Word A b) : Word A b := v.val.eval A b w

@[simp] theorem old_mul (x : M) (w : Word A b) :
    mul A b (old A b x) w = oldAct A b x w := rfl

@[simp] theorem cons_mul (s : S) (v : Word A b) (hv) (w : Word A b) :
    mul A b (cons A b s v hv) w = letterAct A b s (mul A b v w) := rfl

theorem mul_assoc (x y z : Word A b) : mul A b (mul A b x y) z = mul A b x (mul A b y z) := by
  obtain ⟨x, hx⟩ := x
  induction x with
  | old x => exact eval_oldAct A b x y z
  | cons s v ih =>
    change (letterAct A b s (v.eval A b y)).val.eval A b z =
      letterAct A b s (v.eval A b (y.val.eval A b z))
    rw [eval_letterAct]
    exact congrArg (letterAct A b s) (ih hx.1)

theorem mul_one (w : Word A b) : mul A b w (old A b 1) = w := by
  obtain ⟨w, hw⟩ := w
  induction w with
  | old x =>
    apply Subtype.ext
    exact congrArg Raw.old (_root_.mul_one x)
  | cons s v ih =>
    change letterAct A b s (v.eval A b (old A b 1)) = _
    rw [show v.eval A b (old A b 1) = (⟨v, hw.1⟩ : Word A b) from ih hw.1]
    exact letterAct_of_not_headDiv A b s (⟨v, hw.1⟩ : Word A b) hw.2

noncomputable instance : Monoid (Word A b) where
  mul := mul A b
  one := old A b 1
  mul_assoc := mul_assoc A b
  one_mul := oldAct_one A b
  mul_one := mul_one A b

noncomputable instance : LeftCancelMonoid (Word A b) where
  mul_left_cancel x _ _ he := Raw.eval_injective A b x.val he

/-- A literal conservative homomorphism of old elements into probe normal forms. -/
noncomputable def oldHom : M →* Word A b where
  toFun := old A b
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem oldHom_apply (x : M) : oldHom A b x = old A b x := rfl

theorem oldHom_injective : Function.Injective (oldHom A b) :=
  fun _ _ h => (old_inj A b _ _).1 h

theorem old_mul_eq_old_iff (x y : M) (w : Word A b) :
    old A b x * w = old A b y ↔ ∃ z : M, w = old A b z ∧ x * z = y := by
  obtain ⟨w, hw⟩ := w
  cases w with
  | old z =>
    change old A b (x * z) = old A b y ↔ ∃ t, old A b z = old A b t ∧ x * t = y
    simp only [old_inj]
    exact ⟨fun h => ⟨z, rfl, h⟩, fun ⟨t, ht, h⟩ => ht ▸ h⟩
  | cons s v =>
    constructor
    · intro h
      have he := congrArg Subtype.val h
      cases he
    · rintro ⟨z, hz, _⟩
      have he := congrArg Subtype.val hz
      cases he

@[simp] theorem old_dvd_old_iff (x y : M) : old A b x ∣ old A b y ↔ x ∣ y := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨z, _, hz⟩ := (old_mul_eq_old_iff A b x y w).1 hw.symm
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨old A b z, congrArg (old A b) hz⟩

@[simp] theorem old_dvd_iff_headDiv (x : M) (w : Word A b) :
    old A b x ∣ w ↔ headDiv A b x w := by
  rw [headDiv_iff]
  exact exists_congr (fun _ => eq_comm)

/-- Having no old nontrivial unit prevents a letter from being consumed into `1`. -/
theorem exit_ne_one (s : S) : A.exit s ≠ 1 := by
  intro hs
  exact A.separated s ⟨s, hs ▸ A.one_act s⟩

theorem oldAct_exit_ne_one [IsConical M] (s : S) (w : Word A b) :
    oldAct A b (A.exit s) w ≠ 1 := by
  intro h
  obtain ⟨z, _, hz⟩ := (old_mul_eq_old_iff A b (A.exit s) 1 w).1 h
  exact exit_ne_one A s (IsConical.eq_one_of_mul_eq_one hz).1

theorem letterAct_ne_one [IsConical M] (s : S) (w : Word A b) :
    letterAct A b s w ≠ 1 := by
  classical
  by_cases h : headDiv A b b w
  · rw [letterAct_of_headDiv A b s w h]
    exact oldAct_exit_ne_one A b s _
  · rw [letterAct_of_not_headDiv A b s w h]
    intro he
    have hv := congrArg Subtype.val he
    cases hv

noncomputable instance [IsConical M] : IsConical (Word A b) where
  eq_one_of_mul_eq_one := by
    intro x y he
    obtain ⟨x, hx⟩ := x
    cases x with
    | old x =>
      obtain ⟨z, rfl, hz⟩ := (old_mul_eq_old_iff A b x 1 y).1 he
      obtain ⟨rfl, rfl⟩ := IsConical.eq_one_of_mul_eq_one hz
      exact ⟨rfl, rfl⟩
    | cons s v => exact (letterAct_ne_one A b s (v.eval A b y) he).elim

/-- The new generator represented by a letter, with terminal identity. -/
def generator [IsConical M] (hb : b ≠ 1) (s : S) : Word A b :=
  cons A b s (old A b 1) (by
    rintro ⟨z, hz⟩
    exact hb (IsConical.eq_one_of_mul_eq_one hz.symm).1)

theorem generator_mul [IsConical M] (hb : b ≠ 1) (s : S) (w : Word A b) :
    generator A b hb s * w = letterAct A b s w := by
  change letterAct A b s (oldAct A b 1 w) = _
  rw [oldAct_one]

theorem generator_mul_b [IsConical M] (hb : b ≠ 1) (s : S) :
    generator A b hb s * old A b b = old A b (A.exit s) := by
  rw [generator_mul]
  have h : old A b b = oldAct A b b (old A b 1) := by simp
  rw [h, letterAct_oldAct_b, oldAct_old, _root_.mul_one]

end Word
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra
universe u v w
open DiagramOrder
namespace Word
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] (A : Alphabet M S) (b : M)
  {N : Type w} [Monoid N] (f : M →* N) (q : S → N)

/-- Evaluation in any monoid satisfying the letter equivariance and exit
relations. This will give the presentation's universal property. -/
def evalHom : Raw M S → N
  | .old x => f x
  | .cons s v => q s * evalHom v

variable (heq : ∀ x s, q (A.act x s) = f x * q s)
  (hexit : ∀ s, q s * f b = f (A.exit s))

include heq in
theorem evalHom_oldAct (x : M) (v : Raw M S) :
    evalHom f q (v.oldAct A x) = f x * evalHom f q v := by
  cases v with
  | old y => exact f.map_mul x y
  | cons s v => simp only [Raw.oldAct, evalHom, heq, _root_.mul_assoc]

include heq hexit in
theorem evalHom_letterAct (s : S) (v : Word A b) :
    evalHom f q (letterAct A b s v).val = q s * evalHom f q v.val := by
  classical
  by_cases h : headDiv A b b v
  · rw [letterAct_of_headDiv A b s v h]
    change evalHom f q ((quotient A b b v h).val.oldAct A (A.exit s)) = _
    rw [evalHom_oldAct A f q heq]
    conv_rhs => rw [← oldAct_quotient A b b v h]
    change _ = q s * evalHom f q ((quotient A b b v h).val.oldAct A b)
    rw [evalHom_oldAct A f q heq, ← _root_.mul_assoc, hexit]
  · rw [letterAct_of_not_headDiv A b s v h]
    rfl

include heq hexit in
theorem evalHom_mul (v z : Word A b) :
    evalHom f q (v * z).val = evalHom f q v.val * evalHom f q z.val := by
  obtain ⟨v, hv⟩ := v
  induction v with
  | old x => exact evalHom_oldAct A f q heq x z.val
  | cons s v ih =>
    change evalHom f q (letterAct A b s (v.eval A b z)).val = _
    rw [evalHom_letterAct A b f q heq hexit]
    exact (congrArg (q s * ·) (ih hv.1)).trans (_root_.mul_assoc _ _ _).symm

/-- No extra relations were introduced by using irreducibles: any model
of the displayed reductions and old-action relation admits this homomorphism. -/
noncomputable def liftHom : Word A b →* N where
  toFun v := evalHom f q v.val
  map_one' := f.map_one
  map_mul' := evalHom_mul A b f q heq hexit

@[simp] theorem liftHom_old (x : M) :
    liftHom A b f q heq hexit (old A b x) = f x := rfl

@[simp] theorem liftHom_generator [IsConical M] (hb : b ≠ 1) (s : S) :
    liftHom A b f q heq hexit (generator A b hb s) = q s := by
  change q s * f 1 = q s
  rw [f.map_one, _root_.mul_one]

/-- A same-headed normal form is literally a generator times its suffix. -/
theorem generator_mul_of_not_headDiv [IsConical M] (hb : b ≠ 1)
    (s : S) (v : Word A b) (hv : ¬ headDiv A b b v) :
    generator A b hb s * v = cons A b s v hv :=
  (generator_mul A b hb s v).trans (letterAct_of_not_headDiv A b s v hv)

theorem hom_ext [IsConical M] (hb : b ≠ 1) (F G : Word A b →* N)
    (hOld : ∀ x, F (old A b x) = G (old A b x))
    (hNew : ∀ s, F (generator A b hb s) = G (generator A b hb s)) : F = G := by
  apply DFunLike.ext
  rintro ⟨v, hv⟩
  induction v with
  | old x => exact hOld x
  | cons s v ih =>
    change v.reduced A b ∧ ¬ v.headDiv A b at hv
    change F (cons A b s (⟨v, hv.1⟩ : Word A b) hv.2) =
      G (cons A b s (⟨v, hv.1⟩ : Word A b) hv.2)
    rw [← generator_mul_of_not_headDiv A b hb s (⟨v, hv.1⟩ : Word A b) hv.2]
    exact (F.map_mul _ _).trans ((congrArg₂ (· * ·) (hNew s) (ih hv.1)).trans
      (G.map_mul _ _).symm)

/-- Any product with a letter that is old must have gone through its exit. -/
theorem exit_dvd_of_letterAct_eq_old (s : S) (v : Word A b) {y : M}
    (hy : letterAct A b s v = old A b y) : A.exit s ∣ y := by
  classical
  by_cases h : headDiv A b b v
  · rw [letterAct_of_headDiv A b s v h] at hy
    obtain ⟨z, _, hz⟩ := (old_mul_eq_old_iff A b (A.exit s) y _).1 hy
    exact ⟨z, hz.symm⟩
  · rw [letterAct_of_not_headDiv A b s v h] at hy
    cases congrArg Subtype.val hy

/-- The gate of a single letter is its exit. The right factor `b` witnesses
attainment rather than a merely limiting old upper bound. -/
theorem generator_dvd_old_iff [IsConical M] (hb : b ≠ 1) (s : S) (y : M) :
    generator A b hb s ∣ old A b y ↔ A.exit s ∣ y := by
  constructor
  · rintro ⟨w, hw⟩
    rw [generator_mul] at hw
    exact exit_dvd_of_letterAct_eq_old A b s w hw.symm
  · rintro ⟨z, hz⟩
    refine ⟨old A b b * old A b z, ?_⟩
    rw [← _root_.mul_assoc, generator_mul_b]
    exact congrArg (old A b) hz
end Word

namespace Path
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M)

abbrev Extension := Word (P.alphabet he) b

/-- Preservation of the entire old-cone intersection, in every new word. -/
theorem old_cone_intersection (x y j : M)
    (hj : ∀ z : M, x ∣ z ∧ y ∣ z ↔ j ∣ z) (w : P.Extension he b) :
    Word.old (P.alphabet he) b x ∣ w ∧ Word.old (P.alphabet he) b y ∣ w ↔
      Word.old (P.alphabet he) b j ∣ w := by
  simp only [Word.old_dvd_iff_headDiv]
  obtain ⟨w, hw⟩ := w
  cases w with
  | old z => exact hj z
  | cons s w => exact P.inCone_intersection x y j hj s

/-- A new probe word cannot create a common multiple for two disjoint old
cones, even though it may itself divide an old element. -/
theorem common_multiple_reflection {x y : M} {w : P.Extension he b}
    (hx : Word.old (P.alphabet he) b x ∣ w) (hy : Word.old (P.alphabet he) b y ∣ w) :
    ∃ z : M, x ∣ z ∧ y ∣ z := by
  rw [Word.old_dvd_iff_headDiv] at hx hy
  obtain ⟨w, hw⟩ := w
  cases w with
  | old z => exact ⟨z, hx, hy⟩
  | cons s w => exact P.old_common_multiple_of_cones hx hy

variable (hb : b ≠ 1)

noncomputable def probe (i : ℕ) : P.Extension he b :=
  Word.generator (P.alphabet he) b hb (P.letter i 1)

/-- The prescribed old right factor sends every adjoined path probe to its
specified old exit. -/
theorem probe_mul_b (i : ℕ) :
    P.probe he b hb i * Word.old (P.alphabet he) b b =
      Word.old (P.alphabet he) b (P.terminal i * e) := by
  rw [probe, Word.generator_mul_b]
  congr 1
  simp only [alphabet, exit, target_letter, one_mul]

@[simp] theorem probe_zero_mul_b :
    P.probe he b hb 0 * Word.old (P.alphabet he) b b =
      Word.old (P.alphabet he) b (a * e) := by
  rw [probe_mul_b, terminal_zero]

/-- The transition relations are genuine equalities in these normal forms. -/
theorem probe_transition {i j : ℕ} (hij : i ≤ j) :
    Word.old (P.alphabet he) b (P.factor i j hij) * P.probe he b hb j =
      P.probe he b hb i := by
  apply Subtype.ext
  change Raw.cons (P.act (P.factor i j hij) (P.letter j 1)) (.old 1) =
    Raw.cons (P.letter i 1) (.old 1)
  rw [act_letter, mul_one, ← one_mul (P.factor i j hij), letter_transition]

/-- Precisely the old elements in the countable lower closure divide `p₀`. -/
theorem probe_old_profile (x : M) :
    Word.old (P.alphabet he) b x ∣ P.probe he b hb 0 ↔ ∃ i, x ∣ P.node i := by
  rw [Word.old_dvd_iff_headDiv]
  exact P.initial_profile x

/-- No right cancellation is needed to show the probe is not below `a`. -/
theorem probe_not_dvd_a :
    ¬ P.probe he b hb 0 ∣ Word.old (P.alphabet he) b a := by
  rw [probe, Word.generator_dvd_old_iff]
  change ¬ P.target (P.letter 0 1) * e ∣ a
  simp only [target_letter, terminal_zero, one_mul]
  rintro ⟨z, hz⟩
  have heq : e * z = 1 := by
    apply mul_left_cancel (a := a)
    simpa only [mul_assoc, mul_one] using hz.symm
  exact he (IsConical.eq_one_of_mul_eq_one heq).1

end Path

namespace Raw
variable {M S : Type u}

def code : Raw M S → List S × M
  | .old x => ([], x)
  | .cons s w => (s :: (code w).1, (code w).2)

theorem code_injective : Function.Injective (code : Raw M S → List S × M) := by
  intro w
  induction w with
  | old x =>
    intro v he
    cases v with
    | old y => exact congrArg Raw.old (Prod.mk.inj he).2
    | cons s v => cases (Prod.mk.inj he).1
  | cons s w ih =>
    intro v he
    cases v with
    | old y => cases (Prod.mk.inj he).1
    | cons t v =>
      obtain ⟨hst, htail⟩ := List.cons.inj (Prod.mk.inj he).1
      exact congrArg₂ Raw.cons hst (ih (Prod.ext htail (Prod.mk.inj he).2))

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) (hS : Cardinal.mk S ≤ μ) : Cardinal.mk (Raw M S) ≤ μ := by
  calc
    Cardinal.mk (Raw M S) ≤ Cardinal.mk (List S × M) := Cardinal.mk_le_of_injective code_injective
    _ = Cardinal.mk (List S) * Cardinal.mk M := by simp only [Cardinal.mk_prod, Cardinal.lift_id]
    _ ≤ max (max (Cardinal.mk (List S)) (Cardinal.mk M)) Cardinal.aleph0 :=
      Cardinal.mul_le_max _ _
    _ ≤ μ := max_le (max_le ((Cardinal.mk_list_le_max S).trans (max_le hω hS)) hM) hω
end Raw

namespace Path
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M)

/-- The probe extension also respects the infinite scheduling bound. -/
theorem extension_cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) : Cardinal.mk (P.Extension he b) ≤ μ :=
  (Cardinal.mk_le_of_injective Subtype.val_injective).trans
    (Raw.cardinal_le hω hM (P.letters_cardinal_le hω hM))
end Path
end PartitionConsistency.ProbeAlgebra

end OAI
