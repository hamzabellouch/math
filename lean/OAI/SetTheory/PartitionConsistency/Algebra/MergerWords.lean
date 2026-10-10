import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.DiagramOrder
import OAI.SetTheory.PartitionConsistency.Forcing.Diagrams
import OAI.SetTheory.PartitionConsistency.Algebra.Placements
import OAI.SetTheory.PartitionConsistency.Algebra.PlacementExtensions

namespace OAI

namespace PartitionConsistency
namespace DiagramOrder
lemma pair_lub_iff {α : Type*} [Preorder α] (a b j : α) :
    IsLUB {a, b} j ↔ ∀ z, a ≤ z ∧ b ≤ z ↔ j ≤ z := by
  simp only [isLUB_iff_le_iff, upperBounds, Set.mem_ofPred_eq,
    Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq]
  exact forall_congr' (fun _ => iff_comm)
namespace LeftDivOrder
lemma le_iff_dvd {M : Type*} [LeftCancelMonoid M] [IsConical M]
    (x y : LeftDivOrder M) : x ≤ y ↔ x ∣ y := by
  exact exists_congr (fun _ => eq_comm)
end LeftDivOrder
lemma exists_cone_join {M : Type*} [LeftCancelMonoid M] [IsConical M]
    (hM : HasConditionalJoins (LeftDivOrder M)) (x y a : M)
    (hx : x ∣ a) (hy : y ∣ a) :
    ∃ j : M, ∀ z : M, x ∣ z ∧ y ∣ z ↔ j ∣ z := by
  obtain ⟨j, hj⟩ := hM x y a ((LeftDivOrder.le_iff_dvd _ _).2 hx)
    ((LeftDivOrder.le_iff_dvd _ _).2 hy)
  refine ⟨j, ?_⟩
  intro z
  have hz := (pair_lub_iff (α := LeftDivOrder M) x y j).1 hj z
  rw [LeftDivOrder.le_iff_dvd (M := M) x z,
    LeftDivOrder.le_iff_dvd (M := M) y z,
    LeftDivOrder.le_iff_dvd (M := M) j z] at hz
  exact hz
/-- Cancellation for right divisibility in a left-cancellative monoid. -/
theorem left_mul_dvd_iff {M : Type*} [LeftCancelMonoid M] (a x y : M) :
    a * x ∣ a * y ↔ x ∣ y := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, mul_left_cancel (hz.trans (mul_assoc a x z))⟩
  · exact mul_dvd_mul_left a

/-- A nonempty inverse image of a principal right cone under left
multiplication is principal. Its initial element is the right quotient
of the conditional join. -/
theorem exists_cone_residual {M : Type*} [LeftCancelMonoid M]
    (hM : ∀ x y a : M, x ∣ a → y ∣ a → ∃ j : M, ∀ b : M, x ∣ b ∧ y ∣ b ↔ j ∣ b)
    (x a c : M) (hc : x ∣ a * c) :
    ∃ r : M, ∀ t : M, x ∣ a * t ↔ r ∣ t := by
  obtain ⟨s, hs⟩ := hM x a (a * c) hc (dvd_mul_right a c)
  obtain ⟨r, rfl⟩ := ((hs s).2 (dvd_refl s)).2
  refine ⟨r, fun t => ?_⟩
  calc
    x ∣ a * t ↔ x ∣ a * t ∧ a ∣ a * t :=
      ⟨fun h => ⟨h, dvd_mul_right _ _⟩, And.left⟩
    _ ↔ a * r ∣ a * t := hs _
    _ ↔ r ∣ t := left_mul_dvd_iff a r t

end DiagramOrder

namespace MergerAlgebra
universe u v

/-- A right action in which each orbit map is injective. This is the
property of the prescribed quotient of copies used in the merger normal
forms. It does not posit the existence of any monoid extension. -/
class RightFreeAction (M : Type u) (D : Type v) [Monoid M] where
  act : D → M → D
  act_one : ∀ d, act d 1 = d
  act_mul : ∀ d x y, act (act d x) y = act d (x * y)
  factor_injective : ∀ d, Function.Injective (act d)

namespace RightFreeAction
variable {M : Type u} {D : Type v} [Monoid M] [RightFreeAction M D]

/-- The right divisibility relation on a right monoid-set. -/
def Reaches (M : Type u) {D : Type v} [Monoid M] [RightFreeAction M D]
    (z w : D) : Prop := ∃ m : M, act z m = w

@[refl] theorem reaches_refl (z : D) : Reaches M z z := ⟨1, act_one z⟩

theorem reaches_trans {z w v : D} (hzw : Reaches M z w) (hwv : Reaches M w v) :
    Reaches M z v := by
  obtain ⟨m, hm⟩ := hzw
  obtain ⟨n, hn⟩ := hwv
  exact ⟨m * n, by rw [← act_mul, hm, hn]⟩

/-- Conditional joins expressed as exact intersections of right cones. -/
def HasConeJoins (M : Type u) (D : Type v) [Monoid M] [RightFreeAction M D] : Prop :=
  ∀ z w a : D, Reaches M z a → Reaches M w a →
    ∃ j : D, ∀ b : D, Reaches M z b ∧ Reaches M w b ↔ Reaches M j b

end RightFreeAction

/-- The literal normal forms `x z₁ ... zⱼ` of equation
`eq:mono-merger-forms`; words with no new letter are the old monoid. -/
inductive Word (M : Type u) (D : Type v) where
  | old : M → Word M D
  | snoc : Word M D → D → Word M D

namespace Word
variable {M : Type u} {D : Type v} [Monoid M] [RightFreeAction M D]

/-- Multiplication on the right by an old element acts only on the last
new letter (or on the old coefficient, if no new letter is present). -/
def act : Word M D → M → Word M D
  | old x, y => old (x * y)
  | snoc w z, y => snoc w (RightFreeAction.act z y)

@[simp] theorem act_one (w : Word M D) : act w 1 = w := by
  cases w <;> simp [act, RightFreeAction.act_one]

@[simp] theorem act_mul (w : Word M D) (x y : M) :
    act (act w x) y = act w (x * y) := by
  cases w <;> simp [act, mul_assoc, RightFreeAction.act_mul]

/-- Concatenation, absorbing the leading old coefficient of the second
normal form into the last letter of the first. -/
def product (x : Word M D) : Word M D → Word M D
  | old y => act x y
  | snoc y z => snoc (product x y) z

@[simp] theorem product_act (x y : Word M D) (m : M) :
    product x (act y m) = act (product x y) m := by
  cases y with
  | old n => exact (act_mul x n m).symm
  | snoc w d => rfl

theorem product_assoc (x y z : Word M D) :
    product (product x y) z = product x (product y z) := by
  induction z with
  | old m => exact (product_act x y m).symm
  | snoc z d ih => exact congrArg (fun w => snoc w d) ih

theorem old_one_product (w : Word M D) : product (old 1) w = w := by
  induction w with
  | old x => simp [product, act]
  | snoc w z ih => simp [product, ih]

instance : Monoid (Word M D) where
  mul := product
  one := old 1
  mul_assoc := product_assoc
  one_mul := old_one_product
  mul_one := act_one

@[simp] theorem mul_old (w : Word M D) (x : M) : w * old x = act w x := rfl
@[simp] theorem mul_snoc (w y : Word M D) (z : D) :
    w * snoc y z = snoc (w * y) z := rfl
@[simp] theorem old_mul_old (x y : M) :
    (old x : Word M D) * old y = old (x * y) := rfl
@[simp] theorem snoc_mul_old (w : Word M D) (z : D) (y : M) :
    snoc w z * old y = snoc w (RightFreeAction.act z y) := rfl

/-- Number of new letters, used to distinguish old from genuinely new words. -/
def length : Word M D → ℕ
  | old _ => 0
  | snoc w _ => length w + 1

omit [Monoid M] [RightFreeAction M D] in
@[simp] theorem length_old (x : M) : length (old x : Word M D) = 0 := rfl
omit [Monoid M] [RightFreeAction M D] in
@[simp] theorem length_snoc (w : Word M D) (z : D) :
    length (snoc w z) = length w + 1 := rfl
@[simp] theorem length_act (w : Word M D) (x : M) : length (act w x) = length w := by
  cases w <;> rfl

@[simp] theorem length_mul (x y : Word M D) : length (x * y) = length x + length y := by
  induction y with
  | old m => simp
  | snoc y d ih => simp [ih, Nat.add_assoc]

omit [Monoid M] [RightFreeAction M D] in
theorem length_zero_iff (w : Word M D) : length w = 0 ↔ ∃ m, w = old m := by
  cases w <;> simp

section Cancellation
variable [IsLeftCancelMul M]

theorem act_injective (w : Word M D) : Function.Injective (act w) := by
  cases w with
  | old x =>
      intro y z he
      exact mul_left_cancel (Word.old.inj he)
  | snoc w d =>
      intro y z he
      exact RightFreeAction.factor_injective d (Word.snoc.inj he).2

/-- Left cancellation is proved from the displayed normal forms. Right
cancellation is neither used nor asserted. -/
theorem product_left_cancel (x : Word M D) {y z : Word M D} (h : x * y = x * z) :
    y = z := by
  induction y generalizing z with
  | old m =>
      cases z with
      | old n => exact congrArg old (act_injective x h)
      | snoc z d =>
          have hl := congrArg length h
          simp only [length_mul, length_old, length_snoc] at hl
          omega
  | snoc y d ih =>
      cases z with
      | old n =>
          have hl := congrArg length h
          simp only [length_mul, length_old, length_snoc] at hl
          omega
      | snoc z e =>
          obtain ⟨h₁, h₂⟩ := Word.snoc.inj h
          exact congrArg₂ snoc (ih h₁) h₂

instance : LeftCancelMonoid (Word M D) where
  mul_left_cancel x _ _ := product_left_cancel x

end Cancellation

/-- Letter count prevents a new word from acquiring an old right multiple.
It also identifies the old right factor, rather than just reflecting order. -/
theorem factors_of_old {x y : Word M D} {a : M} (h : x * y = old a) :
    ∃ b c : M, x = old b ∧ y = old c ∧ b * c = a := by
  have hl := congrArg length h
  simp only [length_mul, length_old, Nat.add_eq_zero_iff] at hl
  obtain ⟨b, rfl⟩ := (length_zero_iff x).1 hl.1
  obtain ⟨c, rfl⟩ := (length_zero_iff y).1 hl.2
  exact ⟨b, c, rfl, rfl, Word.old.inj h⟩

instance [DiagramOrder.IsConical M] : DiagramOrder.IsConical (Word M D) where
  eq_one_of_mul_eq_one h := by
    obtain ⟨b, c, rfl, rfl, hbc⟩ := factors_of_old h
    obtain ⟨rfl, rfl⟩ := DiagramOrder.IsConical.eq_one_of_mul_eq_one hbc
    exact ⟨rfl, rfl⟩

/-- The old monoid embeds by words with no new letters. -/
def oldHom : M →* Word M D where
  toFun := old
  map_one' := rfl
  map_mul' _ _ := rfl

theorem oldHom_injective : Function.Injective (oldHom : M →* Word M D) := fun _ _ h => Word.old.inj h

/-- The leading old coefficient of the normal form. -/
def leading : Word M D → M
  | old x => x
  | snoc w _ => leading w

omit [Monoid M] [RightFreeAction M D] in
@[simp] theorem leading_old (x : M) : leading (old x : Word M D) = x := rfl
omit [Monoid M] [RightFreeAction M D] in
@[simp] theorem leading_snoc (w : Word M D) (z : D) :
    leading (snoc w z) = leading w := rfl

@[simp] theorem leading_old_mul (x : M) (w : Word M D) :
    leading (old x * w) = x * leading w := by
  induction w with
  | old m => rfl
  | snoc w d ih => exact ih

/-- Old divisors are read solely from the old leading coefficient. -/
theorem old_dvd_iff (x : M) (w : Word M D) :
    old x ∣ w ↔ x ∣ leading w := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨leading z, leading_old_mul x z⟩
  · intro h
    induction w with
    | old y =>
        obtain ⟨a, ha⟩ := h
        exact ⟨old a, congrArg old ha⟩
    | snoc w d ih =>
        obtain ⟨q, hq⟩ := ih h
        exact ⟨snoc q d, congrArg (fun w => snoc w d) hq⟩

/-- Comparisons and common-right-multiple calculations on old entries are
unchanged in the extension, including the absence of a common multiple. -/
theorem old_common_multiple_iff (x y : M) :
    (∃ w : Word M D, old x ∣ w ∧ old y ∣ w) ↔ ∃ a : M, x ∣ a ∧ y ∣ a := by
  constructor
  · rintro ⟨w, hx, hy⟩
    exact ⟨leading w, (old_dvd_iff x w).1 hx, (old_dvd_iff y w).1 hy⟩
  · rintro ⟨a, hx, hy⟩
    exact ⟨old a, (old_dvd_iff x (old a)).2 hx, (old_dvd_iff y (old a)).2 hy⟩

/-- The entire right-cone equation for any old conditional join is preserved,
not just comparisons among old elements. -/
theorem preserve_old_cone_intersection (x y j : M)
    (hj : ∀ a : M, x ∣ a ∧ y ∣ a ↔ j ∣ a) (w : Word M D) :
    old x ∣ w ∧ old y ∣ w ↔ old j ∣ w := by
  simpa only [old_dvd_iff] using hj (leading w)

/-- Dividing a normal form with one more letter means either dividing its
prefix, or having precisely that prefix and advancing the last new letter. -/
theorem dvd_snoc_iff (x w : Word M D) (d : D) :
    x ∣ snoc w d ↔ x ∣ w ∨ ∃ z, x = snoc w z ∧ RightFreeAction.Reaches M z d := by
  constructor
  · rintro ⟨q, hq⟩
    cases q with
    | old m =>
        cases x with
        | old a => cases hq
        | snoc v z =>
            obtain ⟨hw, hd⟩ := Word.snoc.inj hq
            exact Or.inr ⟨z, congrArg (fun v => snoc v z) hw.symm, m, hd.symm⟩
    | snoc q z => exact Or.inl ⟨q, (Word.snoc.inj hq).1⟩
  · rintro (⟨q, hq⟩ | ⟨z, rfl, m, hm⟩)
    · exact ⟨snoc q d, congrArg (fun v => snoc v d) hq⟩
    · exact ⟨old m, congrArg (snoc w) hm.symm⟩

theorem length_le_of_dvd {x y : Word M D} (h : x ∣ y) : length x ≤ length y := by
  obtain ⟨q, rfl⟩ := h
  simp only [length_mul]
  omega

theorem snoc_not_dvd_prefix (w : Word M D) (z : D) : ¬ snoc w z ∣ w := by
  intro h
  have hl := length_le_of_dvd h
  simp only [length_snoc] at hl
  omega

theorem snoc_not_dvd_old (w : Word M D) (z : D) (m : M) : ¬ snoc w z ∣ old m := by
  intro h
  have hl := length_le_of_dvd h
  simp only [length_snoc, length_old] at hl
  omega

theorem snoc_dvd_snoc_iff (w v : Word M D) (z d : D) :
    snoc w z ∣ snoc v d ↔
      snoc w z ∣ v ∨ w = v ∧ RightFreeAction.Reaches M z d := by
  rw [dvd_snoc_iff]
  constructor
  · rintro (h | ⟨e, he, hea⟩)
    · exact Or.inl h
    · obtain ⟨rfl, rfl⟩ := Word.snoc.inj he
      exact Or.inr ⟨rfl, hea⟩
  · rintro (h | ⟨rfl, hz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z, rfl, hz⟩

/-- With a fixed prefix, the intersection of two word cones is exactly
controlled by the intersection of the final-letter cones in the right set. -/
theorem snoc_cone_intersection (w : Word M D) (z t j : D)
    (hj : ∀ d : D, RightFreeAction.Reaches M z d ∧ RightFreeAction.Reaches M t d ↔
      RightFreeAction.Reaches M j d) (a : Word M D) :
    snoc w z ∣ a ∧ snoc w t ∣ a ↔ snoc w j ∣ a := by
  induction a with
  | old m => simp only [snoc_not_dvd_old, false_and]
  | snoc a d ih =>
      simp only [snoc_dvd_snoc_iff]
      by_cases hw : w = a
      · subst a
        simp only [snoc_not_dvd_prefix, true_and, false_or, hj]
      · simpa only [hw, false_and, or_false] using ih

/-- Conditional joins for all normal forms, not only for translated copies.
The induction is on the normal form of a common upper bound. -/
theorem exists_cone_join
    (hM : ∀ x y a : M, x ∣ a → y ∣ a → ∃ j : M, ∀ b : M, x ∣ b ∧ y ∣ b ↔ j ∣ b)
    (hD : RightFreeAction.HasConeJoins M D) (x y a : Word M D)
    (hx : x ∣ a) (hy : y ∣ a) :
    ∃ j : Word M D, ∀ b : Word M D, x ∣ b ∧ y ∣ b ↔ j ∣ b := by
  induction a generalizing x y with
  | old m =>
      obtain ⟨qx, hqx⟩ := hx
      obtain ⟨qy, hqy⟩ := hy
      obtain ⟨r, s, rfl, rfl, hxm⟩ := factors_of_old hqx.symm
      obtain ⟨t, u, rfl, rfl, hym⟩ := factors_of_old hqy.symm
      obtain ⟨j, hj⟩ := hM r t m ⟨s, hxm.symm⟩ ⟨u, hym.symm⟩
      exact ⟨old j, preserve_old_cone_intersection r t j hj⟩
  | snoc a d ih =>
      rcases (dvd_snoc_iff x a d).1 hx with hx | ⟨z, rfl, hz⟩
      · rcases (dvd_snoc_iff y a d).1 hy with hy | ⟨t, rfl, ht⟩
        · exact ih x y hx hy
        · have hxy : x ∣ snoc a t := (dvd_snoc_iff x a t).2 (Or.inl hx)
          exact ⟨snoc a t, fun _ => ⟨And.right, fun h => ⟨hxy.trans h, h⟩⟩⟩
      · rcases (dvd_snoc_iff y a d).1 hy with hy | ⟨t, rfl, ht⟩
        · have hyx : y ∣ snoc a z := (dvd_snoc_iff y a z).2 (Or.inl hy)
          exact ⟨snoc a z, fun _ => ⟨And.left, fun h => ⟨h, hyx.trans h⟩⟩⟩
        · obtain ⟨j, hj⟩ := hD z t d hz ht
          exact ⟨snoc a j, snoc_cone_intersection a z t j hj⟩

end Word
end MergerAlgebra

namespace DiagramForcing.OverlapPrescription
universe u
variable {M : Type u} [LeftCancelMonoid M] {n : ℕ}

/-- Right multiplication respects the pair identifications themselves. No
extra transitive closure is taken. -/
theorem rel_mul (P : OverlapPrescription M n) {z w : Fin n × M}
    (h : P.Rel z w) (m : M) :
    P.Rel (z.1, z.2 * m) (w.1, w.2 * m) := by
  classical
  obtain ⟨i, x⟩ := z
  obtain ⟨j, y⟩ := w
  by_cases hij : i = j
  · subst j
    simp only [rel_same_copy] at h ⊢
    exact congrArg (· * m) h
  · simp only [Rel, hij, ↓reduceIte] at h ⊢
    cases ho : P.start i j with
    | none => simp only [ho] at h
    | some ab =>
        obtain ⟨a, b⟩ := ab
        rw [ho] at h
        obtain ⟨t, rfl, rfl⟩ := h
        exact ⟨t * m, mul_assoc _ _ _, mul_assoc _ _ _⟩

/-- The quotient of the finitely many prescribed copies. Validity, rather
than an equivalence closure, provides its setoid. -/
def copySetoid (P : OverlapPrescription M n) (hP : P.Valid) : Setoid (Fin n × M) :=
  ⟨P.Rel, hP⟩

def Copies (P : OverlapPrescription M n) (hP : P.Valid) := Quotient (P.copySetoid hP)

def copy (P : OverlapPrescription M n) (hP : P.Valid) (i : Fin n) (x : M) : P.Copies hP :=
  Quotient.mk (P.copySetoid hP) (i, x)

@[simp] theorem copy_eq_iff (P : OverlapPrescription M n) (hP : P.Valid)
    (i j : Fin n) (x y : M) :
    P.copy hP i x = P.copy hP j y ↔ P.Rel (i, x) (j, y) := Quotient.eq

theorem copy_injective (P : OverlapPrescription M n) (hP : P.Valid) (i : Fin n) :
    Function.Injective (P.copy hP i) := by
  intro x y he
  exact (P.rel_same_copy i x y).1 ((P.copy_eq_iff hP i i x y).1 he)

def copiesAct (P : OverlapPrescription M n) (hP : P.Valid) (z : P.Copies hP) (m : M) :
    P.Copies hP :=
  Quotient.map (fun z : Fin n × M => (z.1, z.2 * m)) (fun _ _ h => P.rel_mul h m) z

@[simp] theorem copiesAct_copy (P : OverlapPrescription M n) (hP : P.Valid)
    (i : Fin n) (x m : M) :
    P.copiesAct hP (P.copy hP i x) m = P.copy hP i (x * m) := rfl

/-- The injective orbit maps in the prescribed quotient follow from left
cancellation within a single original copy. -/
instance copiesRightFreeAction (P : OverlapPrescription M n) (hP : P.Valid) :
    MergerAlgebra.RightFreeAction M (P.Copies hP) where
  act := P.copiesAct hP
  act_one := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
        change P.copy hP z.1 (z.2 * 1) = P.copy hP z.1 z.2
        rw [mul_one]
  act_mul := by
    intro z x y
    induction z using Quotient.inductionOn with
    | h z =>
        change P.copy hP z.1 ((z.2 * x) * y) = P.copy hP z.1 (z.2 * (x * y))
        rw [mul_assoc]
  factor_injective := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
        intro x y he
        exact mul_left_cancel (P.copy_injective hP z.1 he)

open MergerAlgebra.RightFreeAction

@[simp] theorem reaches_copy_iff (P : OverlapPrescription M n) (hP : P.Valid)
    (i : Fin n) (x : M) (z : P.Copies hP) :
    Reaches M (P.copy hP i x) z ↔ ∃ m, P.copy hP i (x * m) = z := Iff.rfl

@[simp] theorem reaches_same_copy_iff (P : OverlapPrescription M n) (hP : P.Valid)
    (i : Fin n) (x y : M) :
    Reaches M (P.copy hP i x) (P.copy hP i y) ↔ x ∣ y := by
  rw [reaches_copy_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, (P.copy_injective hP i hm).symm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, rfl⟩

theorem same_copy_cone_intersection (P : OverlapPrescription M n) (hP : P.Valid)
    (i : Fin n) (x y j : M) (hj : ∀ a : M, x ∣ a ∧ y ∣ a ↔ j ∣ a)
    (z : P.Copies hP) :
    Reaches M (P.copy hP i x) z ∧ Reaches M (P.copy hP i y) z ↔
      Reaches M (P.copy hP i j) z := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    change P.copy hP i (x * a) = z at ha
    change P.copy hP i (y * b) = z at hb
    have hxy : x * a = y * b := P.copy_injective hP i (ha.trans hb.symm)
    obtain ⟨c, hc⟩ := (hj (x * a)).1 ⟨dvd_mul_right _ _, b, hxy⟩
    exact ⟨c, by change P.copy hP i (j * c) = z; rw [← hc, ha]⟩
  · intro h
    have hu := (hj j).2 (dvd_refl j)
    exact ⟨reaches_trans ((P.reaches_same_copy_iff hP i x j).2 hu.1) h,
      reaches_trans ((P.reaches_same_copy_iff hP i y j).2 hu.2) h⟩

/-- Intersections from different copies must pass through exactly the
specified overlap: validity ensures that the quotient adds no other equality. -/
theorem overlap_cone_intersection (P : OverlapPrescription M n) (hP : P.Valid)
    {i j : Fin n} (hij : i ≠ j) {a b : M} (hab : P.start i j = some (a, b))
    (x y : M) (z : P.Copies hP) :
    Reaches M (P.copy hP i x) z ∧ Reaches M (P.copy hP j y) z ↔
      ∃ t : M, x ∣ a * t ∧ y ∣ b * t ∧ z = P.copy hP i (a * t) := by
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨k, hk⟩⟩
    change P.copy hP i (x * m) = z at hm
    change P.copy hP j (y * k) = z at hk
    have he := (P.copy_eq_iff hP i j (x * m) (y * k)).1 (hm.trans hk.symm)
    simp only [Rel, hij, ↓reduceIte, hab] at he
    obtain ⟨t, ht, ht'⟩ := he
    exact ⟨t, ⟨m, ht.symm⟩, ⟨k, ht'.symm⟩, hm.symm.trans (congrArg _ ht)⟩
  · rintro ⟨t, ⟨m, hm⟩, ⟨k, hk⟩, rfl⟩
    have he : P.copy hP i (a * t) = P.copy hP j (b * t) := by
      apply (P.copy_eq_iff hP i j _ _).2
      simp only [Rel, hij, ↓reduceIte, hab]
      exact ⟨t, rfl, rfl⟩
    exact ⟨⟨m, congrArg (P.copy hP i) hm.symm⟩,
      ⟨k, (congrArg (P.copy hP j) hk.symm).trans he.symm⟩⟩

/-- Conditional joins in the actual prescribed quotient of copies.
The sequential joins and their right quotients are constructed using only
old conditional joins; failing any one of them means there was no common
upper bound in the first place. -/
theorem copies_hasConeJoins (P : OverlapPrescription M n) (hP : P.Valid)
    (hM : ∀ x y a : M, x ∣ a → y ∣ a → ∃ j : M, ∀ b : M, x ∣ b ∧ y ∣ b ↔ j ∣ b) :
    HasConeJoins M (P.Copies hP) := by
  classical
  intro z w c hz hw
  obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep z
  obtain ⟨⟨j, y⟩, rfl⟩ := Quotient.exists_rep w
  change Reaches M (P.copy hP i x) c at hz
  change Reaches M (P.copy hP j y) c at hw
  by_cases hij : i = j
  · subst j
    obtain ⟨u, hu⟩ := (P.reaches_copy_iff hP i x c).1 hz
    obtain ⟨v, hv⟩ := (P.reaches_copy_iff hP i y c).1 hw
    have hxy : x * u = y * v := P.copy_injective hP i (hu.trans hv.symm)
    obtain ⟨k, hk⟩ := hM x y (x * u) (dvd_mul_right _ _) ⟨v, hxy⟩
    exact ⟨P.copy hP i k, P.same_copy_cone_intersection hP i x y k hk⟩
  · obtain ⟨u, hu⟩ := (P.reaches_copy_iff hP i x c).1 hz
    obtain ⟨v, hv⟩ := (P.reaches_copy_iff hP j y c).1 hw
    have he := (P.copy_eq_iff hP i j (x * u) (y * v)).1 (hu.trans hv.symm)
    simp only [Rel, hij, ↓reduceIte] at he
    cases ho : P.start i j with
    | none => simp only [ho] at he
    | some ab =>
        obtain ⟨a, b⟩ := ab
        rw [ho] at he
        obtain ⟨t₀, hxt, hyt⟩ := he
        obtain ⟨r, hr⟩ := DiagramOrder.exists_cone_residual hM x a t₀ ⟨u, hxt.symm⟩
        obtain ⟨s, hs⟩ := DiagramOrder.exists_cone_residual hM y b t₀ ⟨v, hyt.symm⟩
        obtain ⟨k, hk⟩ := hM r s t₀ ((hr t₀).1 ⟨u, hxt.symm⟩)
          ((hs t₀).1 ⟨v, hyt.symm⟩)
        have hcoeff : ∀ t, x ∣ a * t ∧ y ∣ b * t ↔ k ∣ t := fun t => by
          rw [hr t, hs t, hk t]
        refine ⟨P.copy hP i (a * k), fun z => ?_⟩
        change Reaches M (P.copy hP i x) z ∧ Reaches M (P.copy hP j y) z ↔
          Reaches M (P.copy hP i (a * k)) z
        rw [P.overlap_cone_intersection hP hij ho]
        constructor
        · rintro ⟨t, hxt, hyt, rfl⟩
          obtain ⟨m, rfl⟩ := (hcoeff t).1 ⟨hxt, hyt⟩
          exact ⟨m, congrArg (P.copy hP i) (mul_assoc a k m)⟩
        · rintro ⟨m, hm⟩
          change P.copy hP i ((a * k) * m) = z at hm
          have ht := (hcoeff (k * m)).2 (dvd_mul_right _ _)
          exact ⟨k * m, ht.1, ht.2, hm.symm.trans (congrArg _ (mul_assoc a k m))⟩

/-- The extension is constructed, not postulated: its elements are the
normal forms over the actual prescribed quotient. -/
abbrev Merger (P : OverlapPrescription M n) (hP : P.Valid) :=
  MergerAlgebra.Word M (P.Copies hP)

/-- The new roots which merge the original copies. -/
def root (P : OverlapPrescription M n) (hP : P.Valid) (i : Fin n) : P.Merger hP :=
  .snoc (.old 1) (P.copy hP i 1)

@[simp] theorem root_mul_old (P : OverlapPrescription M n) (hP : P.Valid)
    (i : Fin n) (x : M) :
    P.root hP i * .old x = .snoc (.old 1) (P.copy hP i x) := by
  change MergerAlgebra.Word.snoc (.old 1) (P.copy hP i (1 * x)) = _
  rw [one_mul]

/-- Exact realization of the given valid overlap prescription by left
translations. The right-hand side is the original pair relation, not its
transitive closure; no extra overlap is introduced. -/
theorem root_mul_eq_iff (P : OverlapPrescription M n) (hP : P.Valid)
    (z w : Fin n × M) :
    P.root hP z.1 * .old z.2 = P.root hP w.1 * .old w.2 ↔ P.Rel z w := by
  simp only [root_mul_old, MergerAlgebra.Word.snoc.injEq, true_and, copy_eq_iff]

/-- New roots are genuinely new elements, even if an overlap identifies
two of them with one another. -/
theorem root_not_old (P : OverlapPrescription M n) (hP : P.Valid)
    (i : Fin n) (x : M) : P.root hP i ≠ .old x := by
  simp [root]

/-- All conditional joins in the constructed finite-copy merger. -/
theorem merger_hasConditionalJoins [DiagramOrder.IsConical M]
    (P : OverlapPrescription M n) (hP : P.Valid)
    (hM : DiagramOrder.HasConditionalJoins (DiagramOrder.LeftDivOrder M)) :
    DiagramOrder.HasConditionalJoins (DiagramOrder.LeftDivOrder (P.Merger hP)) := by
  intro x y a hx hy
  have hc := DiagramOrder.exists_cone_join hM
  obtain ⟨j, hj⟩ := MergerAlgebra.Word.exists_cone_join hc
    (P.copies_hasConeJoins hP hc) x y a
    ((DiagramOrder.LeftDivOrder.le_iff_dvd (M := P.Merger hP) x a).1 hx)
    ((DiagramOrder.LeftDivOrder.le_iff_dvd (M := P.Merger hP) y a).1 hy)
  refine ⟨j, (DiagramOrder.pair_lub_iff (α := DiagramOrder.LeftDivOrder (P.Merger hP)) x y j).2 (fun z => ?_)⟩
  change (∃ q, x * q = z) ∧ (∃ q, y * q = z) ↔ ∃ q, j * q = z
  constructor
  · rintro ⟨⟨q, hq⟩, ⟨r, hr⟩⟩
    obtain ⟨s, hs⟩ := (hj z).1 ⟨⟨q, hq.symm⟩, ⟨r, hr.symm⟩⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    obtain ⟨⟨q, hq⟩, ⟨r, hr⟩⟩ := (hj z).2 ⟨s, hs.symm⟩
    exact ⟨⟨q, hq.symm⟩, ⟨r, hr.symm⟩⟩

end DiagramForcing.OverlapPrescription
end PartitionConsistency

namespace PartitionConsistency.MergerAlgebra.Word
universe u
variable {M D : Type u}

/-- Finite coding of a normal form; only the existing coefficient and
finitely many quotient letters are needed. -/
def letters : Word M D → List D
  | old _ => []
  | snoc w z => z :: letters w

/-- The normal-form encoding is injective, so no presentation-sized
collection beyond finite strings is required. -/
theorem code_injective : Function.Injective (fun w : Word M D => (leading w, letters w)) := by
  intro w
  induction w with
  | old m =>
      intro v hv
      cases v with
      | old n => exact congrArg old (Prod.mk.inj hv).1
      | snoc v z =>
          have he := (Prod.mk.inj hv).2
          simp [letters] at he
  | snoc w z ih =>
      intro v hv
      cases v with
      | old n =>
          have he := (Prod.mk.inj hv).2
          simp [letters] at he
      | snoc v d =>
          have hzv := List.cons.inj (Prod.mk.inj hv).2
          exact congrArg₂ snoc (ih (Prod.ext (Prod.mk.inj hv).1 hzv.2)) hzv.1

/-- The scheduling bound for the normal forms. -/
theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) (hD : Cardinal.mk D ≤ μ) :
    Cardinal.mk (Word M D) ≤ μ := by
  calc
    Cardinal.mk (Word M D) ≤ Cardinal.mk (M × List D) :=
      Cardinal.mk_le_of_injective code_injective
    _ = Cardinal.mk M * Cardinal.mk (List D) := by simp only [Cardinal.mk_prod, Cardinal.lift_id]
    _ ≤ max (max (Cardinal.mk M) (Cardinal.mk (List D))) Cardinal.aleph0 :=
      Cardinal.mul_le_max _ _
    _ ≤ μ := max_le (max_le hM ((Cardinal.mk_list_le_max D).trans (max_le hω hD))) hω

end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u
variable {M : Type u} [LeftCancelMonoid M] {n : ℕ}

/-- A finite-copy merger preserves the source's infinite cardinal bound. -/
theorem merger_cardinal_le (P : OverlapPrescription M n) (hP : P.Valid)
    {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ) (hM : Cardinal.mk M ≤ μ) :
    Cardinal.mk (P.Merger hP) ≤ μ := by
  apply MergerAlgebra.Word.cardinal_le hω hM
  calc
    Cardinal.mk (P.Copies hP) ≤ Cardinal.mk (Fin n × M) := Cardinal.mk_quotient_le
    _ = n * Cardinal.mk M := by simp [Cardinal.mk_prod]
    _ ≤ max (max (n : Cardinal) (Cardinal.mk M)) Cardinal.aleph0 := Cardinal.mul_le_max _ _
    _ ≤ μ := max_le (max_le ((Cardinal.natCast_lt_aleph0 (n := n)).le.trans hω) hM) hω

end PartitionConsistency.DiagramForcing.OverlapPrescription

end OAI
