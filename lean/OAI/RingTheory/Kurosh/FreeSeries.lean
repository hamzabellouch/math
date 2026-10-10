import Mathlib

namespace OAI

/-! Noncommutative formal series and their ring operations. -/

namespace KuroshConstruction

@[ext] structure FreeSeries (A : Type*) where
  coeff : List (Fin 2) → A

namespace FreeSeries

variable {A : Type*}

theorem coeff_injective : Function.Injective (coeff : FreeSeries A → List (Fin 2) → A) :=
  fun _ _ h => FreeSeries.ext h

instance [Zero A] : Zero (FreeSeries A) := ⟨⟨0⟩⟩

instance [Add A] : Add (FreeSeries A) := ⟨fun f g => ⟨f.coeff + g.coeff⟩⟩

instance [Neg A] : Neg (FreeSeries A) := ⟨fun f => ⟨-f.coeff⟩⟩

instance [Sub A] : Sub (FreeSeries A) := ⟨fun f g => ⟨f.coeff - g.coeff⟩⟩

instance [SMul ℕ A] : SMul ℕ (FreeSeries A) := ⟨fun n f => ⟨n • f.coeff⟩⟩

instance [SMul ℤ A] : SMul ℤ (FreeSeries A) := ⟨fun n f => ⟨n • f.coeff⟩⟩

@[simp] theorem coeff_zero [Zero A] (w) : (0 : FreeSeries A).coeff w = 0 := rfl

@[simp] theorem coeff_add [Add A] (f g : FreeSeries A) (w) :
    (f + g).coeff w = f.coeff w + g.coeff w := rfl

@[simp] theorem coeff_neg [Neg A] (f : FreeSeries A) (w) :
    (-f).coeff w = -f.coeff w := rfl

@[simp] theorem coeff_sub [Sub A] (f g : FreeSeries A) (w) :
    (f - g).coeff w = f.coeff w - g.coeff w := rfl

instance [AddCommGroup A] : AddCommGroup (FreeSeries A) :=
  coeff_injective.addCommGroup coeff rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

def productCoeff [Add A] [Mul A] (f g : List (Fin 2) → A) : List (Fin 2) → A
  | [] => f [] * g []
  | a :: w => f [] * g (a :: w) + productCoeff (fun v => f (a :: v)) g w

instance [Add A] [Mul A] : Mul (FreeSeries A) :=
  ⟨fun f g => ⟨productCoeff f.coeff g.coeff⟩⟩

@[simp] theorem coeff_mul_nil [Add A] [Mul A] (f g : FreeSeries A) :
    (f * g).coeff [] = f.coeff [] * g.coeff [] := rfl

@[simp] theorem coeff_mul_cons [Add A] [Mul A] (f g : FreeSeries A) (a w) :
    (f * g).coeff (a :: w) = f.coeff [] * g.coeff (a :: w) +
      productCoeff (fun v => f.coeff (a :: v)) g.coeff w := rfl

section Ring

variable [Ring A]

lemma productCoeff_zero_left (g : List (Fin 2) → A) (w) :
    productCoeff (0 : List (Fin 2) → A) g w = 0 := by
  induction w with
  | nil => simp [productCoeff]
  | cons a w ih =>
      change 0 * g (a :: w) + productCoeff 0 g w = 0
      rw [zero_mul, zero_add, ih]

lemma productCoeff_zero_right (f : List (Fin 2) → A) (w) :
    productCoeff f (0 : List (Fin 2) → A) w = 0 := by
  induction w generalizing f with
  | nil => simp [productCoeff]
  | cons a w ih => simp [productCoeff, ih]

lemma productCoeff_add_left (f g h : List (Fin 2) → A) (w) :
    productCoeff (f + g) h w = productCoeff f h w + productCoeff g h w := by
  induction w generalizing f g with
  | nil => simp [productCoeff, add_mul]
  | cons a w ih =>
      simp only [productCoeff, Pi.add_apply, add_mul]
      rw [show (fun v => f (a :: v) + g (a :: v)) =
        (fun v => f (a :: v)) + (fun v => g (a :: v)) from rfl, ih]
      abel

lemma productCoeff_add_right (f g h : List (Fin 2) → A) (w) :
    productCoeff f (g + h) w = productCoeff f g w + productCoeff f h w := by
  induction w generalizing f with
  | nil => simp [productCoeff, mul_add]
  | cons a w ih =>
      simp only [productCoeff, Pi.add_apply, mul_add, ih]
      abel

lemma productCoeff_mul_left (c : A) (f g : List (Fin 2) → A) (w) :
    productCoeff (fun v => c * f v) g w = c * productCoeff f g w := by
  induction w generalizing f with
  | nil => simp [productCoeff, mul_assoc]
  | cons a w ih => simp [productCoeff, ih, mul_assoc, mul_add]

lemma productCoeff_assoc (f g h : List (Fin 2) → A) (w) :
    productCoeff (productCoeff f g) h w = productCoeff f (productCoeff g h) w := by
  induction w generalizing f with
  | nil => simp [productCoeff, mul_assoc]
  | cons a w ih =>
      simp only [productCoeff]
      rw [show (fun v => f [] * g (a :: v) +
        productCoeff (fun v => f (a :: v)) g v) =
        (fun v => f [] * g (a :: v)) + productCoeff (fun v => f (a :: v)) g from rfl]
      rw [productCoeff_add_left, productCoeff_mul_left, ih]
      simp [mul_add, mul_assoc, add_assoc]

def const (a : A) : FreeSeries A := ⟨fun w => if w = [] then a else 0⟩

instance : One (FreeSeries A) := ⟨const 1⟩

instance : NatCast (FreeSeries A) := ⟨fun n => const n⟩

instance : IntCast (FreeSeries A) := ⟨fun n => const n⟩

@[simp] lemma coeff_const_nil (a : A) : (const a).coeff [] = a := by simp [const]

@[simp] lemma coeff_const_cons (a : A) (i w) : (const a).coeff (i :: w) = 0 := by
  simp [const]

lemma productCoeff_const_left (c : A) (f : List (Fin 2) → A) (w) :
    productCoeff (const c).coeff f w = c * f w := by
  cases w with
  | nil => simp [productCoeff]
  | cons a w =>
      simp only [productCoeff, coeff_const_nil, coeff_const_cons]
      rw [show (fun _ : List (Fin 2) => (0 : A)) = 0 from rfl,
        productCoeff_zero_left, add_zero]

lemma productCoeff_const_right (c : A) (f : List (Fin 2) → A) (w) :
    productCoeff f (const c).coeff w = f w * c := by
  induction w generalizing f with
  | nil => simp [productCoeff]
  | cons a w ih => simp [productCoeff, ih]

instance : Ring (FreeSeries A) where
  natCast n := const n
  intCast n := const n
  mul_assoc f g h := FreeSeries.ext (funext (productCoeff_assoc f.coeff g.coeff h.coeff))
  one_mul f := by ext w; exact (productCoeff_const_left 1 f.coeff w).trans (one_mul _)
  mul_one f := by ext w; exact (productCoeff_const_right 1 f.coeff w).trans (mul_one _)
  left_distrib f g h := FreeSeries.ext (funext (productCoeff_add_right f.coeff g.coeff h.coeff))
  right_distrib f g h := FreeSeries.ext (funext (productCoeff_add_left f.coeff g.coeff h.coeff))
  zero_mul f := FreeSeries.ext (funext (productCoeff_zero_left f.coeff))
  mul_zero f := FreeSeries.ext (funext (productCoeff_zero_right f.coeff))
  natCast_zero := by ext w; simp [const]
  natCast_succ n := by
    ext w
    change (if w = [] then ((n + 1 : ℕ) : A) else 0) =
      (if w = [] then (n : A) else 0) + (if w = [] then (1 : A) else 0)
    split_ifs <;> simp
  intCast_ofNat n := by
    change const ((n : ℤ) : A) = const (n : A)
    rw [Int.cast_natCast]
  intCast_negSucc n := by
    ext w
    change (if w = [] then ((Int.negSucc n : ℤ) : A) else 0) =
      -(if w = [] then ((n + 1 : ℕ) : A) else 0)
    split_ifs <;> simp

end Ring

end FreeSeries

end KuroshConstruction

end OAI
