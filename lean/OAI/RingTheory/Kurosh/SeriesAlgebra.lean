import Mathlib
import OAI.RingTheory.Kurosh.FreeSeries

namespace OAI

/-! Constant coefficients, scalar maps, and linear coefficients of formal series. -/

namespace KuroshConstruction.FreeSeries

variable {A B K : Type*} [Ring A]

@[simp] lemma coeff_one (w : List (Fin 2)) :
    (1 : FreeSeries A).coeff w = if w = [] then 1 else 0 := rfl

@[simp] lemma coeff_const (a : A) (w : List (Fin 2)) :
    (const a).coeff w = if w = [] then a else 0 := rfl

@[simp] lemma const_mul_coeff (a : A) (f : FreeSeries A) (w) :
    (const a * f).coeff w = a * f.coeff w := productCoeff_const_left _ _ _

@[simp] lemma mul_const_coeff (f : FreeSeries A) (a : A) (w) :
    (f * const a).coeff w = f.coeff w * a := productCoeff_const_right _ _ _

def constHom : A →+* FreeSeries A where
  toFun := const
  map_zero' := by ext w; simp
  map_one' := rfl
  map_add' a b := by ext w; simp; split_ifs <;> simp
  map_mul' a b := by ext w; simp

def constantCoeff : FreeSeries A →+* A where
  toFun f := f.coeff []
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] lemma constantCoeff_const (a : A) : constantCoeff (const a) = a := rfl

instance [CommRing K] [Algebra K A] : Algebra K (FreeSeries A) :=
  ((constHom (A := A)).comp (algebraMap K A)).toAlgebra' fun k f => by
    ext w
    exact (const_mul_coeff _ _ _).trans ((Algebra.commutes k (f.coeff w)).trans
      (mul_const_coeff _ _ _).symm)

@[simp] lemma coeff_algebraMap [CommRing K] [Algebra K A] (k : K) (w) :
    (algebraMap K (FreeSeries A) k).coeff w = if w = [] then algebraMap K A k else 0 := rfl

@[simp] lemma coeff_smul [CommRing K] [Algebra K A] (k : K) (f : FreeSeries A) (w) :
    (k • f).coeff w = k • f.coeff w := by
  change (const (algebraMap K A k) * f).coeff w = k • f.coeff w
  rw [const_mul_coeff, Algebra.smul_def]

def constantCoeffAlgHom [CommRing K] [Algebra K A] : FreeSeries A →ₐ[K] A :=
  { constantCoeff with commutes' := fun _ => rfl }

def constAlgHom [CommRing K] [Algebra K A] : A →ₐ[K] FreeSeries A :=
  { constHom with commutes' := fun _ => rfl }

def map [Ring B] (φ : A →+* B) : FreeSeries A →+* FreeSeries B where
  toFun f := ⟨φ ∘ f.coeff⟩
  map_zero' := by ext w; exact φ.map_zero
  map_one' := by ext w; simp only [Function.comp_apply, coeff_one]; split_ifs <;> simp
  map_add' f g := by ext w; exact φ.map_add _ _
  map_mul' f g := by
    ext w
    change φ (productCoeff f.coeff g.coeff w) = productCoeff (φ ∘ f.coeff) (φ ∘ g.coeff) w
    generalize f.coeff = ff
    generalize g.coeff = gg
    induction w generalizing ff with
    | nil => exact φ.map_mul _ _
    | cons a w ih =>
      simp only [productCoeff, Function.comp_apply, map_add, map_mul]
      rw [ih]
      rfl

def letterCoeff (i : Fin 2) (f : FreeSeries A) : A := f.coeff [i]

def letter (i : Fin 2) : FreeSeries A := ⟨fun w => if w = [i] then 1 else 0⟩

@[simp] lemma coeff_letter (i : Fin 2) (w) :
    (letter i : FreeSeries A).coeff w = if w = [i] then 1 else 0 := rfl

@[simp] lemma constantCoeff_letter (i : Fin 2) :
    constantCoeff (letter i : FreeSeries A) = 0 := rfl

@[simp] lemma letterCoeff_letter (i j : Fin 2) :
    letterCoeff i (letter j : FreeSeries A) = if i = j then 1 else 0 := by
  simp [letterCoeff]

lemma letter_commutes_const (i : Fin 2) (a : A) :
    letter i * const a = const a * letter i := by
  ext w
  simp only [mul_const_coeff, const_mul_coeff, coeff_letter]
  split_ifs <;> simp

lemma letterCoeff_mul (i : Fin 2) (f g : FreeSeries A) :
    letterCoeff i (f * g) =
      constantCoeff f * letterCoeff i g + letterCoeff i f * constantCoeff g := rfl

end KuroshConstruction.FreeSeries

end OAI
