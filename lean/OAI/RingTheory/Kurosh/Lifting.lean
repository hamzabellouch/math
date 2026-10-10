import Mathlib
import OAI.RingTheory.Kurosh.SeriesAlgebra

namespace OAI

/-! Tangent directions, formal identities, and the algebraic lifting proposition. -/

namespace KuroshConstruction

section LiftingInterfaces

variable (K : Type*) {A : Type*} [Field K] [Ring A] [Algebra K A] {u : ℕ}

def innerDirection (C : Fin u → A) : A →ₗ[K] (Fin u → A) where
  toFun T i := T * C i - C i * T
  map_add' T U := by ext i; simp [add_mul, mul_add]; abel
  map_smul' r T := by ext i; simp [smul_sub]

def innerTangent (C : Fin u → A) : Submodule K (Fin u → A) :=
  (innerDirection K C).range

def constantTuple (X : Fin u → FreeSeries A) : Fin u → A :=
  fun i => (X i).coeff []

def letterTuple (X : Fin u → FreeSeries A) (j : Fin 2) : Fin u → A :=
  fun i => (X i).coeff [j]

def LiftingInput (X : Fin u → FreeSeries A) : Prop :=
  Algebra.adjoin K (Set.range (constantTuple X)) = ⊤ ∧
  LinearIndependent K (fun j : Fin 2 =>
    (innerTangent K (constantTuple X)).mkQ (letterTuple X j))

def augmentedTuple (X : Fin u → FreeSeries A) (w : FreeSeries A) :
    Option (Fin u) → FreeSeries A
  | none => w
  | some i => X i

def satisfiesIdentity (X : Fin u → FreeSeries A) (w : FreeSeries A)
    (p : FreeAlgebra K (Option (Fin u))) : Prop :=
  FreeAlgebra.lift K (augmentedTuple X w) p = 0

end LiftingInterfaces

def LiftingStatement : Prop :=
  ∀ (K A : Type) (_ : Field K) (_ : DivisionRing A) (_ : Algebra K A),
    Countable K → CharZero K →
    (∀ n : ℕ, 0 < n → ∃ ζ : K, IsPrimitiveRoot ζ n) →
    Algebra.IsCentral K A → Module.Finite K A →
    ∀ (u : ℕ) (X : Fin u → FreeSeries A), LiftingInput K X →
    ∀ w : FreeSeries A,
    ∃ (K' A' : Type) (_ : Field K') (_ : DivisionRing A')
      (_ : Algebra K K') (_ : Algebra K' A'),
      letI : Algebra K A' := Algebra.compHom A' (algebraMap K K')
      Countable K' ∧ Algebra.IsCentral K' A' ∧ Module.Finite K' A' ∧
      Nat.sqrt (Module.finrank K A) < Nat.sqrt (Module.finrank K' A') ∧
      ∃ (X' : Fin u → FreeSeries A') (w' : FreeSeries A'),
        (∀ p : FreeAlgebra K (Option (Fin u)),
          satisfiesIdentity K X w p → satisfiesIdentity K X' w' p) ∧
        LiftingInput K' X' ∧ IsIntegral K' w'

end KuroshConstruction

end OAI
