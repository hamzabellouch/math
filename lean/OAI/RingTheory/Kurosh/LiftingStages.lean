import Mathlib
import OAI.RingTheory.Kurosh.Lifting
import OAI.RingTheory.Kurosh.ScalarChange

namespace OAI

/-! Compatible finite stages and the consequences of an algebraic lift. -/

namespace KuroshConstruction

section EvalIdentities

variable {K L A : Type*} [Field K] [Field L] [Ring A] [Algebra L A]
  (φ : K →+* L) {I : Type*}

lemma scalarChange_free_evaluate (X : I → A) (p : FreeAlgebra K I) :
    letI : Algebra K A := Algebra.compHom A φ
    FreeAlgebra.lift K X p = FreeAlgebra.lift L X (freeScalarChange φ p) := by
  let := Algebra.compHom A φ
  induction p using FreeAlgebra.induction with
  | grade0 c => simp only [AlgHom.commutes, freeScalarChange_algebraMap]; rfl
  | grade1 i => simp
  | mul p q hp hq => simp only [map_mul, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

lemma scalarChange_series_evaluate (X : I → FreeSeries A) (p : FreeAlgebra K I) :
    letI : Algebra K A := Algebra.compHom A φ
    FreeAlgebra.lift K X p = FreeAlgebra.lift L X (freeScalarChange φ p) := by
  let := Algebra.compHom A φ
  induction p using FreeAlgebra.induction with
  | grade0 c => simp only [AlgHom.commutes, freeScalarChange_algebraMap]; rfl
  | grade1 i => simp
  | mul p q hp hq => simp only [map_mul, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

end EvalIdentities

noncomputable def freeRename {K I J : Type*} [CommSemiring K] (g : I → J) :
    FreeAlgebra K I →ₐ[K] FreeAlgebra K J := FreeAlgebra.lift K (FreeAlgebra.ι K ∘ g)

lemma freeRename_evaluate {K I J B : Type*} [CommSemiring K] [Semiring B] [Algebra K B]
    (g : I → J) (Y : J → B) (p : FreeAlgebra K I) :
    FreeAlgebra.lift K Y (freeRename g p) = FreeAlgebra.lift K (Y ∘ g) p := by
  induction p using FreeAlgebra.induction with
  | grade0 c => simp only [AlgHom.commutes]
  | grade1 i => simp [freeRename]
  | mul p q hp hq => simp only [map_mul, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

structure LiftingStage where
  K : Type
  A : Type
  [fieldK : Field K]
  [divisionA : DivisionRing A]
  [algebraKA : Algebra K A]
  [countableK : Countable K]
  [charZeroK : CharZero K]
  [centralA : Algebra.IsCentral K A]
  [finiteA : Module.Finite K A]
  roots : ∀ n : ℕ, 0 < n → ∃ ζ : K, IsPrimitiveRoot ζ n
  X : Fin 2 → FreeSeries A
  input : LiftingInput K X

attribute [instance] LiftingStage.fieldK LiftingStage.divisionA LiftingStage.algebraKA
  LiftingStage.countableK LiftingStage.charZeroK LiftingStage.centralA LiftingStage.finiteA

structure LiftingStep (S T : LiftingStage) (p : FreeAlgebra S.K (Fin 2)) where
  scalar : S.K →+* T.K
  grow : Nat.sqrt (Module.finrank S.K S.A) < Nat.sqrt (Module.finrank T.K T.A)
  identities : ∀ r : FreeAlgebra S.K (Fin 2),
    FreeAlgebra.lift S.K S.X r = 0 →
    FreeAlgebra.lift T.K T.X (freeScalarChange scalar r) = 0
  integral : IsIntegral T.K (FreeAlgebra.lift T.K T.X (freeScalarChange scalar p))

theorem lifting_step_exists (hL : LiftingStatement) (S : LiftingStage)
    (p : FreeAlgebra S.K (Fin 2)) : ∃ T : LiftingStage, Nonempty (LiftingStep S T p) := by
  obtain ⟨K', A', iK, iA, iKK, iKA, hcount, hcentral, hfinite, hgrow, X', w', hid, hin, hw⟩ :=
    hL S.K S.A S.fieldK S.divisionA S.algebraKA S.countableK S.charZeroK S.roots
      S.centralA S.finiteA 2 S.X S.input (FreeAlgebra.lift S.K S.X p)
  let φ := algebraMap S.K K'
  let : CharZero K' := charZero_of_injective_ringHom φ.injective
  let : Countable K' := hcount
  let : Algebra.IsCentral K' A' := hcentral
  let : Module.Finite K' A' := hfinite
  have hroots : ∀ n : ℕ, 0 < n → ∃ ζ : K', IsPrimitiveRoot ζ n := by
    intro n hn
    obtain ⟨ζ, hζ⟩ := S.roots n hn
    exact ⟨φ ζ, hζ.map_of_injective φ.injective⟩
  let T : LiftingStage := ⟨K', A', hroots, X', hin⟩
  refine ⟨T, ⟨⟨φ, hgrow, ?_, ?_⟩⟩⟩
  · intro r hr
    have h := hid (freeRename Option.some r) (by
      simpa [satisfiesIdentity, freeRename_evaluate, Function.comp_def, augmentedTuple] using hr)
    change FreeAlgebra.lift K' X' (freeScalarChange φ r) = 0
    rw [← scalarChange_series_evaluate]
    simpa [satisfiesIdentity, freeRename_evaluate, Function.comp_def, augmentedTuple] using h
  · have h := hid (FreeAlgebra.ι S.K none - freeRename Option.some p) (by
      simp [satisfiesIdentity, freeRename_evaluate, Function.comp_def, augmentedTuple])
    let : Algebra S.K A' := Algebra.compHom A' φ
    have he₀ : w' = FreeAlgebra.lift S.K X' p := by
      simpa [satisfiesIdentity, freeRename_evaluate, Function.comp_def, augmentedTuple,
        sub_eq_zero] using h
    have he : w' = FreeAlgebra.lift K' X' (freeScalarChange φ p) := by
      rw [scalarChange_series_evaluate] at he₀
      exact he₀
    change IsIntegral K' (FreeAlgebra.lift K' X' (freeScalarChange φ p))
    exact he ▸ hw

end KuroshConstruction

end OAI
