import Mathlib
import OAI.RingTheory.Kurosh.ScheduledTowers
import OAI.RingTheory.Kurosh.Ultraproduct

namespace OAI

/-! Compatible tail-field maps and the limiting scalar field. -/

namespace KuroshConstruction

open Filter

section TailFields

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
  (K A : ℕ → Type*) [∀ i, Field (K i)] [∀ i, DivisionRing (A i)]
  [∀ i, Algebra (K i) (A i)]
  (f : ∀ i j, i ≤ j → K i →+* K j)
  [DirectedSystem K (fun i j h => f i j h)]

noncomputable def tailCoefficients (j : ℕ) (c : K j) : ∀ i, A i :=
  fun i => if h : j ≤ i then algebraMap (K i) (A i) (f j i h c) else 0

noncomputable def ultraStageMap (j : ℕ) : K j →+* DivisionUltraproduct U A where
  toFun c := ultraMap U A (tailCoefficients K A f j c)
  map_one' := by
    rw [← map_one (ultraMap U A)]
    apply (ultraMap_eq_iff U A _ _).mpr
    exact ((eventually_ge_atTop j).filter_mono hU).mono (fun i hi => by
      simp [tailCoefficients, hi])
  map_mul' x y := by
    rw [← map_mul]
    apply (ultraMap_eq_iff U A _ _).mpr
    exact ((eventually_ge_atTop j).filter_mono hU).mono (fun i hi => by
      simp [tailCoefficients, hi])
  map_zero' := by
    rw [← map_zero (ultraMap U A)]
    apply (ultraMap_eq_iff U A _ _).mpr
    exact Eventually.of_forall (fun i => by simp [tailCoefficients])
  map_add' x y := by
    rw [← map_add]
    apply (ultraMap_eq_iff U A _ _).mpr
    exact ((eventually_ge_atTop j).filter_mono hU).mono (fun i hi => by
      simp [tailCoefficients, hi])

lemma ultraStageMap_compatible (i j : ℕ) (hij : i ≤ j) (x : K i) :
    ultraStageMap U hU K A f j (f i j hij x) = ultraStageMap U hU K A f i x := by
  apply (ultraMap_eq_iff U A _ _).mpr
  exact ((eventually_ge_atTop j).filter_mono hU).mono (fun k hjk => by
    simp only [tailCoefficients, dite_eq_left hjk, dite_eq_left (hij.trans hjk)]
    rw [DirectedSystem.map_map (f := fun {i j} h => f i j h)])

noncomputable def ultraLimitMap : DirectLimit K f →+* DivisionUltraproduct U A :=
  DirectLimit.Ring.lift K f _ (ultraStageMap U hU K A f)
    (ultraStageMap_compatible U hU K A f)

omit [DirectedSystem K (fun i j h => f i j h)] in
lemma ultraStageMap_commutes (j : ℕ) (x : K j) (a : DivisionUltraproduct U A) :
    Commute (ultraStageMap U hU K A f j x) a := by
  obtain ⟨z, rfl⟩ := (ultraCongruence U A).mk'_surjective a
  change ultraMap U A (tailCoefficients K A f j x) * ultraMap U A z =
    ultraMap U A z * ultraMap U A (tailCoefficients K A f j x)
  rw [← map_mul, ← map_mul]
  apply (ultraMap_eq_iff U A _ _).mpr
  exact ((eventually_ge_atTop j).filter_mono hU).mono (fun i hi => by
    simp only [Pi.mul_apply, tailCoefficients, dite_eq_left hi]
    exact Algebra.commutes _ _)

lemma ultraLimitMap_commutes (x : DirectLimit K f) (a : DivisionUltraproduct U A) :
    Commute (ultraLimitMap U hU K A f x) a := by
  induction x using DirectLimit.induction with | _ i x
  exact ultraStageMap_commutes U hU K A f i x a

@[instance_reducible] noncomputable def ultraLimitAlgebra : Algebra (DirectLimit K f) (DivisionUltraproduct U A) :=
  (ultraLimitMap U hU K A f).toAlgebra' (ultraLimitMap_commutes U hU K A f)

end TailFields

end KuroshConstruction

end OAI
